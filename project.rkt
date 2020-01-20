#lang racket
(require (lib "eopl.ss" "eopl"))


;;; Utils ;;;
(define (list-of? check)
  (lambda (lst)
    (if (null? lst)
        #t
        (and (check (car lst))
             ((list-of? check) (cdr lst))))))

(define (contains? pred)
  (lambda (check-list obj)
    (ormap (lambda (other)
             (pred other obj))
           check-list)))

(define (remove-all from-list obj pred)
  (if (null? from-list)
      '()
      (if (pred obj (car from-list))
          (remove-all (cdr from-list) obj pred)
          (cons (car from-list) (remove-all (cdr from-list) obj pred)))))

(define (intersect list1 list2 pred)
  (if (null? list1)
      '()
      (if ((contains? pred) list2 (car list1))
          (cons (car list1) (intersect (remove-all (cdr list1) (car list1) pred) list2 pred))
          (intersect (remove-all (cdr list1) (car list1) pred) list2 pred))))

(define (union list1 list2 pred)
  (if (null? list1)
      list2
      (if ((contains? pred) list2 (car list1))
          (cons (car list1) (union (remove-all (cdr list1) (car list1) pred) (remove-all list2 (car list1) pred) pred))
          (cons (car list1) (union (remove-all (cdr list1) (car list1) pred) list2 pred)))))

(define (normalize-string str)
  (string-split str #px"[\\s\\,\\.\\(\\)\\\"\\?\\!\\:\\;]+"))

(define (path-list-concat path-list base-dir)
  (if (null? path-list)
      '()
      (cons (build-path base-dir (car path-list)) (path-list-concat (cdr path-list) base-dir))))

(define (enqueue queue obj)
  (append queue (list obj)))

(define (find-value key-val-list search-key)
  (if (null? key-val-list)
      '()
      (if (string=? (to-str (car (car key-val-list))) search-key)
          (cadr (car key-val-list))
          (find-value (cdr key-val-list) search-key))))

(define (find-all-values key-val-list search-key)
  (if (null? key-val-list)
      '()
      (if (string=? (to-str (car (car key-val-list))) search-key)
          (cons (cadr (car key-val-list)) (find-all-values (cdr key-val-list) search-key))
          (find-all-values (cdr key-val-list) search-key))))

(define (to-str str-str)
  (read (open-input-string str-str)))

(define (first-index word str)
  (if (eq? (string-length word) 0)
      #f
      (if (string-prefix? word str)
          0
          (add1 (first-index (substring word 1) str)))))

;;; Datatype Methods ;;;

(define (method-check mtd)
  (cond
    [(string=? mtd "and") #t]
    [(string=? mtd "or") #t]
    [else (error "Invalid method for query")]))

(define (q-sym? sym)
  (cond
    [(eq? sym '+) #t]
    [(eq? sym '*) #t]
    [(eq? sym '-) #t]
    [else (error "Invalid symbol for func body")]))

(define-datatype q-sym-type q-sym-type?
  (q-sym-type1 (q-sym q-sym?)
               (precedence integer?)))

(define-datatype query-command query-command?
  (qc-directory (address string?))
  (qc-query (words (list-of? string?)))
  (qc-size (file-count integer?))
  (qc-method (type method-check)))

(define-datatype q-func-body-tree q-func-body-tree?
  (q-func-tree-sym-node (node-sym q-sym-type?)
                        (left-child q-func-body-tree?)
                        (right-child q-func-body-tree?))
  (q-func-empty-node)
  (q-func-leaf-node (node-str string?)))

(define-datatype q-func-arg q-func-arg?
  (q-func-arg1 (arg-name string?)
               (arg-value string?)))

(define-datatype q-exp q-exp?
  (q-comm (comm-list (list-of? query-command?)))
  (q-func (func-name string?)
          (func-body q-func-body-tree?)
          (func-arg-list (list-of? q-func-arg?))))

;;; Environments ;;;

(define (extend-q-env env new-entry)
  (q-env new-entry env))

(define (find-func-in-env env func-name)
  (cases q-env-type env
    (empty-q-env () '())
    (q-env (cur-exp rest-env)
           (cases q-exp cur-exp
             (q-comm (comm-list) (find-func-in-env rest-env func-name))
             (q-func (f-name f-body f-arg-list)
                     (if (string=? func-name f-name)
                         cur-exp
                         (find-func-in-env rest-env func-name)))))))

(define (find-first-query-in-env env)
  (cases q-env-type env
    (empty-q-env () (error "No Query in commands"))
    (q-env (cur-exp rest-env)
           (cases q-exp cur-exp
             (q-comm (comm-list) cur-exp)
             (q-func (f-name f-body f-arg-list) (find-first-query-in-env rest-env))))))

(define-datatype q-env-type q-env?
  (q-env (current-exp q-exp?)
         (rest-env q-env?))
  (empty-q-env))

(define (create-fb-env f-arg-list arg-values curr-env)
  (if (eq? (length f-arg-list) (length arg-values))
      (if (null? f-arg-list)
          curr-env
          (cases q-func-arg (car f-arg-list)
            (q-func-arg1 (name val)
                         (create-fb-env (cdr f-arg-list) (cdr arg-values) (fb-env (q-func-arg1 name (car arg-values)) curr-env)))))
      (error "Parameter counts do not match")))

(define (search-fb-env curr-fb-env arg-name)
  (cases fb-env-type curr-fb-env
    (empty-fb-env () arg-name)
    (fb-env (curr-arg rest-env)
            (cases q-func-arg curr-arg
              (q-func-arg1 (name value)
                           (if (string=? name arg-name)
                               value
                               (search-fb-env rest-env arg-name)))))))

(define-datatype fb-env-type fb-env?
  (fb-env (current-arg q-func-arg?)
          (rest-env fb-env?))
  (empty-fb-env))

;;; Parsing Methods ;;;

(define (get-q-sym-pred sym)
  (cond
    [(eq? sym '+) 1]
    [(eq? sym '*) 2]
    [(eq? sym '-) 3]
    [else (error "Invalid symbol for func body")]))

(define (move-operators-to-queue op-sym out-queue op-stack)
  (let ([op-pred (get-q-sym-pred op-sym)])
    (if (null? op-stack)
        (list out-queue (cons (q-sym-type1 op-sym op-pred) op-stack))
        (cases q-sym-type (car op-stack)
          (q-sym-type1 (sym pred)
                       (if (> op-pred pred)
                           (list out-queue (cons (q-sym-type1 op-sym op-pred) op-stack))
                           (move-operators-to-queue op-sym (enqueue out-queue (car op-stack)) (cdr op-stack))))))))

(define (shunting-yard token-list out-queue operator-stack)
  (if (null? token-list)
      (if (null? operator-stack)
          out-queue
          (shunting-yard token-list (enqueue out-queue (car operator-stack)) (cdr operator-stack)))
      (let ([next-token (car token-list)])
        (cond
          [(string? next-token) (shunting-yard (cdr token-list) (enqueue out-queue (car token-list)) operator-stack)]
          [(q-sym? next-token) 
          (let ([changed-pair (move-operators-to-queue next-token out-queue operator-stack)])
            (let ([out-q (car changed-pair)]
                  [op-stk (cadr changed-pair)])
              (shunting-yard (cdr token-list) out-q op-stk)))]
          [else (error "Invalid symbol in func body")]))))

(define (post-order->func-tree post-order-list left-stack)
  (if (null? post-order-list)
      (car left-stack)
      (let ([curr (car post-order-list)])
        (if (string? curr)
            (post-order->func-tree (cdr post-order-list) (cons (q-func-leaf-node curr) left-stack))
            (let ([right-child (car left-stack)]
                  [left-child (cadr left-stack)])
              (post-order->func-tree (cdr post-order-list) (cons (q-func-tree-sym-node curr left-child right-child) (cdr (cdr left-stack)))))))))

(define (parse-func-body body-str)
  (let ([body-list (read (open-input-string body-str))])
    (let ([post-order-list (shunting-yard body-list '() '())])
      (post-order->func-tree post-order-list '()))))

(define (parse-func-arg-list arg-names)
  (if (null? arg-names)
      '()
      (cons (q-func-arg1 (to-str (car arg-names)) "") (parse-func-arg-list (cdr arg-names)))))

(define (parse-command comm-split)
  (let ([key (read (open-input-string (car comm-split)))]
        [value (read (open-input-string (cadr comm-split)))])
    (cond
      [(string=? key "directory") (qc-directory value)]
      [(string=? key "query") (qc-query (string-split value #px"\\s+"))]
      [(string=? key "size") (qc-size value)]
      [(string=? key "method") (qc-method value)]
      [else (error "Invalid Command")])))

(define (extract-command-list comm-list)
  (if (null? comm-list)
      '()
      (cons (parse-command (string-split (car comm-list) #px"\\s+\\:\\s+"))
            (extract-command-list (cdr comm-list)))))

(define (is-comm-func? split-key-values-list)
  (if (null? split-key-values-list)
      #f
      (if (string=? (read (open-input-string (car (car split-key-values-list)))) "func")
          #t
          (is-comm-func? (cdr split-key-values-list)))))

(define (pair-list->key-val-list pair-list)
  (if (null? pair-list)
      '()
      (cons (string-split (car pair-list) #px"\\s+\\:\\s+") (pair-list->key-val-list (cdr pair-list)))))

(define (parse-q-env line-list current-env)
  (if (null? line-list)
      current-env
      (let ([pair-str-list (string-split (substring (car line-list) 2 (- (string-length (car line-list)) 2)) #px"\\s+\\,\\s+")])
        (let ([key-val-list (pair-list->key-val-list pair-str-list)])
          (if (is-comm-func? key-val-list)
              (parse-q-env (cdr line-list) (extend-q-env current-env (q-func (to-str (find-value key-val-list "func"))
                                                                             (parse-func-body (find-value key-val-list "body"))
                                                                             (parse-func-arg-list (find-all-values key-val-list "input")))))
              (parse-q-env (cdr line-list) (extend-q-env current-env (q-comm (extract-command-list pair-str-list)))))))))
            

;;; File Reading and Search Methods ;;;

(define (find-all-files base-dir)
  (path-list-concat (directory-list base-dir) base-dir))

(define (is-func-call? word)
  (and (string-contains? word "(")
       (string-suffix? word ")")))

(define (extract-func-parts func-word)
  (let ([lparam-pos (first-index func-word "(")])
    (let ([fname (substring func-word 0 lparam-pos)]
          [params-list (string-split (substring func-word (add1 lparam-pos) (sub1 (string-length func-word))) #px"\\,")])
      (cons fname params-list))))

(define (read-and-normalize-files dir)
  (map (lambda (file-dir)
         (list file-dir (normalize-string (file->string file-dir))))
       (find-all-files dir)))

(define (search-word files-list word)
  (if (null? files-list)
      '()
      (let ([current-file-dir (car (car files-list))]
            [current-file-words (cadr (car files-list))])
        (if ((contains? string=?) current-file-words word)
            (cons current-file-dir (search-word (cdr files-list) word))
            (search-word (cdr files-list) word)))))

(define (give-files-containing files-list word curr-q-env)
  (if (is-func-call? word)
      (let ([func-parts (extract-func-parts word)])
        (let ([func-obj (find-func-in-env curr-q-env (car func-parts))])
          (if (null? func-obj)
              (search-word files-list word)
              (exec-q-func func-obj (cdr func-parts) files-list curr-q-env))))
      (search-word files-list word)))

(define (handle-search files-list word-list method curr-q-env)
  (if (or (null? (cdr word-list)) (null? method))
      (give-files-containing files-list (car word-list) curr-q-env)
      (if (string=? method "and")
          (intersect (give-files-containing files-list (car word-list) curr-q-env) (handle-search files-list (cdr word-list) method curr-q-env) equal?)
          (union (give-files-containing files-list (car word-list) curr-q-env) (handle-search files-list (cdr word-list) method curr-q-env) equal?))))

;;; Execution Methods ;;;

(define (exec-q-func func-obj args-list files-list curr-q-env)
  (cases q-exp func-obj
    (q-func (f-name f-body f-args)
            (let ([curr-fb-env (create-fb-env f-args args-list (empty-fb-env))])
              (exec-func-body f-body files-list curr-fb-env curr-q-env)))
    (q-comm (comm-list)
            (error "What a Terrible Failure!"))))

(define (exec-func-body f-tree files-list curr-fb-env curr-q-env)
  (cases q-func-body-tree f-tree
    (q-func-empty-node () (error "Empty Node in function tree"))
    (q-func-leaf-node (word)
                      (if (is-func-call? word)
                          (let ([func-parts (extract-func-parts word)])
                            (let ([func-obj (find-func-in-env curr-q-env (car func-parts))])
                              (if (null? func-obj)
                                  (search-word files-list (search-fb-env curr-fb-env word))
                                  (exec-q-func func-obj (cdr func-parts) curr-q-env))))
                          (search-word files-list (search-fb-env curr-fb-env word))))
    (q-func-tree-sym-node (sym left-child right-child)
                          (cases q-sym-type sym
                            (q-sym-type1 (sym-obj prec)
                                         (cond
                                           [(eq? sym-obj '-) (search-word files-list (string-replace
                                                                                      (simple-tree-exec left-child curr-fb-env)
                                                                                      (simple-tree-exec right-child curr-fb-env)
                                                                                      ""))]
                                           [(eq? sym-obj '*) (intersect (exec-func-body left-child files-list curr-fb-env curr-q-env)
                                                                        (exec-func-body right-child files-list curr-fb-env curr-q-env)
                                                                         equal?)]
                                           [(eq? sym-obj '+) (union (exec-func-body left-child files-list curr-fb-env curr-q-env)
                                                                    (exec-func-body right-child files-list curr-fb-env curr-q-env)
                                                                     equal?)]
                                           [else (error "Another What a Terrible Failure!")]))))))

(define (simple-tree-exec t-body curr-fb-env)
  (cases q-func-body-tree t-body
    (q-func-empty-node () (error "Empty Node in function tree"))
    (q-func-leaf-node (word) (search-fb-env curr-fb-env word))
    (q-func-tree-sym-node (sym left-child right-child)
                          (cases q-sym-type sym
                            (q-sym-type1 (sym-obj prec)
                                         (cond
                                           [(eq? sym-obj '-) (string-replace
                                                              (simple-tree-exec left-child curr-fb-env)
                                                              (simple-tree-exec right-child curr-fb-env)
                                                              "")]
                                           [else (error "Lower Precedence under \"-\" in tree")]))))))
                                                             
(define (find-and-execute-query curr-q-env)
  (let ([query-command (find-first-query-in-env curr-q-env)])
    (cases q-exp query-command
      (q-comm (comm-list)
              (sort-commands-and-execute comm-list '() '() '() '() curr-q-env))
      (else (error "Well its not possible")))))
  

(define (execute-command c-dir c-qry c-sze c-mtd curr-q-env)
  (let ([files-list (read-and-normalize-files c-dir)])
    (let ([final-list (handle-search files-list c-qry c-mtd curr-q-env)])
      (if (<= c-sze 0)
          final-list
          (if (< c-sze (length final-list))
              (list-tail final-list (- (length final-list) c-sze))
              final-list)))))
    

(define (sort-commands-and-execute comm-list c-dir c-qry c-sze c-mtd curr-q-env)
  (if (null? comm-list)
      (if (or (null? c-dir) (null? c-qry))
          (error "Missing \"directory\" or \"query\" in command")
          (execute-command c-dir c-qry c-sze c-mtd curr-q-env))
      (cases query-command (car comm-list)
        (qc-directory (dir) (sort-commands-and-execute (cdr comm-list) dir c-qry c-sze c-mtd curr-q-env))
        (qc-query (qry) (sort-commands-and-execute (cdr comm-list) c-dir qry c-sze c-mtd curr-q-env))
        (qc-size (sze) (sort-commands-and-execute (cdr comm-list) c-dir c-qry sze c-mtd curr-q-env))
        (qc-method (mtd) (sort-commands-and-execute (cdr comm-list) c-dir c-qry c-sze mtd curr-q-env)))))
          
(define (run input-address)
  (let ([curr-q-env (parse-q-env (file->lines input-address) (empty-q-env))])
    (find-and-execute-query curr-q-env)))
         