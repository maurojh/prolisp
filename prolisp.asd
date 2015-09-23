(defsystem prolisp
    :author "Mauro Jacob Honorato <maurojh@gmail.com> and Junia Magalhães Rocha <junnia@gmail.com>"
  :maintainer "Mauro Jacob Honorato <maurojh@gmail.com> and Junia Magalhães Rocha <junnia@gmail.com>"
  :license "MIT"
  :version "0.1"
  :homepage ""
  :bug-tracker ""
  :source-control (:git "")
  :components ((:serial t
                :components
                ((:file "prolisp"))))
  :description "A Prolog implementation written in Lisp."
  :long-description
  #.(uiop:read-file-string
     (uiop:subpathname *load-pathname* "README.md"))
  :in-order-to ((test-op (test-op prolist-test))))
