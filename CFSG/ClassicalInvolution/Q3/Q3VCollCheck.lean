module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.ClassicalInvolution.Q3.Q3ZWords

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.Q3Z

@[expose] def collSet : Fin 24 → List ℕ :=
  ![[], [], [], [], [7, 10], [0, 2, 8], [6, 9], [0, 2, 8], [1, 3, 11], [1, 2, 10], [7, 10],
    [1, 2, 9], [0, 3, 9], [0, 3, 9], [1, 3, 11], [1, 2, 10], [1, 3, 11], [1, 2, 9], [0, 3, 10],
    [0, 3, 10], [0, 2, 8], [0, 2, 8], [1, 3, 11], [1, 3, 11]]

@[expose] def v6CollapseCheckFast : Bool :=
  (List.finRange 24).all fun k => gluingComplete k || subsetCheck (v6aWords k) (collSet k) 200000 1

@[expose] def V6CollapseCheckFast : Prop := v6CollapseCheckFast = true

end CFSG.ClassicalInvolution.Q3.Q3V
