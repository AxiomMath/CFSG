module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.ClassicalInvolution.Q3.Q3ZWords

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.CosetTable

@[expose] def c2Subset : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]

@[expose] def v6LayerCheck : Bool :=
  subsetCheck (restrictWords (subsetOf 12 c2Subset) v6Words) [] 400000 51840

@[expose] def v6IndexCheck : Bool :=
  subsetCheck v6Words c2Subset 3000000 176904

@[expose] def v6CollapseCheck : Bool :=
  (List.finRange 24).all fun k => gluingComplete k || subsetCheck (v6aWords k) [] 1000000 1

@[expose] def V6Check : Prop := v6LayerCheck = true ∧ v6IndexCheck = true

@[expose] def V6CollapseCheck : Prop := v6CollapseCheck = true

end CFSG.ClassicalInvolution.Q3.Q3Z
