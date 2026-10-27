module

public import CFSG.ClassicalInvolution.Phan.PhanS15Geom

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open SimpleGraph CFSG.ClassicalInvolution.PhanB3.S.Std CFSG.ClassicalInvolution.PhanB3.S

variable {K : Type} [Field K] {M : Model K}

@[expose] def MuAdj (M : Model K) (A C x y : FFPt M) : Prop :=
  (ffGraph M).Adj x y ∧ (ffGraph M).Adj A x ∧ (ffGraph M).Adj A y ∧ (ffGraph M).Adj C x ∧
    (ffGraph M).Adj C y

@[expose] def MuConnected (M : Model K) : Prop :=
  ∀ A C : FFPt M, bf M A.1.rep C.1.rep ≠ 0 → ∀ B D : FFPt M, (ffGraph M).Adj A B →
    (ffGraph M).Adj C B → (ffGraph M).Adj A D → (ffGraph M).Adj C D →
      Relation.ReflTransGen (MuAdj M A C) B D

theorem qn_of_muPath {A C B D : FFPt M} (h : Relation.ReflTransGen (MuAdj M A C) B D) :
    QN (ffGraph M) A B C D := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact QN.of_eq_diag
  | head hstep _ ih => exact QN.move hstep.2.2.1 hstep.1 hstep.2.2.2.2 ih

theorem bbQuad_of_muConnected (h : MuConnected M) : BBQuad M := by
  intro A B C D hac _ hab hbc hcd hda
  exact qn_of_muPath (h A C hac B D hab hbc.symm hda.symm hcd) hab hbc hcd hda

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q

namespace CFSG.ClassicalInvolution.PhanB3.S

theorem q7Residual_of_muConnected
    (h : ∀ (K : Type) [Field K] [Finite K] (M : Std.Model K), M.q = 7 → Std.Q.MuConnected M) :
    Q7Residual :=
  fun K _ _ M hM => Std.Q.bbQuad_of_muConnected (h K M hM)

end CFSG.ClassicalInvolution.PhanB3.S
