module

public import CFSG.ClassicalInvolution.Asc77.AscR10Q9b
public import CFSG.ClassicalInvolution.Asc77.AscT3XAssembly

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.T3CII.T3W

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Fus9Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Concl20_9 S K K' R R' z → 8 < Nat.card R →
          ∀ b : G, FieldInv20 S K K' W z t b →
            (∃ (u : G) (k : ℕ), 2 ≤ k ∧ Subgroup.zpowers u = K ⊓ W ∧ orderOf u = 2 ^ (k + 1) ∧
              ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) → FusAt S z b


theorem res10aNoConj_of_fus9 (h : Fus9Stmt p f) : Res10aNoConj p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb g
  exact d.r9_noConj c7 c9 h8 hb
    (fun b' hb' hplus => h G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b' hb' hplus) g

end CFSG.ClassicalInvolution.Asc77.T3CII
