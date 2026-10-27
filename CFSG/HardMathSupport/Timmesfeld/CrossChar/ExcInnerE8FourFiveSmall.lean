module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFivePBig
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwSmallThree

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false

theorem setupRigidAtFrobenius_E8_four_five_three (hAK3 : AnyKindCommuteThreeFull) :
    SetupRigidAtFrobenius .E8 e8PhiFourWeyl 5 fun q => q = 3 := by
  intro K _ _ Fr hFr g0 hg0C hg0 S hSD hq3
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hq : S.D.q = Nat.card K := by rw [hSD]; rfl
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hq]; exact hFr c
  have hΦ : S.D.Φ = Units.map (entrywiseHom Fr) := by rw [hSD]; rfl
  have hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8PhiFourWeyl := by
    rw [hSD]; rfl
  have hMΓ : S.D.model ≤ S.Γ := by
    show S.D.model ≤ S.D.Γ
    rw [hSD]
    exact model_le_Γ_ofFrobenius_E8 e8PhiFourWeyl K hFr hg0C hg0
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 1 (by rw [hq, pow_one])
  have hw4 : ∀ δ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 δ →
      e8PhiFourWeyl • e8PhiFourWeyl • δ = -δ := fun δ _ => e8PhiFourWeyl_sq_smul δ
  exact setupRigid_E8_three_of_pbig hAK3 S (hq.trans hq3) hAlg
    (bigAnyPBig_of_phi4_of_ne_two S hFr' hΦ hn (Or.inr (Or.inr (Or.inr rfl))) hw4 (by norm_num)
      hMΓ)
    (rho_ne_of_frob_sq_neg S hFr' hΦ hn hw4)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
