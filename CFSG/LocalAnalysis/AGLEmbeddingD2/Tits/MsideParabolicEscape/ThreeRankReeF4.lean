module

public import CFSG.RankThree.PartOne.KLC.TwF4
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.LieType.Ree CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.KLR
  CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


theorem pRank_three_ne_one_reeF4 {S : Type} [Group S] [Finite S] (m : ℕ)
    (hv : (LieTypeIndex.reeF4 m).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  obtain ⟨X, _, _, _, hm, hX, -, ⟨φ⟩⟩ := exists_reeGamma_equiv_cat hv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ReeTag.F4.reeGamma X m) := Finite.of_equiv _ (e.trans φ).toEquiv
  obtain ⟨D⟩ := reeFrameData_nonempty (K := X) (L := AlgebraicClosure X) hX
  have : CharP (AlgebraicClosure X) 2 :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective 2
  have h3 : (3 : ℤ) ∣ 2 ^ (2 * m + 1) + 1 := by
    have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have : 3 ∣ 2 ^ (2 * m + 1) + 1 := by omega
    exact_mod_cast this
  obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_phi2 (L := AlgebraicClosure X) D.isFrob Nat.prime_three
    (by norm_num) h3
  have h2 := two_le_pRank_reeGamma D wPhi2 Nat.prime_three (by norm_num) Φ hΦ hΦF
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (e.trans φ)] at h2
  omega

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank
