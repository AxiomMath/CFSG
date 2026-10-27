module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.EvenClass
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Classes
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6Good
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.Quad
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree


variable {K : Type} [Field K] [Finite K]

theorem d4Graph_one_pow_three : d4Graph K 1 ^ 3 = 1 := by
  rw [pow_succ, pow_two, ← d4Graph_add, ← d4Graph_add, d4Graph_three]

theorem gammaP_uv_pow_three (hK : Nat.card K = 2) : gammaP K (uSL 1 * vSL 1) ^ 3 = 1 := by
  have hK2 : ringChar K = 2 := by
    have : Fintype K := Fintype.ofFinite K
    have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    exact (FiniteField.even_card_iff_char_two (F := K)).2 (by rw [hc])
  have : CharP K 2 := ringChar.of_eq hK2
  have hc : Commute (MulAut.conj (sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1))) (d4Graph K 1) := by
    have := commute_conj_of_fixed (d4Graph_one_sl2Two (K := K) (uSL 1 * vSL 1))
    exact this.symm
  rw [gammaP, hc.mul_pow, ← map_pow, ← map_pow, uSL_mul_vSL_pow_three, map_one, map_one,
    one_mul, d4Graph_one_pow_three]

theorem ordG2_two : CFSG.Open.ordG2 (2 ^ 1) = 12096 := by
  decide

theorem cardFixGammaPTwo_holds :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      Nat.card (fixedSubgroup (gammaP K (uSL 1 * vSL 1))) ∣ 12096 := by
  intro K _ _ hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; rfl
  have hα : gammaP K (uSL 1 * vSL 1) = MulAut.conj (sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1)) *
      (exactNormalAut Tag.D4 K 1 1 0 * d4Graph K 1) := by
    rw [CFSG.StandardType.AutSt.exactNormalAut_one_one_zero, one_mul]
    rfl
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv
      (ℓ := 2) (f := 1) le_rfl K hK' (gammaP K (uSL 1 * vSL 1)) (gammaP_uv_pow_three hK)
      (sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1)) 1 (Or.inl rfl) hα
  obtain ⟨y, hy, hcard⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_card_fixedSubgroup_eq_class (n := 1) le_rfl hK₃
      hFr hφ3 hφout
  have h1 : Nat.card (fixedSubgroup (gammaP K (uSL 1 * vSL 1))) =
      Nat.card (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup φ) :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)).trans
      ((Nat.card_congr e.toEquiv).trans (Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)))
  rw [h1, hcard, ← ordG2_two]
  rcases hy with rfl | rfl
  · rw [map_one, one_mul, CFSG.HardMathSupport.Lang.E6Descent.card_fixedSubgroup_sigma0 le_rfl hK₃
      hFr]
  · have h := CFSG.HardMathSupport.Lang.E6Descent.card_dvd_ordG2_of_isoPGUThree le_rfl
      (CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds 1 odd_one K₃ Fr hK₃ hFr)
    rwa [CFSG.HardMathSupport.Lang.E6Descent.autFix_eq_fixedSubgroup] at h

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
