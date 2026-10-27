module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1314
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrderBig
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts4

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.CatalogueFi23

open CFSG.Open CFSG.ComponentClassification.CatLeaf

theorem lieModel_three_card_ne_fi23 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 3 f)
    (hX : CFSG.Blueprint.LieModel X t n 3 f) : Nat.card X ≠ 4089470473293004800 := by
  intro hc
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 13) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework_le (by norm_num) hadm hb with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, hf1, hf2⟩
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
  · rcases ht with rfl | rfl <;> revert hord <;> decide
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
      simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
      revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

section Lie


theorem not_isLieChar_three_of_card {K : Type} [Group K] [IsSimpleGroup K]
    (hK : Nat.card K = 4089470473293004800) : ¬ IsLieChar (· = 3) K := by
  rintro ⟨idx, ⟨g⟩, hc⟩
  have hc3 : idx.1.characteristic = 3 := hc
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  obtain ⟨t, n, p, f, hM, hp, -⟩ := AltFacts4.exists_lieModel_tagged idx
  have hX : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) t n p f :=
    CFSG.Blueprint.LieModel.of_mulEquiv g.symm
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hM)
  obtain rfl : p = 3 := hp.trans hc3
  have hadm := CFSG.Blueprint.LieModel.admissible hX
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hZ | hZ
  · have h1 : Nat.card (Subgroup.center K) = 1 := Subgroup.card_eq_one.2 hZ
    rw [h1, mul_one, hK] at hQ
    exact lieModel_three_card_ne_fi23 hO hadm hX hQ.symm
  · have h1 : Nat.card (Subgroup.center K) = Nat.card K := by rw [hZ, Subgroup.card_top]
    rw [h1, hK] at hQ
    have hQ1 : Nat.card (K ⧸ Subgroup.center K) = 1 := by omega
    have h3 := AltFacts4.dvd_card_of_lieModel hO hadm hX
    rw [hQ1] at h3
    omega

section Fi23


theorem inputFi23NotChev3_holds : Claims1314.InputFi23NotChev3 := by
  intro K _ hK
  obtain ⟨e⟩ := hK
  obtain ⟨e'⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  have hS : IsSimpleGroup K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 (e.trans e'.symm)
  have hc : Nat.card K = 4089470473293004800 :=
    (Nat.card_congr (e.trans e'.symm).toEquiv).trans CFSG.Sporadic.Fi23.card_Fi23
  exact not_isLieChar_three_of_card hc

end Fi23

end Lie

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.CatalogueFi23

end
