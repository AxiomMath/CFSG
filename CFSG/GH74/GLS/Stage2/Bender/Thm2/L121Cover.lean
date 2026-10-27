module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Alt
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Bender.Thm2

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L121

theorem card_eq_two_mul {K : Type} [Group K] {n : ℕ} (h : IsDoubleCoverOfAlt K n) :
    Nat.card K = 2 * Nat.card (alternatingGroup (Fin n)) := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  rw [Nat.card_congr e.toEquiv, hc] at h1
  omega

theorem factorization_two_pow_mul {m : ℕ} (hm : ¬ 2 ∣ m) (hm0 : m ≠ 0) :
    (2 ^ 8 * m).factorization 2 = 8 := by
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  simp

theorem card_alt_ten : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem card_alt_eleven : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem card_comap_mk' {M : Type} [Group M] [Finite M] (O : Subgroup M) [O.Normal]
    (C : Subgroup (M ⧸ O)) : Nat.card (C.comap (QuotientGroup.mk' O)) = Nat.card C * Nat.card O := by
  have h1 := (C.comap (QuotientGroup.mk' O)).card_mul_index
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective O),
    Subgroup.card_eq_card_quotient_mul_card_subgroup O, ← C.card_mul_index] at h1
  have hi : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  rw [h1]
  ring

theorem odd_card_pPrimeCore' (X : Type) [Group X] [Finite X] : Odd (Nat.card (pPrimeCore 2 X)) :=
  Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

variable {G : Type} [Group G] [Finite G]

theorem card_S_eq {z : G} {S : Subgroup G} (ctx : Stage2Ctx G z Kind.ly S) : Nat.card ↥S = 2 ^ 8 := by
  have hd := ctx.data
  cases hd with
  | ly hm =>
    obtain ⟨n, hn, hs⟩ := hm
    have hcov := hs.cover
    have h1 := ctx.sylow.card_eq
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥(Cen z))
    have h3 : Nat.card (CentralizerBar z) = 2 * Nat.card (alternatingGroup (Fin n)) :=
      card_eq_two_mul hcov
    have hodd := odd_card_pPrimeCore' ↥(Cen z)
    have hodd' : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(Cen z)) := fun h =>
      (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    have hfac : (Nat.card ↥(Cen z)).factorization 2 = 8 := by
      rw [h2]
      change (Nat.card (CentralizerBar z) * Nat.card (pPrimeCore 2 ↥(Cen z))).factorization 2 = 8
      rw [Nat.factorization_mul (Nat.card_pos).ne' (Nat.card_pos).ne']
      rw [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd', add_zero, h3]
      rcases hn with rfl | rfl
      · rw [card_alt_ten]
        have := factorization_two_pow_mul (m := 14175) (by norm_num) (by norm_num)
        simpa using this
      · rw [card_alt_eleven]
        have := factorization_two_pow_mul (m := 155925) (by norm_num) (by norm_num)
        simpa using this
    rw [h1, hfac]

omit [Finite G] in
theorem isDoubleCoverOfAlt_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : IsDoubleCoverOfAlt A n) : IsDoubleCoverOfAlt B n := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ⟨?_⟩⟩
  · rw [← hc, ← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e]
    exact Subgroup.card_map_of_injective e.injective
  · exact (QuotientGroup.congr (center A) (center B) e
      (CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e)).symm.trans f

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L121
