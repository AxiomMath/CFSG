module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareLinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeG2

public section

namespace CFSG.AGLEmbeddingD2.SquareSmall

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.SquareGeneric CFSG.AGLEmbeddingD2.SquareLinear

local notation "A₅" => alternatingGroup (Fin 5)

section Card

variable {G : Type*} [Group G] [Finite G] {Q : Type*} [Group Q] [Finite Q]

omit [Finite G] [Finite Q] in
theorem HasSubquotient.card_dvd {H : Subgroup G} (h : LeviSection.HasSubquotient H Q) :
    Nat.card Q ∣ Nat.card H := by
  obtain ⟨X, hX, ψ, hψ⟩ := h
  have h1 : Nat.card Q ∣ Nat.card X := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [this, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
    exact dvd_mul_right _ _
  exact h1.trans (Subgroup.card_dvd_of_le hX)

theorem card_alt_five_sq : Nat.card (A₅ × A₅) = 3600 := by
  rw [Nat.card_prod, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

omit [Finite G] [Finite Q] in
theorem false_of_hasSubquotient_of_not_dvd {H : Subgroup G} (h25 : ¬ 25 ∣ Nat.card H)
    (h : LeviSection.HasSubquotient H (A₅ × A₅)) : False := by
  apply h25
  have := HasSubquotient.card_dvd h
  rw [card_alt_five_sq] at this
  exact (by norm_num : 25 ∣ 3600).trans this

theorem not_dvd_card_alt {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) :
    ¬ 25 ∣ Nat.card (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl | rfl <;>
    · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide

theorem not_dvd_card_of_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Assembly.LowTwoRank.StatedProj H)
    (h : ¬ 25 ∣ Nat.card (GL ι K)) : ¬ 25 ∣ Nat.card Y := by
  intro h25
  apply h
  have h1 : Nat.card Y ∣ Nat.card H := by
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  exact h25.trans (h1.trans (Subgroup.card_subgroup_dvd_card H))

theorem not_dvd_card_GL_two_seven {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 7) :
    ¬ 25 ∣ Nat.card (GL (Fin 2) K) := by
  rw [Matrix.card_GL_field, hK]
  decide

theorem not_dvd_card_GL_three_nine {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 9) :
    ¬ 25 ∣ Nat.card (GL (Fin 3) K) := by
  rw [Matrix.card_GL_field, hK]
  decide

end Card

theorem isCyclic_of_isPGroup_three_sl2' {F : Type} [Field F] [Finite F] [CharP F 2]
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hP : IsPGroup 3 P) : IsCyclic P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases h4 : 4 ≤ Nat.card F
  · exact isCyclic_of_isPGroup_three_sl2 h4 P hP
  · have := Fintype.ofFinite F
    obtain ⟨f, -, hf⟩ := FiniteField.card F 2
    have hf1 : (f : ℕ) = 1 := by
      have : 2 ^ (f : ℕ) < 4 := by rw [← hf, ← Nat.card_eq_fintype_card]; omega
      have := f.pos
      have h2 : (f : ℕ) < 2 := by
        by_contra h
        have : 2 ^ 2 ≤ 2 ^ (f : ℕ) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
      rw [card_sl2, Nat.card_eq_fintype_card, hf, hf1]
      norm_num
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
    have hdvd : 3 ^ k ∣ 6 := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card P
    have hk1 : k ≤ 1 := by
      by_contra h
      have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      have := this.trans hdvd
      norm_num at this
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with rfl | rfl
    · rw [pow_zero] at hk
      have := (Nat.card_eq_one_iff_unique.1 hk).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem isCyclic_of_isPGroup_three_rankOne_g2 (i : Fin (Tag.rank .G2))
    (P : Subgroup ↥(adjointGroup .G2 K)) (hP : P ≤ rankOne (g2Datum K).rootGroup i)
    (h3 : IsPGroup 3 P) : IsCyclic P := by
  obtain ⟨φ, hφ, hx, hy⟩ := g2_exists_sl2_hom (K := K) i
  have hrange : rankOne (g2Datum K).rootGroup i = φ.range :=
    rankOne_eq_range_of_sl2
      (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := K)
        (RootSystem.ofCartan (g2Datum K).isFiniteType (g2Datum K).divisible)
        (adjDatum_roots (rootOperatorFamily .G2) K))
      (fun c => (hx c).trans (xPar_simple i c).symm)
      (fun c => (hy c).trans (xPar_neg_simple i c).symm)
  rw [hrange] at hP
  exact isCyclic_of_le_range hφ hP
    (isCyclic_of_isPGroup_three_sl2' _ (h3.comap_of_injective _ hφ))

theorem false_of_square_g2 {Y : Type} [Group Y] [Finite Y] (e : Y ≃* AdjointQuotient .G2 K)
    (T : Sylow 2 Y) (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ ⊤) (hQ : LeviSection.HasSubquotient J (A₅ × A₅)) : False := by
  have hb := borelQuotient_g2 (K := K) e
  obtain ⟨π', hb', -, hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  have hM := hasSubquotient_leviM_of_parab hb' hBJ hQ
  have hBJ' : (borel (g2Datum K) (torus (τ := .G2) K)).map π' ≤ J :=
    Subgroup.map_le_iff_le_comap.mpr hBJ
  obtain ⟨j, hj⟩ := LieOut.exists_node_not_mem_negIndices hb' hBJ' hJ
  have hrank : (g2Datum K).rank = 2 := rfl
  have hsub : (negIndices (g2Datum K) (J.comap π')).Subsingleton := by
    intro x hx y hy
    have hxj : x.val ≠ j.val := fun h => hj (Fin.ext h ▸ hx)
    have hyj : y.val ≠ j.val := fun h => hj (Fin.ext h ▸ hy)
    have h1 : x.val < 2 := x.isLt
    have h2 : y.val < 2 := y.isLt
    have h3 : j.val < 2 := j.isLt
    exact Fin.ext (by omega)
  rcases hsub.eq_empty_or_singleton with hI | ⟨i, hI⟩
  · rw [hI, leviM_empty] at hM
    exact false_of_hasSubquotient_bot hM
  · rw [hI, leviM_singleton] at hM
    exact false_of_hasSubquotient_of_isCyclic
      (fun P hP h3P => isCyclic_of_isPGroup_three_rankOne_g2 i P hP h3P) hM

end G2

end CFSG.AGLEmbeddingD2.SquareSmall
