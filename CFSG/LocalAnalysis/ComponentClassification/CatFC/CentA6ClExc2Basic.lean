module

public import CFSG.LocalAnalysis.SteinbergCAOddResidualOrderFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem a6_orderOf_ne_six (g : alternatingGroup (Fin 6)) : orderOf g ≠ 6 := by
  intro h
  have h6 : g ^ 6 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [h] at this
  have h2 : g ^ 2 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [h] at this
    omega
  have h3 : g ^ 3 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [h] at this
    omega
  have key : ∀ g : alternatingGroup (Fin 6), g ^ 6 = 1 → g ^ 2 = 1 ∨ g ^ 3 = 1 := by
    decide +kernel
  rcases key g h6 with h' | h'
  · exact h2 h'
  · exact h3 h'

theorem a6_orderOf_ne_ten (g : alternatingGroup (Fin 6)) : orderOf g ≠ 10 := by
  intro h
  have h10 : g ^ 10 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [h] at this
  have h2 : g ^ 2 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [h] at this
    omega
  have h5 : g ^ 5 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [h] at this
    omega
  have key : ∀ g : alternatingGroup (Fin 6), g ^ 10 = 1 → g ^ 2 = 1 ∨ g ^ 5 = 1 := by
    decide +kernel
  rcases key g h10 with h' | h'
  · exact h2 h'
  · exact h5 h'

theorem a6_orderOf_ne_two_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (g : alternatingGroup (Fin 6)) : orderOf g ≠ 2 * p := by
  intro h
  have hdvd : 2 * p ∣ 360 := by
    rw [← h, ← a6sq_card]
    exact orderOf_dvd_natCard g
  have hp180 : p ∣ 180 := by
    have : 2 * p ∣ 2 * 180 := by simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hp' : p = 3 ∨ p = 5 := by
    have h180 : (180 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 := by norm_num
    rw [h180] at hp180
    rcases (Nat.Prime.dvd_mul hp).1 hp180 with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)) hp2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)
  rcases hp' with rfl | rfl
  · exact a6_orderOf_ne_six g h
  · exact a6_orderOf_ne_ten g h

theorem false_of_hom_A6 {G : Type*} [Group G] {S : Subgroup G}
    (eS : S ≃* alternatingGroup (Fin 6)) {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) (φ : Matrix.SpecialLinearGroup (Fin 2) F →* G) (hφS : ∀ A, φ A ∈ S)
    (hneg : φ (-1) ≠ 1) (hu : φ (CFSG.LieType.Chevalley.uSL 1) ≠ 1) : False := by
  have h := CFSG.LocalAnalysis.SteinbergCA.orderOf_neg_one_mul_uSL_one hp2 φ hneg hu
  have hmem : φ (-1) * φ (CFSG.LieType.Chevalley.uSL 1) ∈ S := mul_mem (hφS _) (hφS _)
  refine a6_orderOf_ne_two_mul_prime (Fact.out : p.Prime) hp2 (eS ⟨_, hmem⟩) ?_
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h]

theorem false_of_injective_SL2_A6 {G : Type*} [Group G] {S : Subgroup G} {k : Type*} [Field k]
    [Finite k] (hk : ringChar k ≠ 2) (φ : Matrix.SpecialLinearGroup (Fin 2) k →* S)
    (hφ : Function.Injective φ) (eS : S ≃* alternatingGroup (Fin 6)) : False := by
  have : Fintype k := Fintype.ofFinite k
  have : CharP k (ringChar k) := ringChar.charP k
  obtain ⟨n, hp, -⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hp⟩
  have hinj : Function.Injective (S.subtype.comp φ) := S.subtype_injective.comp hφ
  refine false_of_hom_A6 eS hk (S.subtype.comp φ) (fun A => (φ A).2) (fun h => ?_) (fun h => ?_)
  · have h1 := hinj (h.trans (map_one _).symm)
    have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) k =>
      (A : Matrix (Fin 2) (Fin 2) k) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h2
    exact Ring.neg_one_ne_one_of_char_ne_two hk h2
  · exact CFSG.LocalAnalysis.SteinbergCA.uSL_one_ne_one_and_ne_neg_one.1
      (hinj (h.trans (map_one _).symm))

section Data

variable {S : Type} [Group S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem A6Hyp.normal_simple_data (h : A6Hyp σ D) :
    D.Normal ∧ IsSimpleGroup ↥D ∧ (∃ a b : ↥D, a * b ≠ b * a) ∧ 2 ∣ Nat.card ↥D ∧
      Nonempty (↥D ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hDn, ⟨e⟩, -⟩ := h
  haveI := a6sq_simple
  have hs : IsSimpleGroup ↥D := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := a6sq_nonab
  refine ⟨hDn, hs, ⟨e.symm a, e.symm b, fun h' => hab ?_⟩, ?_, ⟨e⟩⟩
  · apply e.symm.injective
    rw [map_mul, map_mul]
    exact h'
  · rw [Nat.card_congr e.toEquiv, a6sq_card]
    norm_num

end Data

end CFSG.ComponentClassification.CatFC
