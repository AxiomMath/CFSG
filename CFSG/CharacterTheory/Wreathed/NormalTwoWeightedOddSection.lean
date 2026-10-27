module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.ProductCharacterFormula

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

universe u

variable {K : Type u} [Group K] [Fintype K]

theorem regular_weighted_pair_sum_eq_zero (basis : FiniteIrreducibleCharacterBasis K)
    (A B : Finset K) (y : K) (hy : ∀ a ∈ A, ∀ b ∈ B, a * b * y ≠ 1) :
    ∑ θ, (basis.representation θ).character 1 *
      ∑ a ∈ A, ∑ b ∈ B, (basis.representation θ).character (a * b * y) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [regular_character_sum basis (a * b * y), ite_eq_right (hy a ha b hb)]

theorem normal_two_subgroup_weighted_odd_section_support (basis : FiniteIrreducibleCharacterBasis K)
    (P : Subgroup K) [P.Normal] (hP : IsPGroup 2 P) (t v : K) (htP : t ∈ P)
    (htcenter : t ∈ Subgroup.center K) (ht : orderOf t = 2) (hvP : v ∈ P) (hv : orderOf v = 2)
    (hconj : IsConj (t * v) v) (lam : ℂ) :
    let F : K → ℂ := fun h => ∑ θ, ((basis.representation θ).character t +
        lam * (basis.representation θ).character v) ^ 2 *
          (basis.representation θ).character (t * h) / (basis.representation θ).character 1
    (∀ h : K, h ∉ P → F h = 0) ∧
    ∀ h : K, Odd (orderOf h) →
      F h = if h = 1 then lam ^ 2 * (Nat.card (Subgroup.centralizer {v}) : ℂ) else 0 := by
  intro F
  set X : Finset K := Finset.univ.filter fun x => IsConj v x with hX
  set T : Finset K := {t} with hT
  have hXinv : ConjInvariant X := by
    intro c x
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      exact hx.trans (isConj_iff.mpr ⟨c, rfl⟩)
    · intro hx
      exact hx.trans (isConj_iff.mpr ⟨c, rfl⟩).symm
  have hTinv : ConjInvariant T := by
    intro c x
    simp only [hT, Finset.mem_singleton]
    constructor
    · rintro rfl
      rw [Subgroup.mem_center_iff.mp htcenter c, mul_inv_cancel_right]
    · intro hx
      have hx' : x = c⁻¹ * t * c := by rw [← hx]; group
      rw [hx', Subgroup.mem_center_iff.mp htcenter c⁻¹, inv_mul_cancel_right]
  have hXP : ∀ x ∈ X, x ∈ P := by
    intro x hx
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hx
    exact (inferInstance : P.Normal).conj_mem v hvP c
  have hXcard : (X.card : ℂ) ≠ 0 := by
    have hvX : v ∈ X := by
      simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsConj.refl v
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hvX)
  have hsummand : ∀ (θ : basis.index) (y : K),
      ((basis.representation θ).character t + lam * (basis.representation θ).character v) ^ 2 *
          (basis.representation θ).character y / (basis.representation θ).character 1 =
        (basis.representation θ).character 1 *
          (∑ a ∈ T, ∑ b ∈ T, (basis.representation θ).character (a * b * y) +
            2 * (lam / X.card) * ∑ a ∈ T, ∑ b ∈ X, (basis.representation θ).character (a * b * y) +
            (lam / X.card) ^ 2 *
              ∑ a ∈ X, ∑ b ∈ X, (basis.representation θ).character (a * b * y)) := by
    intro θ y
    have hdeg : (basis.representation θ).character 1 ≠ 0 :=
      irreducible_character_degree_ne_zero _ (basis.irreducible θ)
    have hirr := basis.irreducible θ
    have hTT := irreducible_character_product_sum (basis.representation θ) hirr T T hTinv hTinv y
    have hTX := irreducible_character_product_sum (basis.representation θ) hirr T X hTinv hXinv y
    have hXX := irreducible_character_product_sum (basis.representation θ) hirr X X hXinv hXinv y
    have hsumT : ∑ a ∈ T, (basis.representation θ).character a =
        (basis.representation θ).character t := by simp [hT]
    have hsumX : ∑ x ∈ X, (basis.representation θ).character x =
        X.card * (basis.representation θ).character v := by
      rw [Finset.sum_congr rfl (fun x hx => ?_), Finset.sum_const, nsmul_eq_mul]
      simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hx
      exact Representation.char_conj _ v c
    rw [hTT, hTX, hXX, hsumT, hsumX]
    field_simp
    ring
  have hout : ∀ h : K, h ∉ P → F h = 0 := by
    intro h hh
    have hy : ∀ A B : Finset K, (∀ a ∈ A, a ∈ P) → (∀ b ∈ B, b ∈ P) →
        ∀ a ∈ A, ∀ b ∈ B, a * b * (t * h) ≠ 1 := by
      intro A B hA hB a ha b hb heq
      apply hh
      have hmem : (a * b * t)⁻¹ ∈ P :=
        P.inv_mem (P.mul_mem (P.mul_mem (hA a ha) (hB b hb)) htP)
      have habth : a * b * t * h = 1 := by rw [mul_assoc (a * b)]; exact heq
      rw [eq_inv_of_mul_eq_one_right habth]
      exact hmem
    have hTP : ∀ a ∈ T, a ∈ P := by
      intro a ha
      rw [hT, Finset.mem_singleton] at ha
      rw [ha]
      exact htP
    change ∑ θ, _ = 0
    simp_rw [hsummand _ (t * h), mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp_rw [mul_left_comm ((basis.representation _).character 1) (2 * (lam / X.card)),
      mul_left_comm ((basis.representation _).character 1) ((lam / X.card) ^ 2)]
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      regular_weighted_pair_sum_eq_zero basis T T _ (hy T T hTP hTP),
      regular_weighted_pair_sum_eq_zero basis T X _ (hy T X hTP hXP),
      regular_weighted_pair_sum_eq_zero basis X X _ (hy X X hXP hXP)]
    ring
  refine ⟨hout, fun h hodd => ?_⟩
  by_cases h1 : h = 1
  ·
    simp only [h1, ↓reduceIte]
    obtain ⟨-, hsum⟩ := central_involution_conjugate_product_weighted_character_sum basis t v
      htcenter ht hv hconj lam
    rw [← hsum]
    change ∑ θ, _ = _
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [mul_one]
    ring
  · simp only [h1, ↓reduceIte]
    apply hout
    intro hmem
    obtain ⟨n, hn⟩ := hP ⟨h, hmem⟩
    have hord : orderOf h ∣ 2 ^ n := by
      rw [← Subgroup.orderOf_mk h hmem]
      exact orderOf_dvd_of_pow_eq_one hn
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    rcases i with _ | i
    · rw [pow_zero, orderOf_eq_one_iff] at hi
      exact h1 hi
    · have heven : Even (orderOf h) := by
        rw [hi, pow_succ]
        exact even_two.mul_left _
      exact (Nat.not_even_iff_odd.mpr hodd) heven

end CFSG.Wreathed
