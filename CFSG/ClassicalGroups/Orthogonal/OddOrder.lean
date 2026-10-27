module

public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap CFSG.LieType.Universal.Spin
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem sq_mem_commutator_of_le_closure (O : Subgroup G) (R : Set G) (hRO : R ⊆ O)
    (hR : ∀ r ∈ R, r ^ 2 = 1) (hle : O ≤ Subgroup.closure (R ∪ (⁅O, O⁆ : Subgroup G) : Set G))
    {g : G} (hg : g ∈ O) : g ^ 2 ∈ (⁅O, O⁆ : Subgroup G) := by
  have hNO : (⁅O, O⁆ : Subgroup G) ≤ O := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have key : g ∈ O ∧ g ^ 2 ∈ (⁅O, O⁆ : Subgroup G) := by
    refine Subgroup.closure_induction (p := fun g _ => g ∈ O ∧ g ^ 2 ∈ (⁅O, O⁆ : Subgroup G))
      ?_ ?_ ?_ ?_ (hle hg)
    · rintro x (hx | hx)
      · exact ⟨hRO hx, by rw [hR x hx]; exact Subgroup.one_mem _⟩
      · exact ⟨hNO hx, by rw [pow_two]; exact Subgroup.mul_mem _ hx hx⟩
    · exact ⟨Subgroup.one_mem _, by rw [one_pow]; exact Subgroup.one_mem _⟩
    · rintro a b - - ⟨ha, ha2⟩ ⟨hb, hb2⟩
      refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
      have hc : ⁅a⁻¹, b⁆ ∈ (⁅O, O⁆ : Subgroup G) :=
        Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ ha) hb
      have : (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := by
        simp only [commutatorElement_def, pow_two]
        group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha2 hc) hb2
    · rintro a - ⟨ha, ha2⟩
      refine ⟨Subgroup.inv_mem _ ha, ?_⟩
      have : a⁻¹ ^ 2 = (a ^ 2)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha2
  exact key.2

theorem mem_of_odd_pow_of_sq_mem {N : Subgroup G} {g : G} (hg : ∀ x : G, x = g → x ^ 2 ∈ N)
    {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) : g ∈ N := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : g ^ 2 ∈ N := hg g rfl
  have : g = (g ^ 2) ^ (k + 1) := by
    have : g ^ (2 * (k + 1)) = g := by
      have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [this, pow_succ, hgm, one_mul]
    rw [← pow_mul, this]
  rw [this]
  exact Subgroup.pow_mem _ h2 _

end Generic

variable {K : Type} [Field K] {n : ℕ}

theorem sq_mem_elementaryGroup_quadPlus (h2 : (2 : K) = 0) (hn : 3 ≤ n)
    {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)) :
    g ^ 2 ∈ elementaryGroup (quadPlus n K) := by
  have hn0 : 0 < n := by omega
  have hE := commutator_orthogonalGroup_quadPlus (K := K) hn
  rw [← hE]
  refine sq_mem_commutator_of_le_closure
    (TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (Set.range (reflect (quadPlus n K)))
    (by rintro _ ⟨v, rfl⟩; exact reflect_mem_orthogonalGroup _ v)
    (by rintro _ ⟨v, rfl⟩; rw [pow_two]; exact reflect_mul_self _ v) ?_ hg
  rw [hE]
  exact orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth hn0)
    (nondegenerate_polarBilin_quadPlus n K) h2
    (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily hn0 hx)
    (fun x hx hx0 => absurd (eq_zero_of_mem_tailSpace_plusFamily hn0 hx) hx0) (by omega)

theorem mem_elementaryGroup_quadPlus_of_odd_pow (h2 : (2 : K) = 0) (hn : 3 ≤ n)
    {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) :
    g ∈ elementaryGroup (quadPlus n K) :=
  mem_of_odd_pow_of_sq_mem (fun _ hx => hx ▸ sq_mem_elementaryGroup_quadPlus h2 hn hg) hm hgm

end CFSG.ClassicalGroups.Orthogonal
