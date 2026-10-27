module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem inf_normalizer_eq_inf_centralizer_of_inf_eq_bot {A H : Subgroup G} (hAH : A ⊓ H = ⊥)
    (hHA : H ≤ normalizer (A : Set G)) :
    A ⊓ normalizer (H : Set G) = A ⊓ centralizer (H : Set G) := by
  apply le_antisymm
  · intro a ha
    rw [Subgroup.mem_inf] at ha ⊢
    refine ⟨ha.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hH : a * h * a⁻¹ * h⁻¹ ∈ H := by
      have hconj : a * h * a⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp ha.2 h).mp hh
      exact H.mul_mem hconj (H.inv_mem hh)
    have hA : a * h * a⁻¹ * h⁻¹ ∈ A := by
      have hhN : h ∈ normalizer (A : Set G) := hHA hh
      have hc : h * a⁻¹ * h⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hhN a⁻¹).mp (A.inv_mem ha.1)
      simpa only [mul_assoc] using A.mul_mem ha.1 hc
    have hmem : a * h * a⁻¹ * h⁻¹ ∈ A ⊓ H := ⟨hA, hH⟩
    have h1 : a * h * a⁻¹ * h⁻¹ = 1 := by
      have := hmem
      rw [hAH] at this
      simpa using this
    have hca : a * h * a⁻¹ = h := mul_inv_eq_one.mp h1
    exact (mul_inv_eq_iff_eq_mul.mp hca).symm
  · exact inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer (H : Set G))

theorem sup_inf_normalizer_eq {P H : Subgroup G} (hHP : H ≤ normalizer (P : Set G)) :
    (P ⊔ H) ⊓ normalizer (H : Set G) = P ⊓ normalizer (H : Set G) ⊔ H := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx_sup, hxN⟩ := hx
    have hxHP : x ∈ H ⊔ P := by simpa [sup_comm] using hx_sup
    have hxmul : x ∈ (H : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H P hHP]
      exact hxHP
    obtain ⟨h, hhH, p, hpP, rfl⟩ := Set.mem_mul.mp hxmul
    have hpN : p ∈ normalizer (H : Set G) := by
      have hinv : h⁻¹ ∈ normalizer (H : Set G) :=
        (normalizer (H : Set G)).inv_mem (Subgroup.le_normalizer hhH)
      simpa using (normalizer (H : Set G)).mul_mem hinv hxN
    have hmem : h * p ∈ H ⊔ (P ⊓ normalizer (H : Set G)) :=
      Subgroup.mul_mem_sup hhH ⟨hpP, hpN⟩
    simpa [sup_comm] using hmem
  · exact sup_le (inf_le_inf le_sup_left le_rfl) (le_inf le_sup_right Subgroup.le_normalizer)

theorem not_mem_normalizer_of_three {B Y Q Q' : Subgroup G} {a : G}
    (h3 : ∀ P₁ P₂ P₃ : Subgroup G, (∀ P ∈ [P₁, P₂, P₃], B < P ∧ P < Y) →
      P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃)
    (haB : a ∈ normalizer (B : Set G)) (haY : a ∈ normalizer (Y : Set G)) (hQ : B < Q ∧ Q < Y)
    (hQ' : B < Q' ∧ Q' < Y) (ha : a ∉ normalizer (Q : Set G)) :
    a ∉ normalizer (Q' : Set G) := by
  let f : G →* G := (MulAut.conj a : G →* G)
  let Q₁ : Subgroup G := Q.map f
  have hf : Function.Injective f := (MulAut.conj a).injective
  have hBmap : B.map f = B := Subgroup.mem_normalizer_iff_map_conj_eq.mp haB
  have hYmap : Y.map f = Y := Subgroup.mem_normalizer_iff_map_conj_eq.mp haY
  have hBQ₁ : B < Q₁ := by
    have h := (Subgroup.map_lt_map_iff_of_injective (f := f) hf).mpr hQ.1
    simpa [Q₁, hBmap] using h
  have hQ₁Y : Q₁ < Y := by
    have h := (Subgroup.map_lt_map_iff_of_injective (f := f) hf).mpr hQ.2
    simpa [Q₁, hYmap] using h
  have hQ₁ne : Q₁ ≠ Q := by
    intro h
    refine ha (Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_)
    simpa [Q₁, f] using h
  intro ha'
  have hlist : ∀ P ∈ [Q, Q₁, Q'], B < P ∧ P < Y := by
    intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl
    · exact hQ
    · exact ⟨hBQ₁, hQ₁Y⟩
    · exact hQ'
  rcases h3 Q Q₁ Q' hlist with h | h | h
  · exact absurd h.symm hQ₁ne
  · exact ha (by rw [h]; exact ha')
  · have hQ'fix : Q'.map f = Q' := Subgroup.mem_normalizer_iff_map_conj_eq.mp ha'
    have hmap : Q.map f = Q'.map f := by
      rw [hQ'fix]
      simpa [Q₁, f] using h
    have hQQ' : Q = Q' := Subgroup.map_injective (f := f) hf hmap
    exact ha (by rw [hQQ']; exact ha')

end CFSG.GroupTheory
