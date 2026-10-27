module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Lem45
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Lem42

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

namespace M4

theorem orderOf_of_isConj (h : M4 O FA SD z S K₁ K₂) {t : G} (htz : IsConj z t) :
    orderOf t = 2 := by
  obtain ⟨c0, hc0⟩ := isConj_iff.1 htz
  refine orderOf_two_iff.2 ⟨?_, ?_⟩
  · rw [← hc0]
    calc c0 * z * c0⁻¹ * (c0 * z * c0⁻¹) = c0 * (z * z) * c0⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  · intro h1
    apply h.z_ne
    have : c0 * z * c0⁻¹ = 1 := by rw [hc0, h1]
    calc z = c0⁻¹ * (c0 * z * c0⁻¹) * c0 := by group
      _ = 1 := by rw [this]; group

end M4

theorem prop41 [Finite G] (h : M44 O FA SD z S K₁ K₂) (h' : M45 O FA SD z S K₁ K₂)
    (hZ : ∀ P : Subgroup G, Syl2In P ⊤ → ∀ x ∈ P, x * x = 1 → x ≠ 1 →
      (∀ s ∈ P, x * s = s * x) → ∃ g : G, g⁻¹ * x * g ∈ P ∧ g⁻¹ * x * g ≠ x) :
    Qm O S K₁ K₂ = zpowers z ∧
      ((∀ u ∈ Pm S K₁ K₂, orderOf u = 2 → IsConj z u) ∨
        ∃ t ∈ S, IsConj z t ∧ t ≠ z ∧ Intch t K₁ K₂ ∧
          (∀ u ∈ Pm S K₁ K₂, orderOf u = 2 → u ≠ z → IsConj (t * z) u) ∧ ¬ IsConj z (t * z)) ∧
      ∀ t ∈ centralizer ({z} : Set G), IsConj z t → Intch t K₁ K₂ →
        ∀ g : G, g⁻¹ * z * g = t → Intch (g * z * g⁻¹) K₁ K₂ := by
  have hc : ∀ t ∈ centralizer ({z} : Set G), IsConj z t → Intch t K₁ K₂ →
      ∀ g : G, g⁻¹ * z * g = t → Intch (g * z * g⁻¹) K₁ K₂ :=
    fun t htC _ hI g hg => h'.c_part hg htC hI
  by_cases hA : H4A O z S K₁ K₂
  · obtain ⟨t, htS, htz, htne, hI⟩ := h.lemma44 hA hZ
    obtain ⟨hQ, hfus, hnc⟩ := h'.lemma45 hA htS htz htne hI
    exact ⟨hQ, Or.inr ⟨t, htS, htz, htne, hI, hfus, hnc⟩, hc⟩
  · have : ∃ t ∈ Rm O S K₁ K₂, IsConj z t ∧ t ≠ z := by
      unfold H4A at hA
      push Not at hA
      exact hA
    obtain ⟨t, htR, htz, htne⟩ := this
    obtain ⟨hfus, hQ⟩ := h'.lemma42 ⟨t, htR, h.orderOf_of_isConj htz, htz, htne⟩
    exact ⟨hQ, Or.inl hfus, hc⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
