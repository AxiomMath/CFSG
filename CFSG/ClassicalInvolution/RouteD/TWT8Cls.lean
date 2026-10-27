module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.TWE.B6

set_option linter.unusedSectionVars false

section Class

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem isCompl_pos_neg (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V} (hg2 : g * g = 1) :
    IsCompl (posSpace g) (negSpace g) := by
  have hE : (g : Module.End K V) * (g : Module.End K V) = 1 := by
    ext v
    have := LinearEquiv.congr_fun hg2 v
    simpa using this
  exact isCompl_eigenspace_of_mul_self h2 hE

theorem polar_pos_neg' (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x y : V} (hx : x ∈ posSpace g)
    (hy : y ∈ negSpace g) : polar Q x y = 0 := by
  have hx' : g x = (1 : K) • x := by
    have := Module.End.mem_eigenspace_iff.mp hx
    simpa using this
  have hy' : g y = (-1 : K) • y := by
    have := Module.End.mem_eigenspace_iff.mp hy
    simpa using this
  exact polar_eigen_orth h2 hgO (a := 1) (by norm_num) hx' (by simpa using hy')

theorem finrank_negSpace_eq_two (h2 : (2 : K) ≠ 0) (hdim : Module.finrank K V = 10)
    {w h : V ≃ₗ[K] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hw2 : w * w = 1)
    (hh2 : h * h = 1) (hhd : Module.finrank K (negSpace h) = 2)
    (hhw : negSpace h ≤ posSpace w) (hpos : 6 ≤ Module.finrank K (posSpace w))
    (hneg : 2 ≤ Module.finrank K (negSpace w)) {F₁ F₂ : Submodule K V}
    (hF₁ : Module.finrank K F₁ = 4) (hF₂ : Module.finrank K F₂ = 4)
    (hF₁s : F₁ ≤ posSpace w ∨ F₁ ≤ negSpace w) (hF₂s : F₂ ≤ posSpace w ∨ F₂ ≤ negSpace w)
    (hF₁h : F₁ ≤ posSpace h) (hF₂h : F₂ ≤ posSpace h)
    (hinf : Module.finrank K ↥(F₁ ⊓ F₂) = 2)
    (hnorth : ¬ ∀ x ∈ F₁, ∀ y ∈ F₂, polar Q x y = 0) :
    Module.finrank K (negSpace w) = 2 := by
  have hcw := isCompl_pos_neg h2 hw2
  have hch := isCompl_pos_neg h2 hh2
  have hab := Submodule.finrank_add_eq_of_isCompl hcw
  rw [hdim] at hab
  have hsup : Module.finrank K ↥(F₁ ⊔ F₂) = 6 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq F₁ F₂
    omega
  set U : Submodule K V := posSpace w ⊓ posSpace h with hU
  have hUd : Disjoint U (negSpace h) := by
    refine Disjoint.mono_left inf_le_right ?_
    exact hch.disjoint
  have hUsup : U ⊔ negSpace h ≤ posSpace w := sup_le inf_le_left hhw
  have hUdim : Module.finrank K U + 2 ≤ Module.finrank K (posSpace w) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (negSpace h)
    rw [hUd.eq_bot, finrank_bot] at h1
    have h3 := Submodule.finrank_mono hUsup
    omega
  have hFU : ∀ F : Submodule K V, F ≤ posSpace w → F ≤ posSpace h → F ≤ U :=
    fun F hw hh => le_inf hw hh
  have horth : ∀ x ∈ posSpace w, ∀ y ∈ negSpace w, polar Q x y = 0 := fun x hx y hy =>
    polar_pos_neg' h2 hwO hx hy
  by_contra hne
  have hb : 3 ≤ Module.finrank K (negSpace w) := by omega
  by_cases hb3 : Module.finrank K (negSpace w) = 3
  ·
    have hn1 : ¬ F₁ ≤ negSpace w := fun hle => by
      have := Submodule.finrank_mono hle
      omega
    have hn2 : ¬ F₂ ≤ negSpace w := fun hle => by
      have := Submodule.finrank_mono hle
      omega
    have h1 : F₁ ≤ U := hFU F₁ (hF₁s.resolve_right hn1) hF₁h
    have h2' : F₂ ≤ U := hFU F₂ (hF₂s.resolve_right hn2) hF₂h
    have := Submodule.finrank_mono (sup_le h1 h2')
    omega
  · have hb4 : Module.finrank K (negSpace w) = 4 := by omega
    have hUle : Module.finrank K U ≤ 4 := by omega
    have key : ∀ F : Submodule K V, Module.finrank K F = 4 → (F ≤ posSpace w ∨ F ≤ negSpace w) →
        F ≤ posSpace h → (F = U ∧ F ≤ posSpace w) ∨ (F = negSpace w ∧ F ≤ negSpace w) := by
      intro F hF hs hFh
      rcases hs with hs | hs
      · left
        refine ⟨(Submodule.eq_of_le_of_finrank_le (hFU F hs hFh) (by omega)), hs⟩
      · right
        exact ⟨Submodule.eq_of_le_of_finrank_le hs (by omega), hs⟩
    rcases key F₁ hF₁ hF₁s hF₁h with ⟨e1, p1⟩ | ⟨e1, n1⟩ <;>
      rcases key F₂ hF₂ hF₂s hF₂h with ⟨e2, p2⟩ | ⟨e2, n2⟩
    · rw [e1, e2, inf_idem] at hinf
      have : Module.finrank K U = 4 := by rw [← e1]; exact hF₁
      omega
    · exact hnorth fun x hx y hy => horth x (p1 hx) y (n2 hy)
    · exact hnorth fun x hx y hy => by
        rw [polar_comm]
        exact horth y (p2 hy) x (n1 hx)
    · rw [e1, e2, inf_idem] at hinf
      have : Module.finrank K (negSpace w) = 4 := hb4
      omega

end Class

end CFSG.ClassicalInvolution.RouteD.TWT8
