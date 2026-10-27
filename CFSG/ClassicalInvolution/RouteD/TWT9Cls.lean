module

public import CFSG.ClassicalInvolution.RouteD.TWT8Cls
public import CFSG.ClassicalInvolution.RouteD.TWEB4V

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.RouteD.TWT8 (isCompl_pos_neg)
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (mem_negSpace_iff' mem_posSpace_iff'
  eq_self_of_perp_plane)

set_option linter.unusedSectionVars false

section Class

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_normalized {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg2 : g * g = 1) {ε : K} (hε : ε = 1 ∨ ε = -1) :
    ∃ g' : V ≃ₗ[K] V, g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g' * g' = 1 ∧
      ∀ x, g' x = ε • g x := by
  rcases hε with rfl | rfl
  · exact ⟨g, hgO, hg2, fun x => by simp⟩
  · let g' : V ≃ₗ[K] V := g.trans (LinearEquiv.neg K)
    have hg'x : ∀ x, g' x = -(g x) := fun x => rfl
    refine ⟨g', ?_, ?_, fun x => by rw [hg'x]; simp⟩
    · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
      rw [hg'x, QuadraticMap.map_neg]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO x
    · refine LinearEquiv.ext fun x => ?_
      have := LinearEquiv.congr_fun hg2 x
      simp only [LinearEquiv.mul_apply, hg'x, map_neg, neg_neg] at this ⊢
      simpa using this

theorem negSpace_eq_plane_td4a (h2 : (2 : K) ≠ 0) (hd : Module.finrank K V = 8)
    {g h : V ≃ₗ[K] V} (hg2 : g * g = 1) (hh2 : h * h = 1) {W : Submodule K V}
    (hW : Module.finrank K W = 4) (hgW : ∀ x ∈ W, g x = x) (hhneg : negSpace h ≤ W)
    (hhdim : Module.finrank K (negSpace h) = 2) (π ρ : HypPair Q)
    (hgπ : ∀ x ∈ hypPlane π, g x = -x) (hgρ : ∀ x ∈ hypPlane ρ, g x = x)
    (hρh : ∀ x ∈ hypPlane ρ, h x = x) {F : Submodule K V} (hF : Module.finrank K F = 4)
    {εF : K} (hεF : εF = 1 ∨ εF = -1) (hgF : ∀ x ∈ F, g x = εF • x)
    (hFh : ∀ x ∈ F, h x = x) (haniso : ∀ y ∈ W, h y = y → y ≠ 0 → Q y ≠ 0) :
    negSpace g = hypPlane π := by
  classical
  have hcg := isCompl_pos_neg h2 hg2
  have hch := isCompl_pos_neg h2 hh2
  have hab := Submodule.finrank_add_eq_of_isCompl hcg
  rw [hd] at hab
  have hπle : hypPlane π ≤ negSpace g := fun x hx => mem_negSpace_iff'.mpr (hgπ x hx)
  have hWle : W ≤ posSpace g := fun x hx => mem_posSpace_iff'.mpr (hgW x hx)
  have hρle : hypPlane ρ ≤ posSpace g := fun x hx => mem_posSpace_iff'.mpr (hgρ x hx)
  have hneg2 : 2 ≤ Module.finrank K (negSpace g) := by
    have := Submodule.finrank_mono hπle
    rw [finrank_hypPlane] at this
    exact this
  have hpos4 : 4 ≤ Module.finrank K (posSpace g) := by
    have := Submodule.finrank_mono hWle
    omega
  set U : Submodule K V := posSpace g ⊓ posSpace h with hU
  have hUd : Disjoint U (negSpace h) := Disjoint.mono_left inf_le_right hch.disjoint
  have hUsup : U ⊔ negSpace h ≤ posSpace g := sup_le inf_le_left (hhneg.trans hWle)
  have hUdim : Module.finrank K U + 2 ≤ Module.finrank K (posSpace g) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (negSpace h)
    rw [hUd.eq_bot, finrank_bot] at h1
    have h3 := Submodule.finrank_mono hUsup
    omega
  rcases hεF with rfl | rfl
  · have hFU : F ≤ U := le_inf (fun x hx => mem_posSpace_iff'.mpr (by simpa using hgF x hx))
      (fun x hx => mem_posSpace_iff'.mpr (hFh x hx))
    have h4 := Submodule.finrank_mono hFU
    exact (Submodule.eq_of_le_of_finrank_eq hπle (by rw [finrank_hypPlane]; omega)).symm
  · have hFn : F ≤ negSpace g := fun x hx => mem_negSpace_iff'.mpr (by simpa using hgF x hx)
    have h4 := Submodule.finrank_mono hFn
    have hposeq : W = posSpace g := Submodule.eq_of_le_of_finrank_le hWle (by omega)
    exfalso
    have hρW : hypPlane ρ ≤ W := hposeq ▸ hρle
    exact haniso ρ.e (hρW (e_mem_hypPlane ρ)) (hρh _ (e_mem_hypPlane ρ)) ρ.e_ne_zero ρ.Q_e

theorem eq_smul_of_perp_td4a (h2 : (2 : K) ≠ 0) (hd : Module.finrank K V = 8)
    {g h : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hh2 : h * h = 1) {W : Submodule K V} (hW : Module.finrank K W = 4) {ε : K}
    (hε : ε = 1 ∨ ε = -1) (hgW : ∀ x ∈ W, g x = ε • x) (hhneg : negSpace h ≤ W)
    (hhdim : Module.finrank K (negSpace h) = 2) (π ρ : HypPair Q)
    (hgπ : ∀ x ∈ hypPlane π, g x = (-ε) • x) (hgρ : ∀ x ∈ hypPlane ρ, g x = ε • x)
    (hρh : ∀ x ∈ hypPlane ρ, h x = x) {F : Submodule K V} (hF : Module.finrank K F = 4)
    {εF : K} (hεF : εF = 1 ∨ εF = -1) (hgF : ∀ x ∈ F, g x = εF • x)
    (hFh : ∀ x ∈ F, h x = x) (haniso : ∀ y ∈ W, h y = y → y ≠ 0 → Q y ≠ 0) :
    ∀ y, y ∈ π.perp → g y = ε • y := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  obtain ⟨g', hg'O, hg'2, hg'x⟩ := exists_normalized hgO hg2 hε
  have hneg := negSpace_eq_plane_td4a h2 hd hg'2 hh2 hW
    (fun x hx => by rw [hg'x, hgW x hx, smul_smul, hεε, one_smul]) hhneg hhdim π ρ
    (fun x hx => by rw [hg'x, hgπ x hx, smul_smul, mul_neg, hεε, neg_one_smul])
    (fun x hx => by rw [hg'x, hgρ x hx, smul_smul, hεε, one_smul]) hρh hF
    (εF := ε * εF) (by rcases hε with rfl | rfl <;> rcases hεF with rfl | rfl <;> simp)
    (fun x hx => by rw [hg'x, hgF x hx, smul_smul]) hFh haniso
  intro y hy
  have h1 : g' y = y := eq_self_of_perp_plane h2 hg'O hg'2 π hneg hy
  rw [hg'x] at h1
  have := congrArg (fun v => ε • v) h1
  simpa [smul_smul, hεε] using this

end Class

end CFSG.ClassicalInvolution.RouteD.TWT9
