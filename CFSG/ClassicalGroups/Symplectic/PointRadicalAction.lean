module

public import CFSG.ClassicalGroups.Symplectic.PointRadicalNormal

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open CFSG.ClassicalGroups.Alternating
open Matrix

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mem_LspGL_siegel {u w : Fin m ⊕ Fin m → K} (hw : spForm m K u w = 0) (c : K) :
    ∃ A ∈ LspGL m K u, ∀ x : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
        x + spForm m K x u • w + spForm m K x w • u + (c * spForm m K x u) • u := by
  let g : Gsp (spForm m K) := Ssp spForm_isAlt u w c
  have hg : g ∈ Lsp (spForm m K) spForm_isAlt u := Ssp_mem_Lsp spForm_isAlt hw c
  let A : StatedSp m K := (spEquiv (m := m) (K := K)).symm g
  refine ⟨(A : GL (Fin m ⊕ Fin m) K), mem_LspGL_iff.mpr ⟨A.2, ?_⟩, fun x => ?_⟩
  · have : spEquiv (m := m) (K := K) ⟨(A : GL (Fin m ⊕ Fin m) K), A.2⟩ = g :=
      (spEquiv (m := m) (K := K)).apply_symm_apply g
    rw [this]
    exact hg
  · have h1 := spEquiv_app A x
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    exact siegel_apply spForm_isAlt hw c x

private theorem mem_span_of_forall_perp {u w : Fin m ⊕ Fin m → K}
    (h : ∀ x, spForm m K x u = 0 → spForm m K x w = 0) : w ∈ Submodule.span K {u} := by
  have := mem_span_of_forall_orthogonal (B := spForm m K) spForm_nondegenerate (ι := Unit)
    (fun _ => u) w (fun y hy => ?_)
  · simpa using this
  · have h1 : spForm m K y u = 0 := by
      have h0 := spForm_isAlt.neg_eq y u
      rw [hy ()] at h0
      exact neg_eq_zero.mp h0
    have h2 := h y h1
    have h3 := spForm_isAlt.neg_eq w y
    rw [h2] at h3
    exact neg_eq_zero.mp h3

theorem mem_span_of_forall_LspGL_apply_eq {u x : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    (h : ∀ g ∈ LspGL m K u, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = x) :
    x ∈ Submodule.span K {u} := by
  have hxu : spForm m K x u = 0 := by
    obtain ⟨A, hA, hAx⟩ := exists_mem_LspGL_siegel (u := u) (w := 0) (by simp) (1 : K)
    have h1 := h A hA
    rw [hAx x] at h1
    have h2 : spForm m K x u • u = 0 := by simpa using h1
    exact (smul_eq_zero.mp h2).resolve_right hu
  refine mem_span_of_forall_perp (fun z hz => ?_)
  have hzu : spForm m K u z = 0 := by
    have h0 := spForm_isAlt.neg_eq u z
    rw [hz] at h0
    exact neg_eq_zero.mp h0
  obtain ⟨A, hA, hAx⟩ := exists_mem_LspGL_siegel (u := u) (w := z) hzu 0
  have h1 := h A hA
  rw [hAx x, hxu] at h1
  have h2 : spForm m K x z • u = 0 := by simpa using h1
  have h3 : spForm m K x z = 0 := (smul_eq_zero.mp h2).resolve_right hu
  have h4 := spForm_isAlt.neg_eq z x
  rw [h3] at h4
  exact neg_eq_zero.mp h4

private theorem exists_orth_not_mem_span (hm : 2 ≤ m) {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) :
    ∃ w, spForm m K u w = 0 ∧ w ∉ Submodule.span K {u} := by
  by_contra hcon
  push Not at hcon
  have hker : LinearMap.ker (spForm m K u) ≤ Submodule.span K {u} := fun w hw =>
    hcon w (LinearMap.mem_ker.mp hw)
  have h1 := LinearMap.finrank_range_add_finrank_ker (spForm m K u)
  have h2 : Module.finrank K (LinearMap.range (spForm m K u)) ≤ 1 := by
    calc _ ≤ Module.finrank K K := Submodule.finrank_le _
      _ = 1 := Module.finrank_self K
  have h3 : Module.finrank K (LinearMap.ker (spForm m K u)) ≤ 1 := by
    calc _ ≤ Module.finrank K (Submodule.span K {u}) := Submodule.finrank_mono hker
      _ = 1 := finrank_span_singleton hu
  rw [finrank_spSpace] at h1
  omega

theorem exists_mem_LspGL_apply_sub_smul (hm : 2 ≤ m) {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) :
    ∃ s ∈ LspGL m K u, ∃ x : Fin m ⊕ Fin m → K, spForm m K x u = 0 ∧ ∃ l : K, l ≠ 0 ∧
      (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = x + l • u := by
  obtain ⟨w, hw, hwu⟩ := exists_orth_not_mem_span hm hu
  obtain ⟨A, hA, hAx⟩ := exists_mem_LspGL_siegel hw (0 : K)
  have hex : ∃ x, spForm m K x u = 0 ∧ spForm m K x w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hwu (mem_span_of_forall_perp hcon)
  obtain ⟨x, hxu, hxw⟩ := hex
  refine ⟨A, hA, x, hxu, spForm m K x w, hxw, ?_⟩
  rw [hAx x, hxu]
  simp

theorem spForm_eq_zero_of_forall_LspGL_apply_sub_mem (hm : 2 ≤ m) {u x : Fin m ⊕ Fin m → K}
    (hu : u ≠ 0)
    (h : ∀ g ∈ LspGL m K u, ∃ c : K,
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = x + c • u) :
    spForm m K x u = 0 := by
  by_contra hxu
  obtain ⟨w, hw, hwu⟩ := exists_orth_not_mem_span hm hu
  obtain ⟨A, hA, hAx⟩ := exists_mem_LspGL_siegel hw (0 : K)
  obtain ⟨c, hc⟩ := h A hA
  rw [hAx x] at hc
  have hc' : x + (spForm m K x u • w + spForm m K x w • u) = x + c • u := by
    rw [← add_assoc]
    simpa using hc
  have h2 : spForm m K x u • w + spForm m K x w • u = c • u := add_left_cancel hc'
  have h1 : spForm m K x u • w = (c - spForm m K x w) • u := by
    rw [sub_smul]
    exact eq_sub_of_add_eq h2
  apply hwu
  have : w = (spForm m K x u)⁻¹ • ((c - spForm m K x w) • u) := by
    rw [← h1, smul_smul, inv_mul_cancel₀ hxu, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))

end CFSG.ClassicalGroups.Symplectic
