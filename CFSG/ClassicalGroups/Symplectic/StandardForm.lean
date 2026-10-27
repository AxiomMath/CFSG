module

public import CFSG.ClassicalGroups.Alternating.PointRadicalFixed
public import CFSG.Open.StatedAPI

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Alternating
open Matrix
open LinearMap (BilinForm)

section Form

variable (m : ℕ) (K : Type*) [Field K]

@[expose] def spJ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := fromBlocks 0 1 (-1) 0

@[expose] noncomputable def spForm : BilinForm K (Fin m ⊕ Fin m → K) := Matrix.toBilin' (spJ m K)

variable {m K}

theorem spForm_apply (x y : Fin m ⊕ Fin m → K) : spForm m K x y = x ⬝ᵥ (spJ m K *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

theorem spJ_mulVec_inl (v : Fin m ⊕ Fin m → K) (i : Fin m) :
    (spJ m K *ᵥ v) (Sum.inl i) = v (Sum.inr i) := by
  simp [spJ, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

theorem spJ_mulVec_inr (v : Fin m ⊕ Fin m → K) (i : Fin m) :
    (spJ m K *ᵥ v) (Sum.inr i) = -v (Sum.inl i) := by
  simp [spJ, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

theorem spForm_self (x : Fin m ⊕ Fin m → K) : spForm m K x x = 0 := by
  rw [spForm_apply]
  simp only [dotProduct, Fintype.sum_sum_type, spJ_mulVec_inl, spJ_mulVec_inr, mul_neg,
    Finset.sum_neg_distrib]
  rw [add_neg_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem spForm_isAlt : (spForm m K).IsAlt := spForm_self

theorem spForm_single_inl_inr (i j : Fin m) :
    spForm m K (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) = if i = j then 1 else 0 := by
  rw [spForm_apply]
  simp [spJ, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, Pi.single_apply]

theorem spJ_mul_spJ : spJ m K * spJ m K = -1 := by
  have h : (-1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      fromBlocks (-1) 0 0 (-1) := by
    rw [← fromBlocks_one, fromBlocks_neg]
    simp
  rw [h, spJ, fromBlocks_multiply]
  simp

theorem spJ_det_ne_zero : (spJ m K).det ≠ 0 := by
  have h : IsUnit (spJ m K).det := by
    refine Matrix.isUnit_det_of_right_inverse (B := -spJ m K) ?_
    rw [Matrix.mul_neg, spJ_mul_spJ, neg_neg]
  exact h.ne_zero

theorem spForm_nondegenerate : (spForm m K).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr spJ_det_ne_zero

theorem finrank_spSpace : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

end Form

section Equiv

variable {m : ℕ} {K : Type} [Field K]

theorem mem_statedSp_iff_forall (A : GL (Fin m ⊕ Fin m) K) :
    A ∈ StatedSp m K ↔ ∀ x y : Fin m ⊕ Fin m → K,
      spForm m K ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = spForm m K x y := by
  rw [mem_statedSp_iff]
  have hcomp := Matrix.toBilin'_comp (spJ m K) (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = spJ m K := rfl
  rw [hJ]
  constructor
  · intro h x y
    have := congrArg (fun F => F x y) hcomp
    simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply', h] at this
    exact this.trans (by rw [← hJ, ← spJ]; rfl)
  · intro h
    apply (Matrix.toBilin' (R₁ := K)).injective
    rw [← hcomp]
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply']
    exact h x y

theorem map_toLin_statedSp :
    (StatedSp m K).map (Matrix.GeneralLinearGroup.toLin :
      GL (Fin m ⊕ Fin m) K ≃* LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)).toMonoidHom =
        bilinIsometryGroup (spForm m K) := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_statedSp_iff_forall, mem_bilinIsometryGroup]
  have hg : ∀ x : Fin m ⊕ Fin m → K,
      ((g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
        (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) x =
        ((Matrix.GeneralLinearGroup.toLin.symm g : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x := by
    intro x
    have := Matrix.GeneralLinearGroup.toLin_apply
      (Matrix.GeneralLinearGroup.toLin.symm g : GL (Fin m ⊕ Fin m) K) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  simp only [hg]

@[expose] noncomputable def spEquiv : StatedSp m K ≃* Gsp (spForm m K) :=
  ((Matrix.GeneralLinearGroup.toLin :
      GL (Fin m ⊕ Fin m) K ≃* LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)).subgroupMap
    (StatedSp m K)).trans (MulEquiv.subgroupCongr map_toLin_statedSp)

theorem spEquiv_app (A : StatedSp m K) (v : Fin m ⊕ Fin m → K) :
    (spEquiv A).app v =
      ((A : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v :=
  rfl

@[expose] noncomputable def LspGL (m : ℕ) (K : Type) [Field K] (u : Fin m ⊕ Fin m → K) :
    Subgroup (GL (Fin m ⊕ Fin m) K) :=
  ((Lsp (spForm m K) spForm_isAlt u).comap (spEquiv (m := m) (K := K)).toMonoidHom).map
    (StatedSp m K).subtype

theorem LspGL_le_statedSp (u : Fin m ⊕ Fin m → K) : LspGL m K u ≤ StatedSp m K := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_LspGL_iff {u : Fin m ⊕ Fin m → K} {A : GL (Fin m ⊕ Fin m) K} :
    A ∈ LspGL m K u ↔
      ∃ hA : A ∈ StatedSp m K, spEquiv ⟨A, hA⟩ ∈ Lsp (spForm m K) spForm_isAlt u := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hA, h⟩
    exact ⟨⟨A, hA⟩, h, rfl⟩

theorem mem_LspGL_iff_siegel {u : Fin m ⊕ Fin m → K} {A : GL (Fin m ⊕ Fin m) K} :
    A ∈ LspGL m K u ↔ A ∈ StatedSp m K ∧ ∃ (w : Fin m ⊕ Fin m → K) (c : K),
      spForm m K u w = 0 ∧ ∀ x : Fin m ⊕ Fin m → K,
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
          x + spForm m K x u • w + spForm m K x w • u + (c * spForm m K x u) • u := by
  rw [mem_LspGL_iff]
  constructor
  · rintro ⟨hA, w, c, hw, hg⟩
    refine ⟨hA, w, c, hw, fun x => ?_⟩
    have h1 : ((siegel (spForm m K) spForm_isAlt u w c :
        LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
          (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) x =
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x := by
      rw [hg]
      exact spEquiv_app ⟨A, hA⟩ x
    rw [← h1, siegel_apply spForm_isAlt hw c x]
  · rintro ⟨hA, w, c, hw, h⟩
    refine ⟨hA, w, c, hw, ?_⟩
    refine Units.ext (LinearMap.ext fun x => ?_)
    rw [siegel_apply spForm_isAlt hw c x]
    exact (h x).symm

end Equiv

section Transitive

variable {V : Type*} [AddCommGroup V]

theorem exists_gsp_apply_eq_of_form_ne_zero {K : Type*} [Field K] [Module K V] {B : BilinForm K V}
    (hB : B.IsAlt) {x y : V} (h : B x y ≠ 0) : ∃ g : Gsp B, g.app x = y := by
  have h1 : B x (y - x) = B x y := by rw [map_sub, hB.self_eq_zero, sub_zero]
  have h2 : B y (y - x) = B x y := by
    rw [map_sub, hB.self_eq_zero, zero_sub, hB.neg_eq]
  obtain ⟨s, hs, hsx⟩ := exists_mem_pointRadical_apply_eq hB (v := y - x) (u := x) (u' := y)
    (by rw [h1, h2]) (by rw [h1]; exact h)
  exact ⟨⟨s, pointRadical_le_bilinIsometryGroup hB _ hs⟩, hsx⟩

theorem exists_gsp_apply_eq {K : Type*} [Field K] [Module K V] {B : BilinForm K V}
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : Gsp B, g.app x = y := by
  by_cases hxy : B x y = 0
  · obtain ⟨a, ha⟩ : ∃ a, B x a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (hBn.1 x hcon)
    obtain ⟨b, hb⟩ : ∃ b, B b y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hy (hBn.2 y hcon)
    obtain ⟨z, hz1, hz2⟩ : ∃ z, B x z ≠ 0 ∧ B z y ≠ 0 := by
      by_cases hay : B a y = 0
      · by_cases hxb : B x b = 0
        · refine ⟨a + b, ?_, ?_⟩
          · rw [map_add, hxb, add_zero]; exact ha
          · rw [map_add, LinearMap.add_apply, hay, zero_add]; exact hb
        · exact ⟨b, hxb, hb⟩
      · exact ⟨a, ha, hay⟩
    obtain ⟨g₁, hg₁⟩ := exists_gsp_apply_eq_of_form_ne_zero hB hz1
    obtain ⟨g₂, hg₂⟩ := exists_gsp_apply_eq_of_form_ne_zero hB hz2
    exact ⟨g₂ * g₁, by rw [Gsp.app_mul, hg₁, hg₂]⟩
  · exact exists_gsp_apply_eq_of_form_ne_zero hB hxy

end Transitive

section StatedTransitive

variable {m : ℕ} {K : Type} [Field K]

theorem exists_statedSp_mulVec_eq {x y : Fin m ⊕ Fin m → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A ∈ StatedSp m K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = y := by
  obtain ⟨g, hg⟩ := exists_gsp_apply_eq spForm_isAlt spForm_nondegenerate hx hy
  refine ⟨((spEquiv (m := m) (K := K)).symm g : GL (Fin m ⊕ Fin m) K),
    ((spEquiv (m := m) (K := K)).symm g).2, ?_⟩
  have := spEquiv_app ((spEquiv (m := m) (K := K)).symm g) x
  rw [MulEquiv.apply_symm_apply] at this
  rw [← this]
  exact hg

end StatedTransitive

end CFSG.ClassicalGroups.Symplectic
