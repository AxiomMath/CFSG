module

public import CFSG.LinearAlgebra.RootGroupSL.ModelBasic

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

@[simp] private theorem diagE_apply (s : Eˣ) (v : VJ) (w : V₀) :
    diagE (k := k) s (v, w) = ((s : E) • v, w) := rfl

@[simp] private theorem diagE_inv_apply (s : Eˣ) (v : VJ) (w : V₀) :
    (diagE (k := k) s)⁻¹ (v, w) = (((s⁻¹ : Eˣ) : E) • v, w) := rfl

@[simp] private theorem diagE_fst (s : Eˣ) (p : VJ × V₀) :
    (diagE (k := k) s p).1 = (s : E) • p.1 := by
  obtain ⟨v, w⟩ := p
  rw [diagE_apply]

@[simp] private theorem diagY_apply (y : V₀ ≃ₗ[k] V₀) (v : VJ) (w : V₀) :
    diagY y (v, w) = (v, y w) := by
  rw [diagY, LinearEquiv.prodCongr_apply]
  rfl

@[simp] private theorem diagY_inv_apply (y : V₀ ≃ₗ[k] V₀) (v : VJ) (w : V₀) :
    (diagY y)⁻¹ (v, w) = (v, y.symm w) := by
  change (diagY y).symm (v, w) = (v, y.symm w)
  rw [diagY, LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
  rfl

@[simp] private theorem diagY_fst (y : V₀ ≃ₗ[k] V₀) (p : VJ × V₀) :
    (diagY y p).1 = p.1 := by
  obtain ⟨v, w⟩ := p
  rw [diagY_apply]

@[simp] private theorem restrictSL_apply (B : SpecialLinearGroup E VJ) (v : VJ) :
    (restrictSL (E := E) (VJ := VJ) k B : VJ ≃ₗ[k] VJ) v = (B : VJ ≃ₗ[E] VJ) v := by
  rw [show (restrictSL (E := E) (VJ := VJ) k B : VJ ≃ₗ[k] VJ) =
      (B : VJ ≃ₗ[E] VJ).restrictScalars k from rfl]
  exact LinearMap.restrictScalars_apply k (B : VJ →ₗ[E] VJ) v

private theorem det_conj_eq_one (z : (VJ × V₀) ≃ₗ[k] (VJ × V₀))
    (g : SpecialLinearGroup k (VJ × V₀)) :
    LinearEquiv.det (z * SpecialLinearGroup.toLinearEquiv g * z⁻¹) = 1 := by
  have hg : LinearEquiv.det (SpecialLinearGroup.toLinearEquiv g) = 1 := g.prop
  simp only [map_mul, map_inv, hg, mul_one, mul_inv_cancel]

private def conjSL (z : (VJ × V₀) ≃ₗ[k] (VJ × V₀))
    (g : SpecialLinearGroup k (VJ × V₀)) : SpecialLinearGroup k (VJ × V₀) :=
  ⟨z * SpecialLinearGroup.toLinearEquiv g * z⁻¹, det_conj_eq_one z g⟩

private theorem conjSL_apply (z : (VJ × V₀) ≃ₗ[k] (VJ × V₀))
    (g : SpecialLinearGroup k (VJ × V₀)) (p : VJ × V₀) :
    conjSL z g p = z (g (z⁻¹ p)) := by
  simp only [conjSL, SpecialLinearGroup.coe_mk, LinearEquiv.mul_apply]
  rfl

private theorem apply_add (g : SpecialLinearGroup k (VJ × V₀)) (v : VJ) (w : V₀) :
    SpecialLinearGroup.toLinearEquiv g (v, w) =
      SpecialLinearGroup.toLinearEquiv g (v, 0) +
        SpecialLinearGroup.toLinearEquiv g (0, w) := by
  have h : (v, w) = (v, (0 : V₀)) + ((0 : VJ), w) := by simp
  rw [h]
  exact map_add (SpecialLinearGroup.toLinearEquiv g) (v, (0 : V₀)) ((0 : VJ), w)

private theorem modelK1_apply (g : SpecialLinearGroup k (VJ × V₀))
    (hg : g ∈ modelK1 k VJ V₀) (v : VJ) (w : V₀) :
    SpecialLinearGroup.toLinearEquiv g (v, w) =
      ((SpecialLinearGroup.toLinearEquiv g (v, 0)).1, w) := by
  rw [apply_add g v w]
  have h1 : SpecialLinearGroup.toLinearEquiv g (v, 0) =
      ((SpecialLinearGroup.toLinearEquiv g (v, 0)).1, (0 : V₀)) :=
    Prod.ext rfl (hg.1 v)
  have h2 : SpecialLinearGroup.toLinearEquiv g (0, w) = ((0 : VJ), w) := hg.2 w
  rw [h1, h2]
  simp

private theorem diagE_smul_inv (s : Eˣ) (v : VJ) :
    (s : E) • (((s⁻¹ : Eˣ) : E) • v) = v := by
  rw [smul_smul]
  have h : (s : E) * ((s⁻¹ : Eˣ) : E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [h, one_smul]

theorem diagE_conj_mem_modelK1 (s : Eˣ) {g : SpecialLinearGroup k (VJ × V₀)}
    (hg : g ∈ modelK1 k VJ V₀) :
    ∃ g' ∈ modelK1 k VJ V₀, SpecialLinearGroup.toLinearEquiv g' =
      diagE s * SpecialLinearGroup.toLinearEquiv g * (diagE s)⁻¹ := by
  refine ⟨conjSL (diagE s) g, ?_, rfl⟩
  constructor
  · intro v
    rw [conjSL_apply]
    have h0 : (diagE (k := k) s)⁻¹ (v, 0) =
        (((s⁻¹ : Eˣ) : E) • v, (0 : V₀)) := diagE_inv_apply s v 0
    rw [h0]
    have hx : g ((((s⁻¹ : Eˣ) : E) • v), (0 : V₀)) =
        ((g ((((s⁻¹ : Eˣ) : E) • v), (0 : V₀))).1, (0 : V₀)) :=
      Prod.ext rfl (hg.1 _)
    rw [hx]
    simp
  · intro w
    rw [conjSL_apply]
    have h0 : (diagE (k := k) s)⁻¹ ((0 : VJ), w) = ((0 : VJ), w) := by
      change ((((s⁻¹ : Eˣ) : E) • (0 : VJ), w) = ((0 : VJ), w))
      rw [smul_zero]
    rw [h0, hg.2 w]
    simp

theorem diagE_conj_mem_modelA1 (s : Eˣ) {g : SpecialLinearGroup k (VJ × V₀)}
    (hg : g ∈ modelA1 k VJ V₀) :
    ∃ g' ∈ modelA1 k VJ V₀, SpecialLinearGroup.toLinearEquiv g' =
      diagE s * SpecialLinearGroup.toLinearEquiv g * (diagE s)⁻¹ := by
  refine ⟨conjSL (diagE s) g, ?_, rfl⟩
  constructor
  · intro v
    rw [conjSL_apply]
    have hgv : g ((diagE (k := k) s)⁻¹ (v, 0)) = (diagE (k := k) s)⁻¹ (v, 0) := by
      rw [diagE_inv_apply]
      exact hg.1 _
    rw [hgv]
    exact LinearEquiv.apply_symm_apply (diagE (k := k) s) (v, 0)
  · intro w
    rw [conjSL_apply]
    have h0 : (diagE (k := k) s)⁻¹ ((0 : VJ), w) = ((0 : VJ), w) := by
      change ((((s⁻¹ : Eˣ) : E) • (0 : VJ), w) = ((0 : VJ), w))
      rw [smul_zero]
    rw [h0]
    have hg0 : g (0, w) = ((g (0, w)).1, w) := Prod.ext rfl (hg.2 w)
    rw [hg0]
    simp

theorem diagE_conj_mem_modelA2 (s : Eˣ) {g : SpecialLinearGroup k (VJ × V₀)}
    (hg : g ∈ modelA2 k VJ V₀) :
    ∃ g' ∈ modelA2 k VJ V₀, SpecialLinearGroup.toLinearEquiv g' =
      diagE s * SpecialLinearGroup.toLinearEquiv g * (diagE s)⁻¹ := by
  refine ⟨conjSL (diagE s) g, ?_, rfl⟩
  constructor
  · intro w
    rw [conjSL_apply]
    have h0 : (diagE (k := k) s)⁻¹ ((0 : VJ), w) = ((0 : VJ), w) := by
      change ((((s⁻¹ : Eˣ) : E) • (0 : VJ), w) = ((0 : VJ), w))
      rw [smul_zero]
    rw [h0, hg.1 w]
    simp
  · intro v
    rw [conjSL_apply]
    have h0 : (diagE (k := k) s)⁻¹ (v, 0) =
        (((s⁻¹ : Eˣ) : E) • v, (0 : V₀)) := diagE_inv_apply s v 0
    rw [h0]
    rw [diagE_fst]
    rw [hg.2 _]
    exact diagE_smul_inv s v

private theorem blockSLE_apply (B : SpecialLinearGroup E VJ) (v : VJ) (w : V₀) :
    SpecialLinearGroup.toLinearEquiv (blockSLE (E := E) k V₀ B) (v, w) =
      ((B : VJ ≃ₗ[E] VJ) v, w) := by
  have h : SpecialLinearGroup.toLinearEquiv
      (blockSLk (VJ := VJ) k V₀ (restrictSL (E := E) (VJ := VJ) k B)) (v, w) =
      ((restrictSL (E := E) (VJ := VJ) k B : VJ ≃ₗ[k] VJ) v, w) := by
    simpa using blockSLk_apply (k := k) (V₀ := V₀)
      (restrictSL (E := E) (VJ := VJ) k B) v w
  simpa [blockSLE] using h

theorem diagE_comm_modelJ (s : Eˣ) {g : SpecialLinearGroup k (VJ × V₀)}
    (hg : g ∈ modelJ k E VJ V₀) :
    diagE s * SpecialLinearGroup.toLinearEquiv g =
      SpecialLinearGroup.toLinearEquiv g * diagE s := by
  obtain ⟨B, rfl⟩ := hg
  apply LinearEquiv.ext
  intro p
  obtain ⟨v, w⟩ := p
  simp only [LinearEquiv.mul_apply, blockSLE_apply, diagE_apply, map_smul]

theorem diagY_conj_mem_modelA1 (y : V₀ ≃ₗ[k] V₀) {g : SpecialLinearGroup k (VJ × V₀)}
    (hg : g ∈ modelA1 k VJ V₀) :
    ∃ g' ∈ modelA1 k VJ V₀, SpecialLinearGroup.toLinearEquiv g' =
      diagY y * SpecialLinearGroup.toLinearEquiv g * (diagY y)⁻¹ := by
  refine ⟨conjSL (diagY y) g, ?_, rfl⟩
  constructor
  · intro v
    rw [conjSL_apply]
    have h0 : (diagY y)⁻¹ (v, 0) = (v, 0) := by
      rw [diagY_inv_apply, map_zero]
    rw [h0, hg.1 v]
    simp
  · intro w
    rw [conjSL_apply]
    have h0 : (diagY y)⁻¹ ((0 : VJ), w) = ((0 : VJ), y.symm w) :=
      diagY_inv_apply y (0 : VJ) w
    rw [h0]
    have hx : g (0, y.symm w) = ((g (0, y.symm w)).1, y.symm w) :=
      Prod.ext rfl (hg.2 (y.symm w))
    rw [hx]
    simp

theorem diagY_conj_mem_modelA2 (y : V₀ ≃ₗ[k] V₀) {g : SpecialLinearGroup k (VJ × V₀)}
    (hg : g ∈ modelA2 k VJ V₀) :
    ∃ g' ∈ modelA2 k VJ V₀, SpecialLinearGroup.toLinearEquiv g' =
      diagY y * SpecialLinearGroup.toLinearEquiv g * (diagY y)⁻¹ := by
  refine ⟨conjSL (diagY y) g, ?_, rfl⟩
  constructor
  · intro w
    rw [conjSL_apply]
    have h0 : (diagY y)⁻¹ ((0 : VJ), w) = ((0 : VJ), y.symm w) :=
      diagY_inv_apply y (0 : VJ) w
    rw [h0, hg.1 (y.symm w)]
    simp
  · intro v
    rw [conjSL_apply]
    have h0 : (diagY y)⁻¹ (v, 0) = (v, 0) := by
      rw [diagY_inv_apply, map_zero]
    rw [h0]
    rw [diagY_fst]
    exact hg.2 v

theorem diagY_comm_modelK1 (y : V₀ ≃ₗ[k] V₀) {g : SpecialLinearGroup k (VJ × V₀)}
    (hg : g ∈ modelK1 k VJ V₀) :
    diagY y * SpecialLinearGroup.toLinearEquiv g =
      SpecialLinearGroup.toLinearEquiv g * diagY y := by
  apply LinearEquiv.ext
  intro p
  obtain ⟨v, w⟩ := p
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [modelK1_apply g hg v w]
  rw [show diagY y (v, w) = (v, y w) from diagY_apply y v w]
  rw [modelK1_apply g hg v (y w)]
  simp [diagY_apply]

end CFSG.LinearAlgebra.RootGroupSL
