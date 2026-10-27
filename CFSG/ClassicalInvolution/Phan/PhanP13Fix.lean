module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Isometry

public section

namespace CFSG.ClassicalInvolution.PhanP

open QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin

variable {F : Type} [Field F] [Invertible (2 : F)] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {W : Submodule F V}

@[expose] noncomputable def decompOrth (hW : (Q.restrict W).Nondegenerate) :
    ((Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W)).prod
      (Q.restrict W)).IsometryEquiv Q where
  toLinearEquiv := (LinearMap.BilinForm.orthogonal Q.polarBilin W).prodEquivOfIsCompl W
    hW.isCompl_orthogonal.symm
  map_app' x := by
    change Q ((x.1 : V) + x.2) = Q x.1 + Q x.2
    have h := (QuadraticMap.isOrtho_polarBilin.mp (x.1.2 x.2 x.2.2)).polar_eq_zero
    rw [QuadraticMap.map_add Q, QuadraticMap.polar_comm, h, add_zero]

theorem decompOrth_apply (hW : (Q.restrict W).Nondegenerate)
    (x : LinearMap.BilinForm.orthogonal Q.polarBilin W × W) :
    decompOrth hW x = (x.1 : V) + (x.2 : V) := rfl

omit [Invertible (2 : F)] [FiniteDimensional F V] in
theorem map_mem_orthogonal_of_fix
    {g : TauCeti.QuadraticMap.orthogonalGroup Q} (hg : ∀ x ∈ W, (g : V ≃ₗ[F] V) x = x)
    {n : V} (hn : n ∈ LinearMap.BilinForm.orthogonal Q.polarBilin W) :
    (g : V ≃ₗ[F] V) n ∈ LinearMap.BilinForm.orthogonal Q.polarBilin W := by
  intro w hw
  have h1 := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem g.2 w n
  rw [hg w hw] at h1
  have h2 : Q.polarBilin w n = 0 := hn w hw
  rw [QuadraticMap.polarBilin_apply_apply] at h2 ⊢
  rw [h1]
  exact h2

theorem mem_range_spinGroupMap_of_fix [Nontrivial V]
    [Nontrivial (LinearMap.BilinForm.orthogonal Q.polarBilin W)] (hQ : Q.Nondegenerate)
    (hW : (Q.restrict W).Nondegenerate) {y : spinGroup Q}
    (hy : ∀ x ∈ W, spinAction Q y x = x) :
    y ∈ ((decompOrth hW).toIsometry.comp
      (QuadraticMap.Isometry.inl (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W))
        (Q.restrict W))).spinGroupMap.range := by
  classical
  set N := LinearMap.BilinForm.orthogonal Q.polarBilin W with hN
  set Q₁ := Q.restrict N with hQ₁def
  set Q₂ := Q.restrict W with hQ₂def
  have hQ₁ : Q₁.Nondegenerate := hQ.nondegenerate_restrict_orthogonal hW
  set e := decompOrth hW with he
  set g : TauCeti.QuadraticMap.orthogonalGroup Q :=
    QuadraticMap.specialOrthogonalToOrthogonal Q (spinToSpecialOrthogonal Q y) with hgdef
  have hgc : ∀ v, (g : V ≃ₗ[F] V) v = spinAction Q y v := fun v => by
    rw [hgdef, QuadraticMap.coe_specialOrthogonalToOrthogonal]
    exact coe_spinToSpecialOrthogonal_apply' Q y v
  have hgfix : ∀ x ∈ W, (g : V ≃ₗ[F] V) x = x := fun x hx => by rw [hgc]; exact hy x hx
  have hdet : QuadraticMap.orthogonalDet Q g = 1 :=
    QuadraticMap.orthogonalDet_specialOrthogonalToOrthogonal _
  have hsn : orthogonalSpinorNorm Q hQ g = 1 := by
    have := CliffordAlgebra.spinorNorm_spinToSpecialOrthogonal Q hQ y
    rwa [CliffordAlgebra.spinorNorm_apply] at this
  set g' : TauCeti.QuadraticMap.orthogonalGroup (Q₁.prod Q₂) :=
    TauCeti.QuadraticMap.orthogonalGroupCongr e.symm g with hg'
  have hg'app : ∀ m, (g' : _ ≃ₗ[F] _) m = e.symm ((g : V ≃ₗ[F] V) (e m)) := fun m =>
    TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply e.symm g m
  have hsymm_N : ∀ (n : N), e.symm (n : V) = (n, 0) := fun n => by
    change e.toLinearEquiv.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    change _ = ((n : N) : V) + ((0 : W) : V)
    simp
  have hsymm_W : ∀ (w : W), e.symm (w : V) = (0, w) := fun w => by
    change e.toLinearEquiv.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    change _ = ((0 : N) : V) + ((w : W) : V)
    simp
  have hrange : g' ∈ (orthogonalGroupProd Q₁ Q₂).range := by
    rw [mem_range_orthogonalGroupProd_iff]
    refine ⟨fun m₁ => ?_, fun m₂ => ?_⟩
    · rw [hg'app]
      have h0 : e (m₁, 0) = (m₁ : V) := by rw [decompOrth_apply]; simp
      rw [h0]
      have hmem := map_mem_orthogonal_of_fix hgfix m₁.2
      have := hsymm_N ⟨(g : V ≃ₗ[F] V) (m₁ : V), hmem⟩
      rw [this]
    · rw [hg'app]
      have h0 : e (0, m₂) = (m₂ : V) := by rw [decompOrth_apply]; simp
      rw [h0, hgfix _ m₂.2, hsymm_W]
  obtain ⟨⟨f₁, f₂⟩, hf⟩ := hrange
  have hfapp : ∀ m : N × W, ((f₁ : N ≃ₗ[F] N) m.1, (f₂ : W ≃ₗ[F] W) m.2) =
      (g' : _ ≃ₗ[F] _) m := fun m => by
    rw [← hf, orthogonalGroupProd_apply]
  have hf₂ : f₂ = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun w => ?_)
    have := hfapp (0, w)
    rw [hg'app] at this
    have h0 : e (0, w) = (w : V) := by rw [decompOrth_apply]; simp
    rw [h0, hgfix _ w.2, hsymm_W] at this
    exact (Prod.ext_iff.1 this).2
  have hdet' : LinearEquiv.det g'.1 = LinearEquiv.det (g : V ≃ₗ[F] V) := by
    have := LinearEquiv.det_conj (g : V ≃ₗ[F] V) e.symm.toLinearEquiv
    convert this using 2
    refine LinearEquiv.ext fun m => ?_
    rw [hg'app]
    rfl
  have hdet₁ : QuadraticMap.orthogonalDet Q₁ f₁ = 1 := by
    have h1 := det_orthogonalGroupProd Q₁ Q₂ (f₁, f₂)
    rw [hf, hdet', hf₂] at h1
    have h2 : LinearEquiv.det (g : V ≃ₗ[F] V) = 1 := by
      rw [← QuadraticMap.orthogonalDet_apply]; exact hdet
    rw [h2] at h1
    simpa using h1.symm
  have hsn₁ : orthogonalSpinorNorm Q₁ hQ₁ f₁ = 1 := by
    have h1 := orthogonalSpinorNorm_orthogonalGroupProd hQ₁ hW (f₁, f₂)
    rw [hf] at h1
    have h2 := QuadraticMap.IsometryEquiv.orthogonalSpinorNorm_orthogonalGroupCongr e.symm hQ g
    rw [hg'] at h1
    rw [h2, hsn, hf₂, map_one] at h1
    exact (mul_one _).symm.trans h1.symm
  obtain ⟨x, hx⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_spinAction_eq hQ₁ f₁ hdet₁ hsn₁
  set ι := e.toIsometry.comp (QuadraticMap.Isometry.inl Q₁ Q₂) with hι
  have hvec : ∀ {P : Type} [AddCommGroup P] [Module F P] (R : QuadraticForm F P)
      (z : spinGroup R) (v : P), spinAction R z v = CliffordAlgebra.spinVectorAction R z v :=
    fun R z v => (coe_spinToSpecialOrthogonal_apply' R z v).symm.trans
      (CliffordAlgebra.coe_spinToSpecialOrthogonal_apply R z v)
  have hact : spinAction Q (ι.spinGroupMap x) = spinAction Q y := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨⟨m₁, m₂⟩, rfl⟩ := e.toLinearEquiv.surjective v
    have h1 := QuadraticMap.IsometryEquiv.spinGroupMap_spinVectorAction_prod e.symm x m₁ m₂
    have h2 : CliffordAlgebra.spinVectorAction Q₁ x m₁ = (f₁ : N ≃ₗ[F] N) m₁ := by
      rw [← hvec Q₁ x m₁, hx]
    rw [h2] at h1
    have h3 : (g' : _ ≃ₗ[F] _) (m₁, m₂) = ((f₁ : N ≃ₗ[F] N) m₁, m₂) := by
      rw [← hfapp (m₁, m₂), hf₂]
      rfl
    have h4 : spinAction Q y (e (m₁, m₂)) = e ((f₁ : N ≃ₗ[F] N) m₁, m₂) := by
      rw [← hgc, ← h3, hg'app]
      exact (e.apply_symm_apply _).symm
    change spinAction Q (ι.spinGroupMap x) (e (m₁, m₂)) = spinAction Q y (e (m₁, m₂))
    rw [h4, hvec]
    exact h1
  have hker : y * (ι.spinGroupMap x)⁻¹ ∈ (spinAction Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hact, mul_inv_cancel]
  rcases (mem_ker_spinAction_iff Q hQ _).1 hker with h | h
  · refine ⟨x, ?_⟩
    exact (mul_inv_eq_one.1 h).symm
  · refine ⟨spinGroup.negOne Q₁ hQ₁.ne_zero * x, ?_⟩
    rw [map_mul, Isometry.spinGroupMap_negOne ι hQ₁.ne_zero]
    exact (mul_inv_eq_iff_eq_mul.1 h).symm

end CFSG.ClassicalInvolution.PhanP
