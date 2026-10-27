module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

variable {k : Type*} [Field k] {σ : k →+* k} {M : Type*} [AddCommGroup M] [Module k M]

@[expose] def sesqUnitaryGroup (B : M →ₛₗ[σ] M →ₗ[k] k) :
    Subgroup (LinearMap.GeneralLinearGroup k M) where
  carrier := {g | ∀ x y, B ((g : M →ₗ[k] M) x) ((g : M →ₗ[k] M) y) = B x y}
  one_mem' _ _ := rfl
  mul_mem' {g g'} hg hg' x y := (hg _ _).trans (hg' x y)
  inv_mem' {g} hg x y := by
    have h := hg (((g⁻¹ : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) x)
      (((g⁻¹ : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) y)
    simp only [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply] at h
    exact h.symm

theorem mem_sesqUnitaryGroup {B : M →ₛₗ[σ] M →ₗ[k] k} {g : LinearMap.GeneralLinearGroup k M} :
    g ∈ sesqUnitaryGroup B ↔ ∀ x y, B ((g : M →ₗ[k] M) x) ((g : M →ₗ[k] M) y) = B x y :=
  Iff.rfl

@[expose] noncomputable def sesqSpecialUnitaryGroup (B : M →ₛₗ[σ] M →ₗ[k] k) :
    Subgroup (LinearMap.GeneralLinearGroup k M) :=
  sesqUnitaryGroup B ⊓ (Units.map (LinearMap.det : (M →ₗ[k] M) →* k)).ker

theorem mem_sesqSpecialUnitaryGroup {B : M →ₛₗ[σ] M →ₗ[k] k}
    {g : LinearMap.GeneralLinearGroup k M} :
    g ∈ sesqSpecialUnitaryGroup B ↔
      g ∈ sesqUnitaryGroup B ∧ LinearMap.det (g : M →ₗ[k] M) = 1 := by
  rw [sesqSpecialUnitaryGroup, Subgroup.mem_inf, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
    Units.val_one]

theorem sesqSpecialUnitaryGroup_le (B : M →ₛₗ[σ] M →ₗ[k] k) :
    sesqSpecialUnitaryGroup B ≤ sesqUnitaryGroup B :=
  inf_le_left

section Orthonormal

variable {B : M →ₛₗ[σ] M →ₗ[k] k}

theorem sesq_eq_zero_of_forall_isotropic (hB : B.IsSymm) {c₀ : k} (hc₀ : σ c₀ ≠ c₀)
    (P : M →ₗ[k] M) (hP : ∀ y, B (P y) (P y) = 0) (y y' : M) : B (P y) (P y') = 0 := by
  have h1 := hP (y + y')
  have h2 := hP (y + c₀ • y')
  have hconj : B (P y') (P y) = σ (B (P y) (P y')) := (hB.eq (P y) (P y')).symm
  simp only [map_add, map_smul, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, hP y, hP y', hconj] at h1 h2
  have h3 : (c₀ - σ c₀) * B (P y) (P y') = 0 := by linear_combination h2 - σ c₀ * h1
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc₀
  · exact h

theorem exists_norm_one_perp_of_lt [FiniteDimensional k M] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {c₀ : k} (hc₀ : σ c₀ ≠ c₀)
    (hnorm : ∀ d : k, σ d = d → d ≠ 0 → ∃ c, σ c * c = d) {r : ℕ}
    (hr : r < Module.finrank k M) (b : Fin r → M)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) :
    ∃ v, B v v = 1 ∧ ∀ i, B (b i) v = 0 := by
  classical
  let P : M →ₗ[k] M := LinearMap.id - ∑ i, (B (b i)).smulRight (b i)
  have hPy : ∀ y, P y = y - ∑ i, B (b i) y • b i := fun y => by simp [P]
  have hbP : ∀ y j, B (b j) (P y) = 0 := by
    intro y j
    rw [hPy, map_sub, map_sum]
    simp [map_smul, hb]
  by_cases hex : ∃ y, B (P y) (P y) ≠ 0
  · obtain ⟨y, hy⟩ := hex
    have hd : σ (B (P y) (P y)) = B (P y) (P y) := hB.eq (P y) (P y)
    obtain ⟨c, hc⟩ := hnorm (B (P y) (P y))⁻¹ (by rw [map_inv₀, hd]) (inv_ne_zero hy)
    refine ⟨c • P y, ?_, fun i => ?_⟩
    · have e : B (c • P y) (c • P y) = σ c * c * B (P y) (P y) := by
        simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
      rw [e, hc, inv_mul_cancel₀ hy]
    · rw [map_smul, hbP, smul_zero]
  · push Not at hex
    have hpol := sesq_eq_zero_of_forall_isotropic hB hc₀ P hex
    have hP0 : ∀ y, P y = 0 := by
      intro y
      refine hBl _ fun z => ?_
      have hz : z = P z + ∑ i, B (b i) z • b i := by rw [hPy]; abel
      have hyb : ∀ i, B (P y) (b i) = 0 := fun i => by
        rw [← hB.eq (b i) (P y), hbP, map_zero]
      rw [hz, map_add, hpol, map_sum]
      simp [map_smul, hyb]
    have htop : Submodule.span k (Set.range b) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y = ∑ i, B (b i) y • b i := by
        have := hPy y
        rw [hP0] at this
        exact sub_eq_zero.mp this.symm
      rw [hy]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hle := finrank_range_le_card (R := k) b
    rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at hle
    omega

theorem exists_orthonormal_family [FiniteDimensional k M] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {c₀ : k} (hc₀ : σ c₀ ≠ c₀)
    (hnorm : ∀ d : k, σ d = d → d ≠ 0 → ∃ c, σ c * c = d) {r : ℕ}
    (hr : r ≤ Module.finrank k M) :
    ∃ b : Fin r → M, ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  induction r with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0⟩
  | succ r ih =>
    obtain ⟨b, hb⟩ := ih (by omega)
    obtain ⟨v, hv, hbv⟩ := exists_norm_one_perp_of_lt hB hBl hc₀ hnorm (by omega) b hb
    have hvb : ∀ i, B v (b i) = 0 := fun i => by rw [← hB.eq (b i) v, hbv i, map_zero]
    refine ⟨Fin.cons v b, fun i j => ?_⟩
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [hv, hbv, hvb, hb, (Fin.succ_ne_zero _).symm]

theorem exists_orthonormal_basis_of_norm [FiniteDimensional k M] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {c₀ : k} (hc₀ : σ c₀ ≠ c₀)
    (hnorm : ∀ d : k, σ d = d → d ≠ 0 → ∃ c, σ c * c = d) :
    ∃ e : Module.Basis (Fin (Module.finrank k M)) k M,
      ∀ i j, B (e i) (e j) = if i = j then 1 else 0 := by
  obtain ⟨b, hb⟩ := exists_orthonormal_family hB hBl hc₀ hnorm le_rfl
  have hli : LinearIndependent k b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (B (b j)) hg
    simpa [map_sum, map_smul, hb] using this
  have hspan : Submodule.span k (Set.range b) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin])
  exact ⟨Module.Basis.mk hli hspan.ge, fun i j => by simp [Module.Basis.coe_mk, hb]⟩

end Orthonormal

theorem UnitaryFieldData.exists_orthonormal_basis {p f : ℕ} (h : UnitaryFieldData p f k)
    [FiniteDimensional k M] {B : M →ₛₗ[h.bar] M →ₗ[k] k} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) :
    ∃ e : Module.Basis (Fin (Module.finrank k M)) k M,
      ∀ i j, B (e i) (e j) = if i = j then 1 else 0 := by
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  refine exists_orthonormal_basis_of_norm hB hBl hc₀ fun d hd _ => ?_
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨d, hd⟩
  exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩

end CFSG.LocalAnalysis.ComponentInitial
