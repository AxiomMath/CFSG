module

public import CFSG.ClassicalGroups.Unitary.Generation
public import CFSG.LinearAlgebra.LinearGroups.UnitaryTransitivity

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.LinearGroups CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary Matrix

variable {p f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

namespace UnitaryFieldData

@[expose] noncomputable def barEquiv (h : UnitaryFieldData p f K) : K ≃+* K where
  toFun := h.bar
  invFun := h.bar
  left_inv := h.bar_bar
  right_inv := h.bar_bar
  map_mul' := map_mul h.bar
  map_add' := map_add h.bar

theorem barEquiv_apply (h : UnitaryFieldData p f K) (c : K) : h.barEquiv c = h.bar c :=
  rfl

theorem isUnitaryInvolution_barEquiv (h : UnitaryFieldData p f K) :
    IsUnitaryInvolution h.barEquiv where
  invol := h.bar_bar
  exists_ne := h.exists_bar_ne
  trace_surj a ha := by
    obtain ⟨c, hc⟩ := h.traceLin_surjective ⟨a, h.mem_fixedField.mpr ha⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  norm_surj d hd _ := by
    obtain ⟨c, hc⟩ := h.normHom_surjective ⟨d, h.mem_fixedField.mpr hd⟩
    exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩

end UnitaryFieldData

section Transport

variable {n : ℕ}

theorem toLin'_apply_eq (e : Module.Basis (Fin n) K V) (M : GL (Fin n) K) (x : V) :
    ((GeneralLinearGroup.toLin' e M : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x =
      e.equivFun.symm ((M : Matrix (Fin n) (Fin n) K) *ᵥ e.equivFun x) :=
  rfl

theorem equivFun_toLin'_apply (e : Module.Basis (Fin n) K V) (M : GL (Fin n) K) (x : V) :
    e.equivFun (((GeneralLinearGroup.toLin' e M : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) x) = (M : Matrix (Fin n) (Fin n) K) *ᵥ e.equivFun x := by
  rw [toLin'_apply_eq, LinearEquiv.apply_symm_apply]

theorem det_toLin' (e : Module.Basis (Fin n) K V) (M : GL (Fin n) K) :
    LinearMap.det ((GeneralLinearGroup.toLin' e M : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) = (M : Matrix (Fin n) (Fin n) K).det := by
  have hM : ((GeneralLinearGroup.toLin' e M : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
      Matrix.toLin e e M := by
    ext x
    rw [Matrix.toLin_apply, toLin'_apply_eq, Module.Basis.equivFun_symm_apply,
      Module.Basis.equivFun_apply]
  rw [hM, LinearMap.det_toLin]

variable (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}

theorem form_eq_herm (e : Module.Basis (Fin n) K V)
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) (x y : V) :
    B x y = herm h.barEquiv (e.equivFun x) (e.equivFun y) := by
  rw [herm_def]
  conv_lhs => rw [← e.sum_equivFun x, ← e.sum_equivFun y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, he,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, RingHom.id_apply,
    UnitaryFieldData.barEquiv_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem toLin'_mem_sesqSpecialUnitaryGroup_iff (e : Module.Basis (Fin n) K V)
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) (M : GL (Fin n) K) :
    GeneralLinearGroup.toLin' e M ∈ sesqSpecialUnitaryGroup B ↔ M ∈ SUid h.barEquiv n := by
  rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, det_toLin', mem_SUid_iff]
  constructor
  · rintro ⟨hiso, hdet⟩
    refine ⟨hdet, fun u v => ?_⟩
    have huv := hiso (e.equivFun.symm u) (e.equivFun.symm v)
    simpa only [form_eq_herm h e he, equivFun_toLin'_apply, LinearEquiv.apply_symm_apply]
      using huv
  · rintro ⟨hdet, hiso⟩
    refine ⟨fun x y => ?_, hdet⟩
    rw [form_eq_herm h e he, form_eq_herm h e he, equivFun_toLin'_apply, equivFun_toLin'_apply,
      hiso]

theorem toLin'_mem_unitaryTransvections (e : Module.Basis (Fin n) K V)
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) {A : SUid h.barEquiv n}
    (hA : A ∈ tvSet h.barEquiv n) :
    GeneralLinearGroup.toLin' e (A : GL (Fin n) K) ∈ unitaryTransvections h B := by
  obtain ⟨a, c, ha, hc, hAv⟩ := hA
  have ha' : B (e.equivFun.symm a) (e.equivFun.symm a) = 0 := by
    rw [form_eq_herm h e he, LinearEquiv.apply_symm_apply, ha]
  refine ⟨e.equivFun.symm a, ha', c, h.mem_traceZero.mpr hc, Units.ext (LinearMap.ext fun x => ?_)⟩
  rw [coe_hermTransvectionGL, hermTransvection_apply, toLin'_apply_eq, ← smul_def, hAv,
    form_eq_herm h e he, LinearEquiv.apply_symm_apply, map_add, map_smul,
    LinearEquiv.symm_apply_apply]

end Transport

theorem unitary_transvection_generation (h : UnitaryFieldData p f K)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 2 ≤ Module.finrank K V) (hnq : (Module.finrank K V, p ^ f) ≠ (3, 2)) :
    Subgroup.closure (unitaryTransvections h B) = sesqSpecialUnitaryGroup B := by
  have : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun g hg => ?_
  · rintro _ ⟨a, ha, c, hc, rfl⟩
    exact (hermitian_unitary_transvection h hB ha).2.1 c hc
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hB hBl
  have h3 : Module.finrank K V = 3 → ∃ s : K, s ≠ 0 ∧ h.barEquiv s * s ≠ 1 := by
    intro hn3
    have hp := h.prime.two_le
    have hpq : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    have hq2 : p ^ f ≠ 2 := fun hq => hnq (by rw [hn3, hq])
    obtain ⟨s, hs0, hs⟩ := exists_ne_zero_norm_ne_one h (by omega)
    exact ⟨s, hs0, by rwa [UnitaryFieldData.barEquiv_apply, mul_comm]⟩
  have hT := T_eq_top h.isUnitaryInvolution_barEquiv hn h3
  let Ψ := GeneralLinearGroup.toLin' e
  have hM : Ψ.symm g ∈ SUid h.barEquiv (Module.finrank K V) := by
    rw [← toLin'_mem_sesqSpecialUnitaryGroup_iff h e he, MulEquiv.apply_symm_apply]
    exact hg
  have key : ∀ A ∈ T h.barEquiv (Module.finrank K V),
      Ψ (A : GL (Fin (Module.finrank K V)) K) ∈ Subgroup.closure (unitaryTransvections h B) := by
    intro A hA
    induction hA using Subgroup.closure_induction with
    | mem A hA => exact Subgroup.subset_closure (toLin'_mem_unitaryTransvections h e he hA)
    | one =>
      rw [OneMemClass.coe_one, map_one]
      exact Subgroup.one_mem _
    | mul A A' _ _ hA hA' =>
      rw [MulMemClass.coe_mul, map_mul]
      exact Subgroup.mul_mem _ hA hA'
    | inv A _ hA =>
      rw [InvMemClass.coe_inv, map_inv]
      exact Subgroup.inv_mem _ hA
  have hg' := key ⟨Ψ.symm g, hM⟩ (by rw [hT]; exact Subgroup.mem_top _)
  have hΨ : Ψ ((⟨Ψ.symm g, hM⟩ : SUid h.barEquiv (Module.finrank K V)) :
      GL (Fin (Module.finrank K V)) K) = g := Ψ.apply_symm_apply g
  rwa [hΨ] at hg'

theorem unitary_four_transvection_generation (h : UnitaryFieldData p f K) (hq : p ^ f = 2)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : Module.finrank K V = 4) :
    Subgroup.closure (unitaryTransvections h B) = sesqSpecialUnitaryGroup B :=
  unitary_transvection_generation h hB hBl (by omega) (by rw [hn, hq]; decide)

end CFSG.LocalAnalysis.ComponentInitial
