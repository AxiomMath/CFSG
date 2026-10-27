module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPolarRecovery

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem unitarySU_ext_mulVecLin {g g' : unitarySU p f K n}
    (hgg : mulVecLin ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      mulVecLin ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : g = g' :=
  Subtype.ext (Units.ext (Matrix.toLin'.injective (by
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply', hgg])))

@[expose] noncomputable def ptTransvection (h : UnitaryFieldData p f K) {a : Fin n → K}
    (ha : stdHermForm h n a a = 0) (c : h.traceZero) : unitarySU p f K n :=
  Classical.choose (exists_mem_unitarySU_hermTransvection h ha c.2)

theorem mulVecLin_ptTransvection (h : UnitaryFieldData p f K) {a : Fin n → K}
    (ha : stdHermForm h n a a = 0) (c : h.traceZero) :
    mulVecLin (((ptTransvection h ha c : unitarySU p f K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = hermTransvection (stdHermForm h n) a c :=
  Classical.choose_spec (exists_mem_unitarySU_hermTransvection h ha c.2)

@[expose] noncomputable def ptTransvectionHom (h : UnitaryFieldData p f K) {a : Fin n → K}
    (ha : stdHermForm h n a a = 0) : Multiplicative h.traceZero →* unitarySU p f K n where
  toFun c := ptTransvection h ha c.toAdd
  map_one' := unitarySU_ext_mulVecLin (by
    rw [mulVecLin_ptTransvection, toAdd_one, ZeroMemClass.coe_zero, hermTransvection_zero,
      Subgroup.coe_one, Units.val_one, Matrix.mulVecLin_one])
  map_mul' c d := unitarySU_ext_mulVecLin (by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_mul, mulVecLin_ptTransvection,
      mulVecLin_ptTransvection, mulVecLin_ptTransvection, toAdd_mul, AddMemClass.coe_add,
      hermTransvection_comp _ ha])

theorem mulVecLin_ptTransvectionHom (h : UnitaryFieldData p f K) {a : Fin n → K}
    (ha : stdHermForm h n a a = 0) (c : Multiplicative h.traceZero) :
    mulVecLin (((ptTransvectionHom h ha c : unitarySU p f K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = hermTransvection (stdHermForm h n) a c.toAdd :=
  mulVecLin_ptTransvection h ha c.toAdd

theorem exists_stdHermForm_eq_one (h : UnitaryFieldData p f K) {a : Fin n → K} (ha0 : a ≠ 0) :
    ∃ x, stdHermForm h n a x = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, stdHermForm h n a y ≠ 0 := by
    by_contra! hz
    exact ha0 (stdHermForm_separatingLeft h n a hz)
  exact ⟨(stdHermForm h n a y)⁻¹ • y, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]⟩

theorem ptTransvectionHom_injective (h : UnitaryFieldData p f K) {a : Fin n → K}
    (ha : stdHermForm h n a a = 0) (ha0 : a ≠ 0) : Function.Injective (ptTransvectionHom h ha) := by
  intro c d hcd
  have hm := congrArg (fun g : unitarySU p f K n =>
    mulVecLin ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hcd
  simp only [mulVecLin_ptTransvectionHom] at hm
  obtain ⟨x, hx⟩ := exists_stdHermForm_eq_one h ha0
  have hxx := LinearMap.congr_fun hm x
  rw [hermTransvection_apply, hermTransvection_apply, hx, mul_one, mul_one] at hxx
  have hca : ((c.toAdd : K) - d.toAdd) • a = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact add_left_cancel hxx
  rcases smul_eq_zero.mp hca with h0 | h0
  · exact Multiplicative.toAdd.injective (Subtype.ext (sub_eq_zero.mp h0))
  · exact absurd h0 ha0

theorem norm_mul_mem_traceZero (h : UnitaryFieldData p f K) (μ : K) {c : K}
    (hc : c ∈ h.traceZero) : h.norm μ * c ∈ h.traceZero := by
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace] at hc ⊢
  rw [map_mul, (UnitaryFieldData.mem_fixedField h).mp (h.norm_mem_fixedField μ), ← mul_add, hc,
    mul_zero]

theorem unitary_point_subgroup (h : UnitaryFieldData p f K) {L : Submodule K (Fin n → K)}
    (hL : L ∈ isotropicLines h n) {a : Fin n → K} (haL : a ∈ L) (ha0 : a ≠ 0) :
    (∀ c : Multiplicative h.traceZero,
      mulVecLin (((ptTransvectionHom h (hL.2 a haL) c : unitarySU p f K n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = hermTransvection (stdHermForm h n) a c.toAdd) ∧
    Function.Injective (ptTransvectionHom h (hL.2 a haL)) ∧
    (ptTransvectionHom h (hL.2 a haL)).range = isotropicTransvectionGroup h n L ∧
    ∀ x ∈ isotropicTransvectionGroup h n L, ∀ y ∈ isotropicTransvectionGroup h n L,
      x * y = y * x := by
  set φ := ptTransvectionHom h (hL.2 a haL) with hφ
  have hrange : φ.range = isotropicTransvectionGroup h n L := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      exact Subgroup.subset_closure ⟨a, haL, c.toAdd, c.toAdd.2,
        mulVecLin_ptTransvectionHom h _ c⟩
    · refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨b, hb, c, hc, hg⟩
      obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp
        ((eq_span_singleton_of_mem_of_finrank_eq_one hL.1 haL ha0) ▸ hb)
      have hscale := (hermitian_unitary_transvection h (stdHermForm_isSymm h n)
        (hL.2 a haL)).2.2.2.2.2 c hc μ
      refine ⟨Multiplicative.ofAdd ⟨h.norm μ * c, norm_mul_mem_traceZero h μ hc⟩,
        unitarySU_ext_mulVecLin ?_⟩
      rw [mulVecLin_ptTransvectionHom, hg, hscale]
      rfl
  refine ⟨mulVecLin_ptTransvectionHom h _, ptTransvectionHom_injective h _ ha0, hrange,
    fun x hx y hy => ?_⟩
  rw [← hrange] at hx hy
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem mulVecLin_conj_hermTransvection (h : UnitaryFieldData p f K) (g : unitarySU p f K n)
    {x : unitarySU p f K n} {a : Fin n → K} {c : K}
    (hx : mulVecLin ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      hermTransvection (stdHermForm h n) a c) :
    mulVecLin (((g * x * g⁻¹ : unitarySU p f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      hermTransvection (stdHermForm h n) (g • a) c := by
  refine LinearMap.ext fun v => ?_
  have hgi : g • g⁻¹ • v = v := smul_inv_smul g v
  have hiso := stdHermForm_smul_smul h g a (g⁻¹ • v)
  rw [hgi] at hiso
  have hxv := LinearMap.congr_fun hx (g⁻¹ • v)
  rw [mulVecLin_apply] at hxv
  rw [hermTransvection_apply, hiso, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
    Units.val_mul, mulVecLin_apply, ← mulVec_mulVec, ← mulVec_mulVec]
  change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
    (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (g⁻¹ • v)) = _
  rw [hxv, hermTransvection_apply, mulVec_add, mulVec_smul]
  change g • g⁻¹ • v + _ • (g • a) = _
  rw [hgi]

theorem unitary_point_conjugation (h : UnitaryFieldData p f K) (g : unitarySU p f K n)
    {L : Submodule K (Fin n → K)} (hL : L ∈ isotropicLines h n) :
    g • L ∈ isotropicLines h n ∧
    (isotropicTransvectionGroup h n L).map (MulAut.conj g).toMonoidHom =
      isotropicTransvectionGroup h n (g • L) ∧
    isotropicTransvectionGroup h n L ≤ MulAction.stabilizer (unitarySU p f K n) L ∧
    ((isotropicTransvectionGroup h n L).subgroupOf
      (MulAction.stabilizer (unitarySU p f K n) L)).Normal := by
  have hmap : ∀ (g : unitarySU p f K n) (L : Submodule K (Fin n → K)),
      (isotropicTransvectionGroup h n L).map (MulAut.conj g).toMonoidHom =
        isotropicTransvectionGroup h n (g • L) := by
    intro g L
    rw [isotropicTransvectionGroup, MonoidHom.map_closure, isotropicTransvectionGroup]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨b, hb, c, hc, hx⟩, rfl⟩
      exact ⟨g • b, Submodule.smul_mem_pointwise_smul _ _ _ hb, c, hc,
        mulVecLin_conj_hermTransvection h g hx⟩
    · rintro ⟨b', hb', c, hc, hy⟩
      obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists b' g L).mp hb'
      refine ⟨g⁻¹ * y * g⁻¹⁻¹, ⟨b, hb, c, hc, ?_⟩, ?_⟩
      · rw [mulVecLin_conj_hermTransvection h g⁻¹ hy, inv_smul_smul]
      · change g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y
        group
  have hfix : isotropicTransvectionGroup h n L ≤ MulAction.stabilizer (unitarySU p f K n) L := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨b, hb, c, -, hx⟩
    have htot := isTotIso_of_mem_isoLines (B := stdHermForm h n) hL
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.smul_def, smul_eq_map, hx]
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hermTransvection_apply, htot b hb u hu, mul_zero, zero_smul, add_zero]
      exact hu
    · intro hv
      exact ⟨v, hv, by rw [hermTransvection_apply, htot b hb v hv, mul_zero, zero_smul, add_zero]⟩
  refine ⟨(isotropicLines h n).smul_mem g hL, hmap g L, hfix,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hfix).mpr fun s hs => ?_⟩
  have hsL : s • L = L := MulAction.mem_stabilizer_iff.mp hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have := Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hu
    rwa [hmap s L, hsL] at this
  · intro hu
    have hs' : s⁻¹ • L = L := by rw [← hsL, inv_smul_smul, hsL]
    have := Subgroup.mem_map_of_mem (MulAut.conj s⁻¹).toMonoidHom hu
    rw [hmap s⁻¹ L, hs'] at this
    convert this using 1
    change u = s⁻¹ * (s * u * s⁻¹) * s⁻¹⁻¹
    group

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
