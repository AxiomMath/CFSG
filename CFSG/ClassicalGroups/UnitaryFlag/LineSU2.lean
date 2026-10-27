module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherProjectiveAction

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open scoped Pointwise CharTwo

variable {m : ℕ} {K : Type} [Field K]

private theorem two_eq_zero (h : UnitaryFieldData 2 m K) : (2 : K) = 0 := by
  haveI := h.charP
  exact CharP.cast_eq_zero K 2

private theorem add_self_eq_zero (h : UnitaryFieldData 2 m K) (c : K) : c + c = 0 := by
  rw [← two_mul, two_eq_zero h, zero_mul]

theorem mem_traceZero_iff_bar_eq (h : UnitaryFieldData 2 m K) {c : K} :
    c ∈ h.traceZero ↔ h.bar c = c := by
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace]
  constructor
  · intro hc
    exact add_left_cancel (hc.trans (add_self_eq_zero h c).symm)
  · intro hc
    rw [hc, add_self_eq_zero h]

theorem mem_traceZero_of_bar_eq (h : UnitaryFieldData 2 m K) {c : K} (hc : h.bar c = c) :
    c ∈ h.traceZero :=
  (mem_traceZero_iff_bar_eq h).mpr hc

@[expose] def stdIsoA : Fin 3 → K := ![1, 1, 0]

@[expose] def stdIsoB : Fin 3 → K := ![0, 1, 1]

@[expose] def stdNormC : Fin 3 → K := ![1, 1, 1]

@[simp] theorem stdHermForm_stdIsoA_stdIsoA (h : UnitaryFieldData 2 m K) :
    stdHermForm h 3 stdIsoA stdIsoA = 0 := by
  haveI := h.charP
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [stdHermForm_apply, stdIsoA, Fin.sum_univ_three, h2]

@[simp] theorem stdHermForm_stdIsoB_stdIsoB (h : UnitaryFieldData 2 m K) :
    stdHermForm h 3 stdIsoB stdIsoB = 0 := by
  haveI := h.charP
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [stdHermForm_apply, stdIsoB, Fin.sum_univ_three, h2]

@[simp] theorem stdHermForm_stdNormC_stdNormC (h : UnitaryFieldData 2 m K) :
    stdHermForm h 3 stdNormC stdNormC = 1 := by
  haveI := h.charP
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have h3 : (1 : K) + 1 + 1 = 1 := by rw [h2, zero_add]
  simp [stdHermForm_apply, stdNormC, Fin.sum_univ_three, h3]

@[simp] theorem stdHermForm_stdIsoA_stdIsoB (h : UnitaryFieldData 2 m K) :
    stdHermForm h 3 stdIsoA stdIsoB = 1 := by
  simp [stdHermForm_apply, stdIsoA, stdIsoB, Fin.sum_univ_three]

@[simp] theorem stdHermForm_stdIsoB_stdIsoA (h : UnitaryFieldData 2 m K) :
    stdHermForm h 3 stdIsoB stdIsoA = 1 := by
  simp [stdHermForm_apply, stdIsoA, stdIsoB, Fin.sum_univ_three]

@[simp] theorem stdHermForm_stdIsoA_stdNormC (h : UnitaryFieldData 2 m K) :
    stdHermForm h 3 stdIsoA stdNormC = 0 := by
  haveI := h.charP
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [stdHermForm_apply, stdIsoA, stdNormC, Fin.sum_univ_three, h2]

@[simp] theorem stdHermForm_stdIsoB_stdNormC (h : UnitaryFieldData 2 m K) :
    stdHermForm h 3 stdIsoB stdNormC = 0 := by
  haveI := h.charP
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [stdHermForm_apply, stdIsoB, stdNormC, Fin.sum_univ_three, h2]

theorem stdIsoA_ne_zero : (stdIsoA : Fin 3 → K) ≠ 0 := by
  intro h0
  have := congrFun h0 0
  simp [stdIsoA] at this

theorem stdIsoB_ne_zero : (stdIsoB : Fin 3 → K) ≠ 0 := by
  intro h0
  have := congrFun h0 2
  simp [stdIsoB] at this

@[expose] def stdLinePlane : Submodule K (Fin 3 → K) := Submodule.span K {stdIsoA, stdIsoB}

@[expose] def stdPointA : Submodule K (Fin 3 → K) := Submodule.span K {stdIsoA}

@[expose] def stdPointB : Submodule K (Fin 3 → K) := Submodule.span K {stdIsoB}

theorem stdIsoA_mem_stdPointA : (stdIsoA : Fin 3 → K) ∈ stdPointA :=
  Submodule.mem_span_singleton_self _

theorem stdIsoB_mem_stdPointB : (stdIsoB : Fin 3 → K) ∈ stdPointB :=
  Submodule.mem_span_singleton_self _

theorem stdPointA_le_stdLinePlane : stdPointA (K := K) ≤ stdLinePlane (K := K) := by
  intro x hx
  rw [stdPointA] at hx
  rw [stdLinePlane]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  exact Submodule.smul_mem _ c
    (Submodule.subset_span (Set.mem_insert (stdIsoA : Fin 3 → K) {stdIsoB}))

theorem stdPointB_le_stdLinePlane : stdPointB (K := K) ≤ stdLinePlane (K := K) := by
  intro x hx
  rw [stdPointB] at hx
  rw [stdLinePlane]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  exact Submodule.smul_mem _ c
    (Submodule.subset_span (Set.mem_insert_of_mem (stdIsoA : Fin 3 → K)
      (Set.mem_singleton (stdIsoB : Fin 3 → K))))

theorem stdPointA_mem_isotropicLines (h : UnitaryFieldData 2 m K) :
    stdPointA ∈ isotropicLines h 3 :=
  span_singleton_mem_isotropicLines h stdIsoA_ne_zero (stdHermForm_stdIsoA_stdIsoA h)

theorem stdPointB_mem_isotropicLines (h : UnitaryFieldData 2 m K) :
    stdPointB ∈ isotropicLines h 3 :=
  span_singleton_mem_isotropicLines h stdIsoB_ne_zero (stdHermForm_stdIsoB_stdIsoB h)

theorem mem_stdLinePlane {v : Fin 3 → K} :
    v ∈ stdLinePlane ↔
      ∃ s t : K, s • (stdIsoA : Fin 3 → K) + t • (stdIsoB : Fin 3 → K) = v := by
  unfold stdLinePlane
  exact Submodule.mem_span_pair

@[expose] def stdLineSU2 (h : UnitaryFieldData 2 m K) : Subgroup (unitarySU 2 m K 3) :=
  isotropicTransvectionGroup h 3 stdPointA ⊔ isotropicTransvectionGroup h 3 stdPointB

theorem stdHermForm_stdIso_add_self (h : UnitaryFieldData 2 m K) (t : K) :
    stdHermForm h 3 (stdIsoA + t • (stdIsoB : Fin 3 → K))
      (stdIsoA + t • (stdIsoB : Fin 3 → K)) = t + h.bar t := by
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ,
    smul_eq_mul, stdHermForm_stdIsoA_stdIsoA, stdHermForm_stdIsoA_stdIsoB,
    stdHermForm_stdIsoB_stdIsoA, stdHermForm_stdIsoB_stdIsoB, mul_zero, mul_one, zero_add,
    add_zero]
  ring

theorem unitarySU_smul_def (h : UnitaryFieldData 2 m K) (g : unitarySU 2 m K 3)
    (v : Fin 3 → K) :
    g • v = mulVecLin ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) v := by
  rw [Subgroup.smul_def]
  change ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin 3) K) :
    LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v = _
  rw [Matrix.GeneralLinearGroup.coe_toLin]

theorem ptTransvection_smul (h : UnitaryFieldData 2 m K) {a : Fin 3 → K}
    (ha : stdHermForm h 3 a a = 0) (c : h.traceZero) (v : Fin 3 → K) :
    ptTransvection h ha c • v = v + ((c : K) * stdHermForm h 3 a v) • a := by
  rw [unitarySU_smul_def h, mulVecLin_ptTransvection, hermTransvection_apply]

theorem ptTransvection_mul_self (h : UnitaryFieldData 2 m K) {a : Fin 3 → K}
    (ha : stdHermForm h 3 a a = 0) (c : h.traceZero) :
    ptTransvection h ha c * ptTransvection h ha c = 1 := by
  apply unitarySU_ext_mulVecLin
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_mul, mulVecLin_ptTransvection,
    hermTransvection_comp _ ha]
  rw [show (c : K) + (c : K) = 0 from add_self_eq_zero h (c : K), hermTransvection_zero,
    Subgroup.coe_one, Units.val_one, Matrix.mulVecLin_one]

theorem ptTransvection_mem_isotropicTransvectionGroup (h : UnitaryFieldData 2 m K)
    {L : Submodule K (Fin 3 → K)} (hL : L ∈ isotropicLines h 3) {a : Fin 3 → K}
    (ha : a ∈ L) (ha0 : a ≠ 0) (c : h.traceZero) :
    ptTransvection h ((mem_isotropicLines.mp hL).2 a ha) c ∈
      isotropicTransvectionGroup h 3 L := by
  obtain ⟨g, hg, hgm⟩ := exists_mem_isotropicTransvectionGroup h hL ha c.2
  have heq : ptTransvection h ((mem_isotropicLines.mp hL).2 a ha) c = g :=
    unitarySU_ext_mulVecLin
      ((mulVecLin_ptTransvection h ((mem_isotropicLines.mp hL).2 a ha) c).trans hgm.symm)
  rwa [heq]

theorem ptTransvection_stdIsoB_mul_ptTransvection_stdIsoA_mul
    (h : UnitaryFieldData 2 m K) {t : K} (ht : t ∈ h.traceZero) {c : K}
    (hc : c ∈ h.traceZero)
    (hio : stdHermForm h 3 (stdIsoA + t • (stdIsoB : Fin 3 → K))
      (stdIsoA + t • (stdIsoB : Fin 3 → K)) = 0) :
    ptTransvection h (stdHermForm_stdIsoB_stdIsoB h) ⟨t, ht⟩ *
        ptTransvection h (stdHermForm_stdIsoA_stdIsoA h) ⟨c, hc⟩ *
        ptTransvection h (stdHermForm_stdIsoB_stdIsoB h) ⟨t, ht⟩ =
      ptTransvection h hio ⟨c, hc⟩ := by
  set g := ptTransvection h (stdHermForm_stdIsoB_stdIsoB h) ⟨t, ht⟩ with hg
  set x := ptTransvection h (stdHermForm_stdIsoA_stdIsoA h) ⟨c, hc⟩ with hx
  have hg2 : g * g = 1 := ptTransvection_mul_self h _ ⟨t, ht⟩
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hxlin : mulVecLin ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      hermTransvection (stdHermForm h 3) (stdIsoA : Fin 3 → K) c :=
    mulVecLin_ptTransvection h _ ⟨c, hc⟩
  have hconj := mulVecLin_conj_hermTransvection h g hxlin
  rw [hginv] at hconj
  have hga : g • (stdIsoA : Fin 3 → K) =
      (stdIsoA : Fin 3 → K) + t • (stdIsoB : Fin 3 → K) := by
    rw [ptTransvection_smul, stdHermForm_stdIsoB_stdIsoA]
    norm_num
  rw [hga] at hconj
  refine unitarySU_ext_mulVecLin ?_
  rw [hconj, mulVecLin_ptTransvection]

theorem stdHermForm_norm_smul (h : UnitaryFieldData 2 m K) (s : K) (w : Fin 3 → K) :
    stdHermForm h 3 (s • w) (s • w) = h.norm s * stdHermForm h 3 w w := by
  simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
    UnitaryFieldData.norm]
  ring

theorem hermTransvection_zero_vector (h : UnitaryFieldData 2 m K) (c : K) :
    hermTransvection (stdHermForm h 3) (0 : Fin 3 → K) c = LinearMap.id := by
  ext x
  simp [hermTransvection_apply]

theorem norm_ne_zero (h : UnitaryFieldData 2 m K) {s : K} (hs : s ≠ 0) : h.norm s ≠ 0 := by
  rw [UnitaryFieldData.norm]
  exact mul_ne_zero hs (fun h0 => hs ((h.bar_eq_zero_iff).mp h0))

theorem exists_mem_stdLineSU2_hermTransvection (h : UnitaryFieldData 2 m K)
    {v : Fin 3 → K} (hv : v ∈ stdLinePlane) (hvv : stdHermForm h 3 v v = 0) {c : K}
    (hc : c ∈ h.traceZero) :
    ∃ g ∈ stdLineSU2 h,
      mulVecLin ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        hermTransvection (stdHermForm h 3) v c := by
  haveI := h.charP
  obtain ⟨s, t, hst⟩ := mem_stdLinePlane.mp hv
  subst hst
  by_cases hs : s = 0
  · subst hs
    rw [zero_smul, zero_add] at hvv ⊢
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul] at hvv ⊢
      refine ⟨1, (stdLineSU2 h).one_mem, ?_⟩
      rw [Subgroup.coe_one, Units.val_one, Matrix.mulVecLin_one, hermTransvection_zero_vector]
    · have htc : h.norm t * c ∈ h.traceZero := norm_mul_mem_traceZero h t hc
      refine ⟨ptTransvection h (stdHermForm_stdIsoB_stdIsoB h) ⟨h.norm t * c, htc⟩, ?_, ?_⟩
      · exact Subgroup.mem_sup_right (ptTransvection_mem_isotropicTransvectionGroup h
          (stdPointB_mem_isotropicLines h) stdIsoB_mem_stdPointB stdIsoB_ne_zero _)
      · rw [mulVecLin_ptTransvection]
        exact ((hermitian_unitary_transvection h (stdHermForm_isSymm h 3)
          (stdHermForm_stdIsoB_stdIsoB h)).2.2.2.2.2 c hc t).symm
  · set u := t / s with hu
    have hst' : s • ((stdIsoA : Fin 3 → K) + u • (stdIsoB : Fin 3 → K)) =
        s • (stdIsoA : Fin 3 → K) + t • (stdIsoB : Fin 3 → K) := by
      rw [smul_add, smul_smul, hu]
      congr 1
      field_simp
    have hww : stdHermForm h 3 ((stdIsoA : Fin 3 → K) + u • (stdIsoB : Fin 3 → K))
        ((stdIsoA : Fin 3 → K) + u • (stdIsoB : Fin 3 → K)) = 0 := by
      have h1 : h.norm s * stdHermForm h 3
          ((stdIsoA : Fin 3 → K) + u • (stdIsoB : Fin 3 → K))
          ((stdIsoA : Fin 3 → K) + u • (stdIsoB : Fin 3 → K)) = 0 := by
        rw [← stdHermForm_norm_smul, hst']
        exact hvv
      exact (mul_eq_zero.mp h1).resolve_left (norm_ne_zero h hs)
    have hu_mem : u ∈ h.traceZero := by
      rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace]
      rw [← stdHermForm_stdIso_add_self h u]
      exact hww
    have hsc : h.norm s * c ∈ h.traceZero := norm_mul_mem_traceZero h s hc
    refine ⟨ptTransvection h (stdHermForm_stdIsoB_stdIsoB h) ⟨u, hu_mem⟩ *
        ptTransvection h (stdHermForm_stdIsoA_stdIsoA h) ⟨h.norm s * c, hsc⟩ *
        ptTransvection h (stdHermForm_stdIsoB_stdIsoB h) ⟨u, hu_mem⟩, ?_, ?_⟩
    · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
      · exact Subgroup.mem_sup_right (ptTransvection_mem_isotropicTransvectionGroup h
          (stdPointB_mem_isotropicLines h) stdIsoB_mem_stdPointB stdIsoB_ne_zero _)
      · exact Subgroup.mem_sup_left (ptTransvection_mem_isotropicTransvectionGroup h
          (stdPointA_mem_isotropicLines h) stdIsoA_mem_stdPointA stdIsoA_ne_zero _)
      · exact Subgroup.mem_sup_right (ptTransvection_mem_isotropicTransvectionGroup h
          (stdPointB_mem_isotropicLines h) stdIsoB_mem_stdPointB stdIsoB_ne_zero _)
    · rw [ptTransvection_stdIsoB_mul_ptTransvection_stdIsoA_mul h hu_mem hsc hww,
        mulVecLin_ptTransvection, ← hst']
      exact ((hermitian_unitary_transvection h (stdHermForm_isSymm h 3) hww).2.2.2.2.2 c hc s).symm

theorem stdLinePlane_eq_span_range :
    stdLinePlane (K := K) =
      Submodule.span K (Set.range ![(stdIsoA : Fin 3 → K), (stdIsoB : Fin 3 → K)]) := by
  unfold stdLinePlane
  congr 1
  ext x
  simp [or_comm]

theorem linearIndependent_stdIso (h : UnitaryFieldData 2 m K) :
    LinearIndependent K ![(stdIsoA : Fin 3 → K), (stdIsoB : Fin 3 → K)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun w => stdHermForm h 3 w (stdIsoB : Fin 3 → K)) hst
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ,
    stdHermForm_stdIsoA_stdIsoB, stdHermForm_stdIsoB_stdIsoB, smul_eq_mul, mul_one, mul_zero,
    add_zero, map_zero, LinearMap.zero_apply] at h1
  have h2 := congrArg (fun w => stdHermForm h 3 w (stdIsoA : Fin 3 → K)) hst
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ,
    stdHermForm_stdIsoA_stdIsoA, stdHermForm_stdIsoB_stdIsoA, smul_eq_mul, mul_one, mul_zero,
    zero_add, map_zero, LinearMap.zero_apply] at h2
  exact ⟨h.bar_eq_zero_iff.mp h1, h.bar_eq_zero_iff.mp h2⟩

theorem stdLinePlane_finrank (h : UnitaryFieldData 2 m K) :
    Module.finrank K ↥(stdLinePlane (K := K)) = 2 := by
  rw [stdLinePlane_eq_span_range, finrank_span_eq_card (linearIndependent_stdIso h)]
  simp

theorem stdLinePlane_form_separatingLeft (h : UnitaryFieldData 2 m K) :
    ((stdHermForm h 3).domRestrict₁₂ stdLinePlane stdLinePlane).SeparatingLeft := by
  intro x hx
  have hxa : stdHermForm h 3 (x : Fin 3 → K) (stdIsoA : Fin 3 → K) = 0 := by
    have := hx ⟨(stdIsoA : Fin 3 → K), stdPointA_le_stdLinePlane stdIsoA_mem_stdPointA⟩
    simpa [LinearMap.domRestrict₁₂_apply] using this
  have hxb : stdHermForm h 3 (x : Fin 3 → K) (stdIsoB : Fin 3 → K) = 0 := by
    have := hx ⟨(stdIsoB : Fin 3 → K), stdPointB_le_stdLinePlane stdIsoB_mem_stdPointB⟩
    simpa [LinearMap.domRestrict₁₂_apply] using this
  obtain ⟨s, t, hst⟩ := mem_stdLinePlane.mp x.2
  have e1 : h.bar t = 0 := by
    have := hxa
    rw [← hst] at this
    simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ,
      stdHermForm_stdIsoA_stdIsoA, stdHermForm_stdIsoB_stdIsoA, smul_eq_mul, mul_one, mul_zero,
      zero_add] using this
  have e2 : h.bar s = 0 := by
    have := hxb
    rw [← hst] at this
    simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ,
      stdHermForm_stdIsoA_stdIsoB, stdHermForm_stdIsoB_stdIsoB, smul_eq_mul, mul_one, mul_zero,
      add_zero] using this
  have hs : s = 0 := h.bar_eq_zero_iff.mp e2
  have ht : t = 0 := h.bar_eq_zero_iff.mp e1
  refine Subtype.ext ?_
  rw [← hst, hs, ht, zero_smul, zero_smul, add_zero]
  rfl

theorem exists_stdLinePlane_orthonormalBasis' (h : UnitaryFieldData 2 m K) :
    ∃ e : Module.Basis (Fin (Module.finrank K ↥(stdLinePlane (K := K)))) K
        ↥(stdLinePlane (K := K)),
      ∀ i j, (stdHermForm h 3) ((e i : ↥stdLinePlane) : Fin 3 → K)
        ((e j : ↥stdLinePlane) : Fin 3 → K) = if i = j then 1 else 0 := by
  haveI : FiniteDimensional K ↥(stdLinePlane (K := K)) := inferInstance
  have hsymm : ((stdHermForm h 3).domRestrict₁₂ stdLinePlane stdLinePlane).IsSymm :=
    ⟨fun x y => by
      rw [LinearMap.domRestrict₁₂_apply, LinearMap.domRestrict₁₂_apply]
      exact (stdHermForm_isSymm h 3).eq (x : Fin 3 → K) (y : Fin 3 → K)⟩
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis
    (M := ↥(stdLinePlane (K := K)))
    (B := (stdHermForm h 3).domRestrict₁₂ stdLinePlane stdLinePlane)
    hsymm (stdLinePlane_form_separatingLeft h)
  exact ⟨e, fun i j => by simpa [LinearMap.domRestrict₁₂_apply] using he i j⟩

theorem exists_stdLinePlane_orthonormalBasis (h : UnitaryFieldData 2 m K) :
    ∃ e : Module.Basis (Fin 2) K ↥(stdLinePlane (K := K)),
      ∀ i j, (stdHermForm h 3) ((e i : ↥stdLinePlane) : Fin 3 → K)
        ((e j : ↥stdLinePlane) : Fin 3 → K) = if i = j then 1 else 0 := by
  obtain ⟨e, he⟩ := exists_stdLinePlane_orthonormalBasis' h
  refine ⟨e.reindex (finCongr (stdLinePlane_finrank h)), fun i j => ?_⟩
  have h := he ((finCongr (stdLinePlane_finrank h)).symm i)
    ((finCongr (stdLinePlane_finrank h)).symm j)
  simpa [Module.Basis.reindex_apply] using h

@[expose] noncomputable def lineIso (e : Module.Basis (Fin 2) K ↥(stdLinePlane (K := K))) :
    (Fin 2 → K) →ₗ[K] (Fin 3 → K) :=
  (stdLinePlane (K := K)).subtype.comp
    (e.equivFun.symm : (Fin 2 → K) →ₗ[K] ↥(stdLinePlane (K := K)))

theorem lineIso_apply (e : Module.Basis (Fin 2) K ↥(stdLinePlane (K := K))) (u : Fin 2 → K) :
    lineIso e u = ((e.equivFun.symm u : ↥stdLinePlane) : Fin 3 → K) := rfl

theorem lineIso_mem (e : Module.Basis (Fin 2) K ↥(stdLinePlane (K := K))) (u : Fin 2 → K) :
    lineIso e u ∈ stdLinePlane (K := K) := (e.equivFun.symm u).2

theorem lineIso_sum (e : Module.Basis (Fin 2) K ↥(stdLinePlane (K := K))) (u : Fin 2 → K) :
    lineIso e u = ∑ i, u i • ((e i : ↥stdLinePlane) : Fin 3 → K) := by
  rw [lineIso_apply, Module.Basis.equivFun_symm_apply]
  simp

theorem lineIso_eq (e : Module.Basis (Fin 2) K ↥(stdLinePlane (K := K)))
    (w : ↥(stdLinePlane (K := K))) : lineIso e (e.equivFun w) = (w : Fin 3 → K) := by
  rw [lineIso_apply, LinearEquiv.symm_apply_apply]

theorem stdHermForm_orthonormal_sum (h : UnitaryFieldData 2 m K)
    {e : Fin 2 → Fin 3 → K}
    (he : ∀ i j, stdHermForm h 3 (e i) (e j) = if i = j then 1 else 0) (u v : Fin 2 → K) :
    stdHermForm h 3 (∑ i, u i • e i) (∑ i, v i • e i) =
      ∑ i, h.bar (u i) * v i := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ,
    he, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hji
    simp [hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem lineIso_isometry (h : UnitaryFieldData 2 m K)
    (e : Module.Basis (Fin 2) K ↥(stdLinePlane (K := K)))
    (he : ∀ i j, stdHermForm h 3 ((e i : ↥stdLinePlane) : Fin 3 → K)
      ((e j : ↥stdLinePlane) : Fin 3 → K) = if i = j then 1 else 0) (u v : Fin 2 → K) :
    stdHermForm h 3 (lineIso e u) (lineIso e v) = herm h.barEquiv u v := by
  rw [lineIso_sum, lineIso_sum, herm_def, stdHermForm_orthonormal_sum h he]
  simp only [UnitaryFieldData.barEquiv_apply]

theorem exists_mem_stdLineSU2_of_mem_T (h : UnitaryFieldData 2 m K)
    {φ : (Fin 2 → K) →ₗ[K] (Fin 3 → K)}
    (hφ : ∀ u v, stdHermForm h 3 (φ u) (φ v) = herm h.barEquiv u v)
    (hφW : ∀ u, φ u ∈ stdLinePlane (K := K))
    {g : SUid h.barEquiv 2} (hg : g ∈ T h.barEquiv 2) :
    ∃ g' ∈ stdLineSU2 h, ∀ u, g' • φ u = φ (g • u) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨a, c, ha, hc, hact⟩ := hg
      have hφa : stdHermForm h 3 (φ a) (φ a) = 0 := by rw [hφ, ha]
      have hc' : c ∈ h.traceZero := by
        rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace]
        exact hc
      obtain ⟨g', hg'mem, hg'lin⟩ :=
        exists_mem_stdLineSU2_hermTransvection h (hφW a) hφa hc'
      refine ⟨g', hg'mem, fun u => ?_⟩
      rw [unitarySU_smul_def h, hg'lin, hermTransvection_apply, hφ, hact u, map_add, map_smul]
  | one => exact ⟨1, (stdLineSU2 h).one_mem, fun u => by simp⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
      obtain ⟨g₁', h₁, e₁⟩ := ih₁
      obtain ⟨g₂', h₂, e₂⟩ := ih₂
      refine ⟨g₁' * g₂', Subgroup.mul_mem _ h₁ h₂, fun u => ?_⟩
      rw [mul_smul, mul_smul, e₂, e₁]
  | inv g _ ih =>
      obtain ⟨g', hg', e⟩ := ih
      refine ⟨g'⁻¹, Subgroup.inv_mem _ hg', fun u => ?_⟩
      rw [inv_smul_eq_iff, e (g⁻¹ • u), smul_inv_smul]

theorem stdNormC_ne_zero : (stdNormC : Fin 3 → K) ≠ 0 := by
  intro h0
  have := congrFun h0 0
  simp [stdNormC] at this

theorem stdLinePlane_orthogonal_stdNormC (h : UnitaryFieldData 2 m K) {w : Fin 3 → K}
    (hw : w ∈ stdLinePlane (K := K)) :
    stdHermForm h 3 w (stdNormC : Fin 3 → K) = 0 := by
  obtain ⟨s, t, rfl⟩ := mem_stdLinePlane.mp hw
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ,
    stdHermForm_stdIsoA_stdNormC, stdHermForm_stdIsoB_stdNormC, smul_eq_mul, mul_zero, add_zero]

theorem stdLinePlane_sup_stdNormC_eq_top (h : UnitaryFieldData 2 m K) :
    stdLinePlane (K := K) ⊔ Submodule.span K {(stdNormC : Fin 3 → K)} = ⊤ := by
  have hinf : stdLinePlane (K := K) ⊓ Submodule.span K {(stdNormC : Fin 3 → K)} = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx0 : x = 0 := by
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hx2
      have hc : stdHermForm h 3 (x : Fin 3 → K) (stdNormC : Fin 3 → K) = 0 :=
        stdLinePlane_orthogonal_stdNormC h hx1
      rw [← hlam] at hc
      simp only [map_smulₛₗ, LinearMap.smul_apply, stdHermForm_stdNormC_stdNormC, smul_eq_mul,
        mul_one] at hc
      have hlam0 : lam = 0 := h.bar_eq_zero_iff.mp hc
      rw [← hlam, hlam0, zero_smul]
    rw [hx0]
    exact Submodule.zero_mem _
  have hfin : Module.finrank K ↥(stdLinePlane (K := K) ⊔
      Submodule.span K {(stdNormC : Fin 3 → K)}) = 3 := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (stdLinePlane (K := K)) (Submodule.span K {(stdNormC : Fin 3 → K)})
    rw [hinf, finrank_bot, stdLinePlane_finrank h,
      finrank_span_singleton stdNormC_ne_zero] at hsup
    omega
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hfin, Module.finrank_fin_fun]

theorem exists_stdLinePlane_add_stdNormC (h : UnitaryFieldData 2 m K) (v : Fin 3 → K) :
    ∃ w ∈ stdLinePlane (K := K), ∃ lam : K, v = w + lam • (stdNormC : Fin 3 → K) := by
  have hv : v ∈ stdLinePlane (K := K) ⊔ Submodule.span K {(stdNormC : Fin 3 → K)} := by
    rw [stdLinePlane_sup_stdNormC_eq_top h]
    exact Submodule.mem_top
  obtain ⟨w, hw, u, hu, hwu⟩ := Submodule.mem_sup.mp hv
  obtain ⟨lam, rfl⟩ := Submodule.mem_span_singleton.mp hu
  exact ⟨w, hw, lam, hwu.symm⟩

theorem stdLineSU2_smul_stdNormC (h : UnitaryFieldData 2 m K) {g : unitarySU 2 m K 3}
    (hg : g ∈ stdLineSU2 h) : g • (stdNormC : Fin 3 → K) = stdNormC := by
  have hfixA : isotropicTransvectionGroup h 3 stdPointA ≤
      MulAction.stabilizer (unitarySU 2 m K 3) (stdNormC : Fin 3 → K) := by
    rw [stdPointA]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨a, ha, c, hc, hx⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, unitarySU_smul_def h, hx,
      hermTransvection_apply]
    have hzero : stdHermForm h 3 a (stdNormC : Fin 3 → K) = 0 := by
      refine stdLinePlane_orthogonal_stdNormC h ?_
      exact stdPointA_le_stdLinePlane ha
    rw [hzero, mul_zero, zero_smul, add_zero]
  have hfixB : isotropicTransvectionGroup h 3 stdPointB ≤
      MulAction.stabilizer (unitarySU 2 m K 3) (stdNormC : Fin 3 → K) := by
    rw [stdPointB]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨a, ha, c, hc, hx⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, unitarySU_smul_def h, hx,
      hermTransvection_apply]
    have hzero : stdHermForm h 3 a (stdNormC : Fin 3 → K) = 0 := by
      refine stdLinePlane_orthogonal_stdNormC h ?_
      exact stdPointB_le_stdLinePlane ha
    rw [hzero, mul_zero, zero_smul, add_zero]
  exact sup_le hfixA hfixB hg

theorem exists_norm_one_stdLinePlane_of_not_le (h : UnitaryFieldData 2 m K)
    {z : Submodule K (Fin 3 → K)} (hz : z ∈ isotropicLines h 3)
    (hzW : ¬ z ≤ stdLinePlane (K := K)) :
    ∃ w ∈ stdLinePlane (K := K), stdHermForm h 3 w w = 1 ∧
      z = Submodule.span K {(w : Fin 3 → K) + stdNormC} := by
  haveI := h.charP
  obtain ⟨v, hv0, hviso, hzv⟩ := exists_eq_span_of_mem_isotropicLines hz
  obtain ⟨w₀, hw₀, lam, hdecomp⟩ := exists_stdLinePlane_add_stdNormC h v
  have hlam : lam ≠ 0 := by
    rintro rfl
    apply hzW
    rw [hzv, hdecomp, zero_smul, add_zero]
    exact Submodule.span_le.mpr (by
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hw₀)
  have hwc : stdHermForm h 3 w₀ (stdNormC : Fin 3 → K) = 0 :=
    stdLinePlane_orthogonal_stdNormC h hw₀
  have hcw : stdHermForm h 3 (stdNormC : Fin 3 → K) w₀ = 0 := by
    rw [← (stdHermForm_isSymm h 3).eq w₀ (stdNormC : Fin 3 → K), hwc, map_zero]
  have hnorm : stdHermForm h 3 w₀ w₀ = h.norm lam := by
    have h1 : stdHermForm h 3 (w₀ + lam • (stdNormC : Fin 3 → K))
        (w₀ + lam • (stdNormC : Fin 3 → K)) = 0 := by
      rw [← hdecomp]
      exact hviso
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ,
      hwc, hcw, stdHermForm_stdNormC_stdNormC, smul_eq_mul, mul_one, mul_zero, zero_add,
      add_zero, UnitaryFieldData.norm] at h1
    have h3 : stdHermForm h 3 w₀ w₀ = lam * h.bar lam := by
      have := eq_neg_of_add_eq_zero_right h1
      simpa using this.symm
    rw [h3, UnitaryFieldData.norm]
  refine ⟨lam⁻¹ • w₀, Submodule.smul_mem _ _ hw₀, ?_, ?_⟩
  · have hbar : h.bar lam ≠ 0 := fun h0 => hlam (h.bar_eq_zero_iff.mp h0)
    rw [stdHermForm_norm_smul, hnorm, UnitaryFieldData.norm, UnitaryFieldData.norm]
    simp only [map_inv₀]
    field_simp
  · rw [hzv, hdecomp]
    have h2 : lam⁻¹ • (w₀ + lam • (stdNormC : Fin 3 → K)) =
        lam⁻¹ • w₀ + stdNormC := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    rw [← h2, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hlam))]

theorem exists_mem_SUid_two_smul_eq (h : UnitaryFieldData 2 m K) {y y' : Fin 2 → K}
    (hy : herm h.barEquiv y y = 1) (hy' : herm h.barEquiv y' y' = 1) :
    ∃ t : SUid h.barEquiv 2, t ∈ T h.barEquiv 2 ∧ t • y = y' := by
  have hσ := h.isUnitaryInvolution_barEquiv
  have hsingle : ∀ i : Fin 2,
      herm h.barEquiv (Pi.single i (1 : K)) (Pi.single i (1 : K)) = 1 := by
    intro i
    rw [herm_fin_two]
    fin_cases i <;> simp
  have h01 : herm h.barEquiv (Pi.single (0 : Fin 2) (1 : K))
      (Pi.single (1 : Fin 2) (1 : K)) = 0 := by
    rw [herm_fin_two]
    simp
  have hyeq : y = y 0 • (Pi.single (0 : Fin 2) (1 : K)) +
      y 1 • (Pi.single (1 : Fin 2) (1 : K)) := by
    funext i
    fin_cases i <;> simp
  have hyeq' : y' = y' 0 • (Pi.single (0 : Fin 2) (1 : K)) +
      y' 1 • (Pi.single (1 : Fin 2) (1 : K)) := by
    funext i
    fin_cases i <;> simp
  obtain ⟨t₁, ht₁, h₁⟩ := exists_mem_T_of_orthonormal (σ := h.barEquiv) hσ
    (hsingle 0) (hsingle 1) h01 (y 0) (y 1) (by rw [← hyeq]; exact hy)
  obtain ⟨t₂, ht₂, h₂⟩ := exists_mem_T_of_orthonormal (σ := h.barEquiv) hσ
    (hsingle 0) (hsingle 1) h01 (y' 0) (y' 1) (by rw [← hyeq']; exact hy')
  rw [← hyeq] at h₁
  rw [← hyeq'] at h₂
  refine ⟨t₂ * t₁⁻¹, ?_, ?_⟩
  · rw [T_two_eq_top hσ]
    exact Subgroup.mem_top _
  · rw [mul_smul]
    have hinv : t₁⁻¹ • y = Pi.single 0 (1 : K) := by
      rw [← h₁, inv_smul_smul]
    rw [hinv, h₂]

theorem exists_mem_stdLineSU2_smul_eq (h : UnitaryFieldData 2 m K)
    {z z' : Submodule K (Fin 3 → K)} (hz : z ∈ isotropicLines h 3)
    (hz' : z' ∈ isotropicLines h 3) (hzW : ¬ z ≤ stdLinePlane (K := K))
    (hzW' : ¬ z' ≤ stdLinePlane (K := K)) :
    ∃ g ∈ stdLineSU2 h, g • z = z' := by
  obtain ⟨e, he⟩ := exists_stdLinePlane_orthonormalBasis h
  obtain ⟨w, hw, hwn, hzeq⟩ := exists_norm_one_stdLinePlane_of_not_le h hz hzW
  obtain ⟨w', hw', hw'n, hz'eq⟩ := exists_norm_one_stdLinePlane_of_not_le h hz' hzW'
  set y : Fin 2 → K := e.equivFun ⟨w, hw⟩ with hy
  set y' : Fin 2 → K := e.equivFun ⟨w', hw'⟩ with hy'
  have hiy : herm h.barEquiv y y = 1 := by
    rw [← lineIso_isometry h e he y y,
      show lineIso e y = (w : Fin 3 → K) from lineIso_eq e ⟨w, hw⟩]
    exact hwn
  have hiy' : herm h.barEquiv y' y' = 1 := by
    rw [← lineIso_isometry h e he y' y',
      show lineIso e y' = (w' : Fin 3 → K) from lineIso_eq e ⟨w', hw'⟩]
    exact hw'n
  obtain ⟨t, ht, hty⟩ := exists_mem_SUid_two_smul_eq h hiy hiy'
  obtain ⟨g, hg, hge⟩ :=
    exists_mem_stdLineSU2_of_mem_T h (lineIso_isometry h e he) (lineIso_mem e) ht
  refine ⟨g, hg, ?_⟩
  have hgw : g • (w : Fin 3 → K) = w' := by
    have h1 := hge y
    rw [show lineIso e y = (w : Fin 3 → K) from lineIso_eq e ⟨w, hw⟩, hty,
      show lineIso e y' = (w' : Fin 3 → K) from lineIso_eq e ⟨w', hw'⟩] at h1
    exact h1
  rw [hzeq, hz'eq, Subgroup.smul_def, smul_eq_map, Submodule.map_span, Set.image_singleton]
  congr 1
  rw [← unitarySU_smul_def h, smul_add, hgw, stdLineSU2_smul_stdNormC h hg]

theorem stdLinePlane_eq_stdPointA_sup_stdPointB :
    stdLinePlane (K := K) = stdPointA (K := K) ⊔ stdPointB (K := K) := by
  rw [stdLinePlane, stdPointA, stdPointB, ← Submodule.span_union]
  congr 1

theorem unitarySU_smul_sup (h : UnitaryFieldData 2 m K) (g : unitarySU 2 m K 3)
    (A B : Submodule K (Fin 3 → K)) : g • (A ⊔ B) = g • A ⊔ g • B := by
  simp only [Subgroup.smul_def, smul_eq_map, Submodule.map_sup]

theorem unitarySU_smul_mono (h : UnitaryFieldData 2 m K) (g : unitarySU 2 m K 3)
    {A B : Submodule K (Fin 3 → K)} (hAB : A ≤ B) : g • A ≤ g • B := by
  simp only [Subgroup.smul_def, smul_eq_map]
  exact Submodule.map_mono hAB

theorem isotropicTransvectionGroup_le_stdLineSU2 (h : UnitaryFieldData 2 m K)
    {z : Submodule K (Fin 3 → K)} (hz : z ∈ isotropicLines h 3)
    (hzle : z ≤ stdLinePlane (K := K)) :
    isotropicTransvectionGroup h 3 z ≤ stdLineSU2 h := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨a, ha, c, hc, hg⟩
  have hha : stdHermForm h 3 a a = 0 := (mem_isotropicLines.mp hz).2 a ha
  obtain ⟨g', hg'mem, hg'lin⟩ :=
    exists_mem_stdLineSU2_hermTransvection h (hzle ha) hha hc
  have heq : g = g' := unitarySU_ext_mulVecLin (hg.trans hg'lin.symm)
  rwa [heq]

theorem sup_stdLineSU2_isotropicTransvectionGroup_eq_top (h : UnitaryFieldData 2 m K)
    (hm : 2 ≤ m) {z : Submodule K (Fin 3 → K)} (hz : z ∈ isotropicLines h 3)
    (hzW : ¬ z ≤ stdLinePlane (K := K)) :
    stdLineSU2 h ⊔ isotropicTransvectionGroup h 3 z = ⊤ := by
  have hnq : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := by
    intro hEq
    have h2 : 2 ^ m = 2 := congrArg Prod.snd hEq
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hgen := unitary_point_normal_generation h (le_refl 3) hnq
    (stdPointA_mem_isotropicLines h)
  rw [eq_top_iff, ← hgen]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x hx
  obtain ⟨g, hxg⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hgL, hmap, -, -⟩ := unitary_point_conjugation h g (stdPointA_mem_isotropicLines h)
  have hx' : x ∈ isotropicTransvectionGroup h 3 (g • stdPointA) := by
    rw [← hmap]
    exact hxg
  by_cases hle : g • stdPointA ≤ stdLinePlane (K := K)
  · exact Subgroup.mem_sup_left (isotropicTransvectionGroup_le_stdLineSU2 h hgL hle hx')
  · obtain ⟨l, hl, hlsmul⟩ := exists_mem_stdLineSU2_smul_eq h hz hgL hzW hle
    have hconj := (unitary_point_conjugation h l hz).2.1
    rw [hlsmul] at hconj
    have hle' : isotropicTransvectionGroup h 3 (g • stdPointA) ≤
        stdLineSU2 h ⊔ isotropicTransvectionGroup h 3 z := by
      rw [← hconj]
      rintro y hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
        (Subgroup.mem_sup_right hy')) (Subgroup.inv_mem _ (Subgroup.mem_sup_left hl))
    exact hle' hx'

end CFSG.ClassicalGroups.UnitaryFlag
