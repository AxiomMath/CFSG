module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAFixSpace
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCLift

public section

namespace CFSG.SeitzReduction.OmegaPilot

open QuadraticMap
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_conj eichler_smul_left
  eichler_mul eichler_inv eichler_apply_of_polar_eq_zero)

section Nil

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
  (hNN : ∀ v, N (N v) = 0)

include hadj hNN in
theorem eichler_apply_of_mem_range_of_mem_ker {u m w : Fin d → K} (hu : u ∈ LinearMap.range N)
    (hm : m ∈ LinearMap.ker N) (hw : w ∈ LinearMap.range N) : eichler Q u m w = w :=
  eichler_apply_of_polar_eq_zero (polar_mem_range_ker N hadj hw (range_le_ker N hNN hu))
    (polar_mem_range_ker N hadj hw hm)

include hadj in
theorem eichler_sub_mem_range_of_mem_ker {u m v : Fin d → K} (hu : u ∈ LinearMap.range N)
    (hQu : Q u = 0) (hm : m ∈ LinearMap.ker N) (hv : v ∈ LinearMap.ker N) :
    eichler Q u m v - v ∈ LinearMap.range N := by
  have hvu : polar Q v u = 0 := by
    rw [polar_comm]
    exact polar_mem_range_ker N hadj hu hv
  rw [eichler_apply hQu (polar_mem_range_ker N hadj hu hm), hvu, zero_smul, add_zero, mul_zero,
    add_zero, sub_sub_cancel_left]
  exact (LinearMap.range N).neg_mem ((LinearMap.range N).smul_mem _ hu)

include hadj hNN in
theorem eichler_comm_nil {u m : Fin d → K} (hu : u ∈ LinearMap.range N) (hQu : Q u = 0)
    (hm : m ∈ LinearMap.ker N) (v : Fin d → K) :
    eichler Q u m (N v) = N (eichler Q u m v) := by
  rw [eichler_apply_of_mem_range_of_mem_ker N hadj hNN hu hm (LinearMap.mem_range_self N v),
    eichler_apply hQu (polar_mem_range_ker N hadj hu hm), map_sub, map_add, map_smul, map_smul,
    LinearMap.mem_ker.mp hm, LinearMap.mem_ker.mp (range_le_ker N hNN hu), smul_zero, smul_zero,
    add_zero, sub_zero]

end Nil

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] in
theorem eichlerBar_mem_autFixSubgroup_of_nil (hn : 3 ≤ n)
    (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (s : matrixIsometries (coordinateQuadPlus n K))
    (hss : s * s = 1) {u m : Fin (2 * n) → K} (hu : u ∈ LinearMap.range (sNil s.val))
    (hQu : coordinateQuadPlus n K u = 0) (hm : m ∈ LinearMap.ker (sNil s.val)) :
    eichlerBar hn u m ∈ autFixSubgroup (isometryConjugationHom _ s) := by
  refine mem_autFixSubgroup_of_commute hQ s fun v => ?_
  have hs : ∀ w, matrixLinearEquiv s.val w = sNil s.val w + w := fun w => by
    rw [sNil_apply, sub_add_cancel]
  rw [projLift_eichlerBar, hs, hs, map_add,
    eichler_comm_nil (sNil s.val) (polar_sNil_left s hss) (sNil_sNil (congrArg Subtype.val hss))
      hu hQu hm]

omit [Finite K] in
theorem exists_core_eichler (hn : 3 ≤ n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hx : x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)))
    {u m : Fin (2 * n) → K} (hu : u ∈ LinearMap.range (sNil s.val))
    (hQu : coordinateQuadPlus n K u = 0) (hm : m ∈ LinearMap.ker (sNil s.val)) {a : K}
    (hxu : projLift hQ x u = a • u) (hxm : projLift hQ x m = m) :
    ∃ y ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
      projLift hQ y = eichler (coordinateQuadPlus n K) u (m - a • m) := by
  set e := eichlerBar (K := K) hn u m with he
  have heC := eichlerBar_mem_autFixSubgroup_of_nil hn hQ s hss hu hQu hm
  have hum : polar (coordinateQuadPlus n K) u m = 0 :=
    polar_mem_range_ker (sNil s.val) (polar_sNil_left s hss) hu hm
  have huam : polar (coordinateQuadPlus n K) u (a • m) = 0 := by
    rw [polar_smul_right, hum, smul_zero]
  refine ⟨e * x * e⁻¹ * x⁻¹, mul_mem (conj_mem_perfectCore' heC hx) (inv_mem hx), ?_⟩
  rw [projLift_mul, projLift_mul, projLift_mul, projLift_inv, projLift_inv, he,
    projLift_eichlerBar]
  set L := projLift hQ x with hL
  have hLO : (L : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K) :=
    Subgroup.commutator_le_self _ (projLift_mem_orthDerived hQ x)
  have hconj : L * eichler (coordinateQuadPlus n K) u m * L⁻¹ =
      eichler (coordinateQuadPlus n K) u (a • m) := by
    rw [eichler_conj hLO, hxu, hxm, eichler_smul_left]
  calc eichler (coordinateQuadPlus n K) u m * L * (eichler (coordinateQuadPlus n K) u m)⁻¹ * L⁻¹
      = eichler (coordinateQuadPlus n K) u m *
        (L * eichler (coordinateQuadPlus n K) u m * L⁻¹)⁻¹ := by group
    _ = eichler (coordinateQuadPlus n K) u m *
        eichler (coordinateQuadPlus n K) u (-(a • m)) := by
        rw [hconj, eichler_inv huam]
    _ = eichler (coordinateQuadPlus n K) u (m - a • m) := by
        rw [eichler_mul hum (by rw [polar_neg_right, huam, neg_zero]), sub_eq_add_neg]

omit [Finite K] in
theorem exists_core_eichler_radical (hn : 3 ≤ n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hx : x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)))
    {u m : Fin (2 * n) → K} (hu : u ∈ LinearMap.range (sNil s.val))
    (hQu : coordinateQuadPlus n K u = 0) (hm : m ∈ LinearMap.ker (sNil s.val)) {a : K}
    (hxu : projLift hQ x u = a • u) (hxm : projLift hQ x m = m) :
    ∃ y ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
      projLift hQ y = eichler (coordinateQuadPlus n K) u (m - a • m) ∧
      (∀ w ∈ LinearMap.range (sNil s.val), projLift hQ y w = w) ∧
      ∀ v ∈ LinearMap.ker (sNil s.val), projLift hQ y v - v ∈ LinearMap.range (sNil s.val) := by
  obtain ⟨y, hy, hyl⟩ := exists_core_eichler hn hQ s hss hx hu hQu hm hxu hxm
  have hm' : m - a • m ∈ LinearMap.ker (sNil s.val) :=
    sub_mem hm ((LinearMap.ker (sNil s.val)).smul_mem a hm)
  refine ⟨y, hy, hyl, fun w hw => ?_, fun v hv => ?_⟩
  · rw [hyl]
    exact eichler_apply_of_mem_range_of_mem_ker (sNil s.val) (polar_sNil_left s hss)
      (sNil_sNil (congrArg Subtype.val hss)) hu hm' hw
  · rw [hyl]
    exact eichler_sub_mem_range_of_mem_ker (sNil s.val) (polar_sNil_left s hss) hu hQu hm' hv

theorem exists_core_move (hn : 3 ≤ n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1) (hq4 : 4 ≤ Nat.card K)
    (U C : Submodule K (Fin (2 * n) → K)) (hUW : U ≤ LinearMap.range (sNil s.val))
    (hQU : ∀ u ∈ U, coordinateQuadPlus n K u = 0) (hCK : C ≤ LinearMap.ker (sNil s.val))
    (hdisj : U ⊓ C = ⊥) (hsup : U ⊔ C = LinearMap.ker (sNil s.val)) (hU0 : U ≠ ⊥)
    {y₀ : Fin (2 * n) → K} (hy₀ : y₀ ∈ C) (hQy₀ : coordinateQuadPlus n K y₀ = 1)
    (htor : ∀ u ∈ U, u ≠ 0 → ∀ a : Kˣ,
      ∃ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        projLift hQ x u = (a : K) • u ∧ ∀ c ∈ C, projLift hQ x c = c)
    {v : Fin (2 * n) → K} (hv : v ∉ LinearMap.range (sNil s.val)) :
    ∃ r ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
      (∀ w ∈ LinearMap.range (sNil s.val), projLift hQ r w = w) ∧
      (∀ v' ∈ LinearMap.ker (sNil s.val),
        projLift hQ r v' - v' ∈ LinearMap.range (sNil s.val)) ∧
      projLift hQ r v - v ∉ C := by
  obtain ⟨a, ha⟩ := exists_unit_ne_one (K := K) hq4
  have ha1 : (1 - (a : K)) ≠ 0 := fun h => ha (Units.ext (sub_eq_zero.mp h).symm)
  have hUC : ∀ z ∈ U, z ∈ C → z = 0 := fun z hzU hzC => by
    have hz : z ∈ U ⊓ C := Submodule.mem_inf.mpr ⟨hzU, hzC⟩
    rwa [hdisj, Submodule.mem_bot] at hz
  have key : ∀ u ∈ U, u ≠ 0 → ∀ m ∈ C,
      ∃ r ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        projLift hQ r = eichler (coordinateQuadPlus n K) u (m - (a : K) • m) ∧
        (∀ w ∈ LinearMap.range (sNil s.val), projLift hQ r w = w) ∧
        ∀ v' ∈ LinearMap.ker (sNil s.val),
          projLift hQ r v' - v' ∈ LinearMap.range (sNil s.val) := by
    intro u hu hu0 m hm
    obtain ⟨x, hx, hxu, hxC⟩ := htor u hu hu0 a
    exact exists_core_eichler_radical hn hQ s hss hx (hUW hu) (hQU u hu) (hCK hm) hxu (hxC m hm)
  have hpol : ∀ u ∈ U, ∀ m ∈ C,
      polar (coordinateQuadPlus n K) u (m - (a : K) • m) = 0 := fun u hu m hm =>
    polar_mem_range_ker (sNil s.val) (polar_sNil_left s hss) (hUW hu)
      (hCK (sub_mem hm (C.smul_mem _ hm)))
  obtain ⟨k, hk, hvk⟩ :
      ∃ k ∈ LinearMap.ker (sNil s.val), polar (coordinateQuadPlus n K) v k ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hv (mem_range_of_forall_polar (sNil s.val) (polar_sNil_left s hss)
      (regular_coordinateQuadPlus n K hn).1 fun z hz => by
        rw [polar_comm]
        exact hno z hz)
  rw [← hsup] at hk
  obtain ⟨u₀, hu₀, c₀, hc₀, rfl⟩ := Submodule.mem_sup.mp hk
  by_cases hU : ∃ u₁ ∈ U, polar (coordinateQuadPlus n K) v u₁ ≠ 0
  · obtain ⟨u₁, hu₁, hvu₁⟩ := hU
    have hu₁0 : u₁ ≠ 0 := by
      rintro rfl
      exact hvu₁ (polar_zero_right _ _)
    obtain ⟨t, ht0, ht⟩ : ∃ t : K, t ≠ 0 ∧ polar (coordinateQuadPlus n K) v y₀ +
        (1 - (a : K)) * t * polar (coordinateQuadPlus n K) v u₁ ≠ 0 := by
      by_cases h : polar (coordinateQuadPlus n K) v y₀ +
          (1 - (a : K)) * 1 * polar (coordinateQuadPlus n K) v u₁ = 0
      · refine ⟨a, a.ne_zero, fun h' => ?_⟩
        have h2 : (1 - (a : K)) * ((a : K) - 1) * polar (coordinateQuadPlus n K) v u₁ = 0 := by
          linear_combination h' - h
        rcases mul_eq_zero.mp h2 with h3 | h3
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact ha1 h4
          · exact ha (Units.ext (sub_eq_zero.mp h4))
        · exact hvu₁ h3
      · exact ⟨1, one_ne_zero, h⟩
    have hu : t • u₁ ∈ U := U.smul_mem t hu₁
    obtain ⟨r, hr, hrl, hW, hK⟩ := key (t • u₁) hu (smul_ne_zero ht0 hu₁0) y₀ hy₀
    refine ⟨r, hr, hW, hK, fun hC => ?_⟩
    rw [hrl, eichler_apply (hQU _ hu) (hpol _ hu y₀ hy₀)] at hC
    set m' := y₀ - (a : K) • y₀ with hm'
    set c := polar (coordinateQuadPlus n K) v m' +
      coordinateQuadPlus n K m' * polar (coordinateQuadPlus n K) v (t • u₁) with hc
    have hA : polar (coordinateQuadPlus n K) v (t • u₁) • m' ∈ C :=
      C.smul_mem _ (sub_mem hy₀ (C.smul_mem _ hy₀))
    have hB : c • (t • u₁) ∈ C := by
      have h := sub_mem hA hC
      convert h using 1
      abel
    have h0 := hUC _ (U.smul_mem c hu) hB
    rw [smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · have hQm' : coordinateQuadPlus n K m' = (1 - (a : K)) * (1 - (a : K)) := by
        rw [hm', show y₀ - (a : K) • y₀ = (1 - (a : K)) • y₀ by rw [sub_smul, one_smul],
          QuadraticMap.map_smul, hQy₀, smul_eq_mul, mul_one]
      rw [hc, hQm', hm', polar_sub_right, polar_smul_right, polar_smul_right, smul_eq_mul,
        smul_eq_mul] at h0
      exact mul_ne_zero ha1 ht (by linear_combination h0)
    · exact smul_ne_zero ht0 hu₁0 h0
  · push Not at hU
    have hvc₀ : polar (coordinateQuadPlus n K) v c₀ ≠ 0 := by
      rwa [polar_add_right, hU u₀ hu₀, zero_add] at hvk
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨r, hr, hrl, hW, hK⟩ := key u hu hu0 c₀ hc₀
    refine ⟨r, hr, hW, hK, fun hC => ?_⟩
    rw [hrl, eichler_apply (hQU u hu) (hpol u hu c₀ hc₀), hU u hu, zero_smul, add_zero,
      mul_zero, add_zero, sub_sub_cancel_left] at hC
    have hC' := C.neg_mem hC
    rw [neg_neg] at hC'
    have h0 := hUC _ (U.smul_mem _ hu) hC'
    rw [smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · rw [polar_sub_right, polar_smul_right, smul_eq_mul] at h0
      exact mul_ne_zero ha1 hvc₀ (by linear_combination h0)
    · exact hu0 h0

end Core

end CFSG.SeitzReduction.OmegaPilot
