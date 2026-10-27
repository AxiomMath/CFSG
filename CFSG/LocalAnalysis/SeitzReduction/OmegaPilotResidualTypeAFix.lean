module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeASp

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le normalizer_le_normalizer_perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply commutator_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_conj eichler_smul_left
  eichler_mul
  eichler_inv eichler_apply_of_polar_eq_zero eichler_mem_elementaryGroup)

section Generic

variable {K : Type} [Field K] {d : ℕ}

theorem kerQuotHom_eq_one_of [CharP K 2] {Q : QuadraticForm K (Fin d → K)} (hQ : ∃ v, Q v ≠ 0)
    {X : Subgroup (matrixProjectiveDerived Q)} (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hXN : ∀ x ∈ X, ∀ v, projLift hQ x (N v) = N (projLift hQ x v)) (x : ↥X)
    (h : ∀ v ∈ LinearMap.ker N, projLift hQ (x : matrixProjectiveDerived Q) v - v ∈
      LinearMap.range N) : kerQuotHom hQ X N hXN x = 1 := by
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun z => ?_
  change kerQuotMap N _ (hXN x x.2) (Submodule.Quotient.mk z) = Submodule.Quotient.mk z
  rw [kerQuotMap_mk', Submodule.Quotient.eq]
  change ((⟨projLift hQ (x : matrixProjectiveDerived Q) z, _⟩ - z : LinearMap.ker N) :
    Fin d → K) ∈ LinearMap.range N
  exact h z z.2

theorem rangeRestrictHom_eq_one_of [CharP K 2] {Q : QuadraticForm K (Fin d → K)}
    (hQ : ∃ v, Q v ≠ 0) {X : Subgroup (matrixProjectiveDerived Q)}
    (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hXN : ∀ x ∈ X, ∀ v, projLift hQ x (N v) = N (projLift hQ x v)) (x : ↥X)
    (h : ∀ w ∈ LinearMap.range N, projLift hQ (x : matrixProjectiveDerived Q) w = w) :
    rangeRestrictHom hQ X N hXN x = 1 :=
  LinearMap.ext fun w => Subtype.ext (h w w.2)

theorem conj_mem_perfectCore' {G : Type*} [Group G] {H : Subgroup G} {c p : G} (hc : c ∈ H)
    (hp : p ∈ perfectCore H) : c * p * c⁻¹ ∈ perfectCore H :=
  (Subgroup.mem_normalizer_iff.mp ((Subgroup.le_normalizer.trans
    (normalizer_le_normalizer_perfectCore H)) hc) p).mp hp

end Generic

variable {K : Type} [Field K] {n ℓ : ℕ}

theorem polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp {u m : Fin (2 * n) → K}
    (hu : u ∈ lowSpan K n ℓ) (hm : m ∈ lowPerp K n ℓ) :
    polar (coordinateQuadPlus n K) u m = 0 := by
  rw [polar_coordinateQuadPlus]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [(hu i).1, zero_mul, add_zero]
  by_cases hi : i.val < ℓ
  · rw [hm i hi, mul_zero]
  · rw [(hu i).2 (by omega), zero_mul]

theorem polar_eq_zero_of_mem_lowPerp_of_mem_lowSpan {u m : Fin (2 * n) → K}
    (hm : m ∈ lowPerp K n ℓ) (hu : u ∈ lowSpan K n ℓ) :
    polar (coordinateQuadPlus n K) m u = 0 := by
  rw [polar_comm]
  exact polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hu hm

theorem eichler_apply_of_mem_lowSpan {u m w : Fin (2 * n) → K} (hu : u ∈ lowSpan K n ℓ)
    (hm : m ∈ lowPerp K n ℓ) (hw : w ∈ lowSpan K n ℓ) :
    eichler (coordinateQuadPlus n K) u m w = w :=
  eichler_apply_of_polar_eq_zero
    (polar_eq_zero_of_mem_lowPerp_of_mem_lowSpan (lowSpan_le_lowPerp ℓ hw) hu)
    (polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hw hm)

theorem eichler_sub_mem_lowSpan {u m v : Fin (2 * n) → K} (hu : u ∈ lowSpan K n ℓ)
    (hm : m ∈ lowPerp K n ℓ) (hv : v ∈ lowPerp K n ℓ) :
    eichler (coordinateQuadPlus n K) u m v - v ∈ lowSpan K n ℓ := by
  rw [eichler_apply (coordinateQuadPlus_lowSpan hu)
      (polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hu hm),
    polar_eq_zero_of_mem_lowPerp_of_mem_lowSpan hv hu, zero_smul, add_zero, mul_zero, add_zero,
    sub_sub_cancel_left]
  exact (lowSpan K n ℓ).neg_mem ((lowSpan K n ℓ).smul_mem _ hu)

variable (P : LowPairing n ℓ)

theorem eichler_lowNil {u m : Fin (2 * n) → K} (hu : u ∈ lowSpan K n ℓ) (hm : m ∈ lowPerp K n ℓ)
    (v : Fin (2 * n) → K) :
    eichler (coordinateQuadPlus n K) u m (lowNil P v) =
      lowNil P (eichler (coordinateQuadPlus n K) u m v) := by
  rw [eichler_apply_of_mem_lowSpan hu hm (lowNil_mem_lowSpan P v),
    eichler_apply (coordinateQuadPlus_lowSpan hu)
      (polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hu hm),
    map_sub, map_add, map_smul, map_smul, lowNil_of_mem_lowPerp P hm,
    lowNil_of_mem_lowPerp P (lowSpan_le_lowPerp ℓ hu), smul_zero, smul_zero, add_zero, sub_zero]

section Core

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem eichler_mem_orthDerived_plus (hn : 3 ≤ n) (u w : Fin (2 * n) → K) :
    eichler (coordinateQuadPlus n K) u w ∈ orthDerived (coordinateQuadPlus n K) := by
  rw [show orthDerived (coordinateQuadPlus n K) =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (coordinateQuadPlus n K) from
    commutator_coordinateQuadPlus n K hn]
  exact eichler_mem_elementaryGroup (coordinateQuadPlus n K) u w

@[expose] noncomputable def eichlerBar (hn : 3 ≤ n) (u w : Fin (2 * n) → K) :
    matrixProjectiveDerived (coordinateQuadPlus n K) :=
  projHom _ ⟨eichler (coordinateQuadPlus n K) u w, eichler_mem_orthDerived_plus hn u w⟩

omit [Finite K] in
theorem projLift_eichlerBar (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (hn : 3 ≤ n)
    (u w : Fin (2 * n) → K) :
    projLift hQ (eichlerBar hn u w) = eichler (coordinateQuadPlus n K) u w :=
  projLift_projHom hQ _

omit [Finite K] in
theorem eichlerBar_mem_autFixSubgroup (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (hn : 3 ≤ n)
    {u m : Fin (2 * n) → K} (hu : u ∈ lowSpan K n ℓ) (hm : m ∈ lowPerp K n ℓ) :
    eichlerBar hn u m ∈ autFixSubgroup (isometryConjugationHom _ (lowRep P)) := by
  refine mem_autFixSubgroup_of_commute hQ (lowRep P) fun v => ?_
  rw [projLift_eichlerBar]
  change eichler _ u m (matrixLinearEquiv (lowRepGL P) v) =
    matrixLinearEquiv (lowRepGL P) (eichler _ u m v)
  rw [matrixLinearEquiv_lowRepGL, matrixLinearEquiv_lowRepGL, map_add, eichler_lowNil P hu hm]

omit [Finite K] in
theorem exists_mem_R_projLift_eq_eichler (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (hn : 3 ≤ n)
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)} (hx : x ∈ typeACore K P)
    {u m : Fin (2 * n) → K} (hu : u ∈ lowSpan K n ℓ) (hm : m ∈ lowPerp K n ℓ) {a : K}
    (hxu : projLift hQ x u = a • u) (hxm : projLift hQ x m = m) :
    ∃ y ∈ (rangeRestrictHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ⊓
      (kerQuotHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker,
      projLift hQ ((y : typeACore K P) : matrixProjectiveDerived (coordinateQuadPlus n K)) =
        eichler (coordinateQuadPlus n K) u (m - a • m) := by
  set e := eichlerBar (K := K) hn u m with he
  have heC := eichlerBar_mem_autFixSubgroup P hQ hn hu hm
  have hy : e * x * e⁻¹ * x⁻¹ ∈ typeACore K P :=
    mul_mem (conj_mem_perfectCore' heC hx) (inv_mem hx)
  have hum : polar (coordinateQuadPlus n K) u m = 0 :=
    polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hu hm
  have huam : polar (coordinateQuadPlus n K) u (a • m) = 0 := by
    rw [polar_smul_right, hum, smul_zero]
  have hlift : projLift hQ (e * x * e⁻¹ * x⁻¹) =
      eichler (coordinateQuadPlus n K) u (m - a • m) := by
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
      _ = eichler (coordinateQuadPlus n K) u m * eichler (coordinateQuadPlus n K) u (-(a • m)) := by
          rw [hconj, eichler_inv huam]
      _ = eichler (coordinateQuadPlus n K) u (m - a • m) := by
          rw [eichler_mul hum (by rw [polar_neg_right, huam, neg_zero]), sub_eq_add_neg]
  have hm' : m - a • m ∈ lowPerp K n ℓ := sub_mem hm ((lowPerp K n ℓ).smul_mem _ hm)
  refine ⟨⟨_, hy⟩, Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr ?_, MonoidHom.mem_ker.mpr ?_⟩,
    hlift⟩
  · refine rangeRestrictHom_eq_one_of hQ _ _ _ fun w hw => ?_
    change projLift hQ (e * x * e⁻¹ * x⁻¹) w = w
    rw [hlift]
    exact eichler_apply_of_mem_lowSpan hu hm' (mem_lowSpan_of_mem_range hw)
  · refine kerQuotHom_eq_one_of hQ _ _ _ fun v hv => ?_
    change projLift hQ (e * x * e⁻¹ * x⁻¹) v - v ∈ _
    rw [hlift, range_lowNil]
    rw [ker_lowNil] at hv
    exact eichler_sub_mem_lowSpan hu hm' hv

end Core

end CFSG.SeitzReduction.OmegaPilot
