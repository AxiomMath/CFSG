module

public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.OddTranspositions.Width

public section

namespace CFSG.Fischer.Classification.Unitary

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)
open CFSG.OddTranspositions

variable {m : ℕ}

@[expose] noncomputable def v1 (hm : 4 ≤ m) : Fin m → K :=
  Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ ω

@[expose] noncomputable def v2 (hm : 4 ≤ m) : Fin m → K :=
  Pi.single ⟨2, by omega⟩ 1 + Pi.single ⟨3, by omega⟩ ω

@[expose] noncomputable def v3 (hm : 4 ≤ m) : Fin m → K := v1 hm + v2 hm

theorem v1_ne_zero (hm : 4 ≤ m) : v1 hm ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by
    simpa [v1, Fin.ext_iff] using congrFun h ⟨0, by omega⟩
  exact one_ne_zero h1

theorem v2_ne_zero (hm : 4 ≤ m) : v2 hm ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by
    simpa [v2, Fin.ext_iff] using congrFun h ⟨2, by omega⟩
  exact one_ne_zero h1

theorem v3_ne_zero (hm : 4 ≤ m) : v3 hm ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by
    simpa [v3, v1, v2, Fin.ext_iff] using congrFun h ⟨0, by omega⟩
  exact one_ne_zero h1

theorem herm_v1_v1 (hm : 4 ≤ m) : fischerHermitianF4 m (v1 hm) (v1 hm) = 0 := by
  rw [fischerHermitianF4_eq_herm]
  simpa [v1] using isotropic_single_add_single (n := m)
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]) (t := ω) omega_ne_zero

theorem herm_v2_v2 (hm : 4 ≤ m) : fischerHermitianF4 m (v2 hm) (v2 hm) = 0 := by
  rw [fischerHermitianF4_eq_herm]
  simpa [v2] using isotropic_single_add_single (n := m)
    (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (by simp [Fin.ext_iff]) (t := ω) omega_ne_zero

theorem herm_v1_v2 (hm : 4 ≤ m) : fischerHermitianF4 m (v1 hm) (v2 hm) = 0 := by
  rw [fischerHermitianF4_eq_herm, v2, herm_single_add_single_left]
  simp [v1, Fin.ext_iff]

theorem herm_v1_v3 (hm : 4 ≤ m) : fischerHermitianF4 m (v1 hm) (v3 hm) = 0 := by
  have h11 : herm frob (v1 hm) (v1 hm) = 0 := by
    simpa [fischerHermitianF4_eq_herm] using herm_v1_v1 hm
  have h21 : herm frob (v2 hm) (v1 hm) = 0 := by
    simpa [fischerHermitianF4_eq_herm] using herm_v1_v2 hm
  rw [fischerHermitianF4_eq_herm, v3, herm_add_left, h11, h21]
  simp

theorem herm_v2_v3 (hm : 4 ≤ m) : fischerHermitianF4 m (v2 hm) (v3 hm) = 0 := by
  have h12 : herm frob (v1 hm) (v2 hm) = 0 :=
    herm_eq_zero_comm frob frob_frob (by
      simpa [fischerHermitianF4_eq_herm] using herm_v1_v2 hm)
  have h22 : herm frob (v2 hm) (v2 hm) = 0 := by
    simpa [fischerHermitianF4_eq_herm] using herm_v2_v2 hm
  rw [fischerHermitianF4_eq_herm, v3, herm_add_left, h12, h22]
  simp

theorem herm_v3_v3 (hm : 4 ≤ m) : fischerHermitianF4 m (v3 hm) (v3 hm) = 0 := by
  have h11 : herm frob (v1 hm) (v1 hm) = 0 := by
    simpa [fischerHermitianF4_eq_herm] using herm_v1_v1 hm
  have h22 : herm frob (v2 hm) (v2 hm) = 0 := by
    simpa [fischerHermitianF4_eq_herm] using herm_v2_v2 hm
  have h21 : herm frob (v2 hm) (v1 hm) = 0 := by
    simpa [fischerHermitianF4_eq_herm] using herm_v1_v2 hm
  have h12 : herm frob (v1 hm) (v2 hm) = 0 := herm_eq_zero_comm frob frob_frob h21
  rw [fischerHermitianF4_eq_herm, v3, herm_add_left, herm_add_right, herm_add_right,
    h11, h12, h21, h22]
  simp

theorem herm_frob_v1_v1 (hm : 4 ≤ m) : herm frob (v1 hm) (v1 hm) = 0 := by
  rw [← fischerHermitianF4_eq_herm]
  exact herm_v1_v1 hm

theorem herm_frob_v2_v2 (hm : 4 ≤ m) : herm frob (v2 hm) (v2 hm) = 0 := by
  rw [← fischerHermitianF4_eq_herm]
  exact herm_v2_v2 hm

theorem herm_frob_v3_v3 (hm : 4 ≤ m) : herm frob (v3 hm) (v3 hm) = 0 := by
  rw [← fischerHermitianF4_eq_herm]
  exact herm_v3_v3 hm

theorem herm_frob_v1_v2 (hm : 4 ≤ m) : herm frob (v1 hm) (v2 hm) = 0 := by
  exact herm_eq_zero_comm frob frob_frob (by
    rw [← fischerHermitianF4_eq_herm]
    exact herm_v1_v2 hm)

theorem herm_frob_v1_v3 (hm : 4 ≤ m) : herm frob (v1 hm) (v3 hm) = 0 := by
  exact herm_eq_zero_comm frob frob_frob (by
    rw [← fischerHermitianF4_eq_herm]
    exact herm_v1_v3 hm)

theorem herm_frob_v2_v3 (hm : 4 ≤ m) : herm frob (v2 hm) (v3 hm) = 0 := by
  exact herm_eq_zero_comm frob frob_frob (by
    rw [← fischerHermitianF4_eq_herm]
    exact herm_v2_v3 hm)

theorem v2_not_smul_v1 (hm : 4 ≤ m) : ¬ ∃ c : K, v2 hm = c • v1 hm := by
  rintro ⟨c, hc⟩
  have h1 : (1 : K) = 0 := by
    simpa [v1, v2, Fin.ext_iff] using congrFun hc ⟨2, by omega⟩
  exact one_ne_zero h1

theorem v3_not_smul_v1 (hm : 4 ≤ m) : ¬ ∃ c : K, v3 hm = c • v1 hm := by
  rintro ⟨c, hc⟩
  have h1 : (1 : K) = 0 := by
    simpa [v3, v1, v2, Fin.ext_iff] using congrFun hc ⟨2, by omega⟩
  exact one_ne_zero h1

theorem v3_not_smul_v2 (hm : 4 ≤ m) : ¬ ∃ c : K, v3 hm = c • v2 hm := by
  rintro ⟨c, hc⟩
  have h1 : ω = 0 := by
    simpa [v3, v1, v2, Fin.ext_iff] using congrFun hc ⟨1, by omega⟩
  exact omega_ne_zero h1

theorem tvU_images_distinct_in_center_quotient (hm : 4 ≤ m) :
    tq (v1 hm) ≠ tq (v2 hm) ∧ tq (v1 hm) ≠ tq (v3 hm) ∧
      tq (v2 hm) ≠ tq (v3 hm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact v2_not_smul_v1 hm
      ((tq_eq_tq_iff (by omega) (v1_ne_zero hm) (herm_frob_v1_v1 hm)
        (v2_ne_zero hm) (herm_frob_v2_v2 hm)).1 h)
  · intro h
    exact v3_not_smul_v1 hm
      ((tq_eq_tq_iff (by omega) (v1_ne_zero hm) (herm_frob_v1_v1 hm)
        (v3_ne_zero hm) (herm_frob_v3_v3 hm)).1 h)
  · intro h
    exact v3_not_smul_v2 hm
      ((tq_eq_tq_iff (by omega) (v2_ne_zero hm) (herm_frob_v2_v2 hm)
        (v3_ne_zero hm) (herm_frob_v3_v3 hm)).1 h)

theorem tqU_images_distinct (hm : 4 ≤ m) :
    tqU (v1 hm) ≠ tqU (v2 hm) ∧ tqU (v1 hm) ≠ tqU (v3 hm) ∧
      tqU (v2 hm) ≠ tqU (v3 hm) := by
  obtain ⟨h12, h13, h23⟩ := tvU_images_distinct_in_center_quotient hm
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply h12
    have := congrArg (u2Equiv m) h
    simpa [u2Equiv_tqU] using this
  · intro h
    apply h13
    have := congrArg (u2Equiv m) h
    simpa [u2Equiv_tqU] using this
  · intro h
    apply h23
    have := congrArg (u2Equiv m) h
    simpa [u2Equiv_tqU] using this

theorem mem_D_of_tqU_mem {G : Type*} [Group G] {D : Set G} {m : ℕ}
    {φ : G ≃* U2 m} (hφ : φ '' D = DU m) {v : Fin m → K}
    (hv0 : v ≠ 0) (hv : herm frob v v = 0) : φ.symm (tqU v) ∈ D := by
  have hq : tqU v ∈ DU m := tqU_mem_DU hv0 hv
  have himg : φ (φ.symm (tqU v)) ∈ φ '' D := by
    rw [φ.apply_symm_apply, hφ]
    exact hq
  obtain ⟨g, hgD, hg⟩ := himg
  rw [φ.injective hg] at hgD
  exact hgD

theorem width_two_false_of_psu_case {G : Type*} [Group G] {D : Set G} {m : ℕ}
    (hm : 4 ≤ m)
    (hmodel : fischerCentralQuotientModel D
      (fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) K => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    ¬ WidthLe D 2 := by
  classical
  obtain ⟨φ, hφ⟩ :=
    (CFSG.Fischer.Classification.fischerCentralQuotientModel_iff_U2 (m := m)).1 hmodel
  let y1 : G := φ.symm (tqU (v1 hm))
  let y2 : G := φ.symm (tqU (v2 hm))
  let y3 : G := φ.symm (tqU (v3 hm))
  have hy1D : y1 ∈ D := by
    simpa [y1] using mem_D_of_tqU_mem (m := m) hφ (v1_ne_zero hm) (herm_frob_v1_v1 hm)
  have hy2D : y2 ∈ D := by
    simpa [y2] using mem_D_of_tqU_mem (m := m) hφ (v2_ne_zero hm) (herm_frob_v2_v2 hm)
  have hy3D : y3 ∈ D := by
    simpa [y3] using mem_D_of_tqU_mem (m := m) hφ (v3_ne_zero hm) (herm_frob_v3_v3 hm)
  obtain ⟨hq12, hq13, hq23⟩ := tqU_images_distinct (m := m) hm
  have hy12 : y1 ≠ y2 := by
    intro h
    apply hq12
    have := congrArg φ h
    simpa [y1, y2] using this
  have hy13 : y1 ≠ y3 := by
    intro h
    apply hq13
    have := congrArg φ h
    simpa [y1, y3] using this
  have hy23 : y2 ≠ y3 := by
    intro h
    apply hq23
    have := congrArg φ h
    simpa [y2, y3] using this
  have hc12 : Commute y1 y2 := by
    have hq : Commute (tqU (v1 hm)) (tqU (v2 hm)) :=
      (tqU_commute_iff (by omega) (v1_ne_zero hm) (herm_frob_v1_v1 hm)
        (v2_ne_zero hm) (herm_frob_v2_v2 hm)).2 (herm_frob_v1_v2 hm)
    have hq' : Commute (φ y1) (φ y2) := by simpa [y1, y2] using hq
    simpa using hq'.map φ.symm
  have hc13 : Commute y1 y3 := by
    have hq : Commute (tqU (v1 hm)) (tqU (v3 hm)) :=
      (tqU_commute_iff (by omega) (v1_ne_zero hm) (herm_frob_v1_v1 hm)
        (v3_ne_zero hm) (herm_frob_v3_v3 hm)).2 (herm_frob_v1_v3 hm)
    have hq' : Commute (φ y1) (φ y3) := by simpa [y1, y3] using hq
    simpa using hq'.map φ.symm
  have hc23 : Commute y2 y3 := by
    have hq : Commute (tqU (v2 hm)) (tqU (v3 hm)) :=
      (tqU_commute_iff (by omega) (v2_ne_zero hm) (herm_frob_v2_v2 hm)
        (v3_ne_zero hm) (herm_frob_v3_v3 hm)).2 (herm_frob_v2_v3 hm)
    have hq' : Commute (φ y2) (φ y3) := by simpa [y2, y3] using hq
    simpa using hq'.map φ.symm
  intro hW
  rw [widthLe_two_iff] at hW
  exact hW y1 hy1D y2 hy2D y3 hy3D hy12 hy13 hy23 ⟨hc12, hc13, hc23⟩

end CFSG.Fischer.Classification.Unitary
