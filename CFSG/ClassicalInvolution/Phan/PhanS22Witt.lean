module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Witt

open QuadraticMap Module

section Basic

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem polar_sum_left {ι : Type*} [Fintype ι] (v : ι → V) (c : ι → F) (y : V) :
    polar Q (∑ i, c i • v i) y = ∑ i, c i * polar Q (v i) y := by
  simp only [← polarBilin_apply_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]

theorem polar_sum_right {ι : Type*} [Fintype ι] (x : V) (v : ι → V) (c : ι → F) :
    polar Q x (∑ i, c i • v i) = ∑ i, c i * polar Q x (v i) := by
  simp only [← polarBilin_apply_apply, map_sum, map_smul, smul_eq_mul]

theorem polar_sum_smul {ι : Type*} [Fintype ι] (v : ι → V) (c d : ι → F) :
    polar Q (∑ i, c i • v i) (∑ j, d j • v j) =
      ∑ i, ∑ j, c i * (d j * polar Q (v i) (v j)) := by
  rw [polar_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [polar_sum_right, Finset.mul_sum]

theorem map_add_smul_of_map_eq_zero {r : V} (hr : Q r = 0) (z : V) (t : F) :
    Q (z + t • r) = Q z + t * polar Q z r := by
  rw [QuadraticMap.map_add Q z (t • r), QuadraticMap.map_smul, polar_smul_right, hr]
  simp

theorem map_sub_map_smul_eq_zero {r : V} (hr : Q r = 0) {z : V} (hz : polar Q z r = 1) :
    Q (z - Q z • r) = 0 := by
  rw [sub_eq_add_neg, ← neg_smul, map_add_smul_of_map_eq_zero hr, hz]
  ring

theorem not_mem_span_of_polar {ι : Type*} [Fintype ι] (v : ι → V) {r y : V}
    (hry : polar Q r y = 1) (hrv : ∀ j, polar Q r (v j) = 0) :
    y ∉ Submodule.span F (Set.range v) := by
  intro h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp h
  rw [← hc, polar_sum_right] at hry
  simp [hrv] at hry

theorem rel_step {ι : Type*} [Fintype ι] (v : ι → V) {r y : V} (hry : polar Q r y = 1)
    (hrv : ∀ j, polar Q r (v j) = 0) (c : Option ι → F)
    (h : ∑ i, c i • i.elim y v = 0) : c none = 0 ∧ ∑ i, c (some i) • v i = 0 := by
  rw [Fintype.sum_option] at h
  simp only [Option.elim_none, Option.elim_some] at h
  have h1 : c none = 0 := by
    have := congrArg (polar Q r) h
    rw [polar_add_right, polar_smul_right, polar_sum_right, polar_zero_right, hry] at this
    simpa [hrv] using this
  refine ⟨h1, ?_⟩
  rw [h1, zero_smul, zero_add] at h
  exact h

theorem family_extend {ι : Type*} [Fintype ι] (v w : ι → V)
    (hgram : ∀ i j, polar Q (v i) (v j) = polar Q (w i) (w j))
    (hrel : ∀ c : ι → F, ∑ i, c i • v i = 0 ↔ ∑ i, c i • w i = 0) {r r' y y' : V}
    (hy : polar Q r y = 1) (hy' : polar Q r' y' = 1) (hQy : Q y = 0) (hQy' : Q y' = 0)
    (hrv : ∀ j, polar Q r (v j) = 0) (hrw : ∀ j, polar Q r' (w j) = 0)
    (hyy : ∀ i, polar Q (v i) y = polar Q (w i) y') :
    (∀ i j : Option ι, polar Q (i.elim y v) (j.elim y v) = polar Q (i.elim y' w) (j.elim y' w)) ∧
    (∀ c : Option ι → F, ∑ i, c i • i.elim y v = 0 ↔ ∑ i, c i • i.elim y' w = 0) := by
  refine ⟨?_, fun c => ?_⟩
  · intro i j
    rcases i with _ | i <;> rcases j with _ | j
    · simp only [Option.elim_none]
      rw [polar_self, polar_self, hQy, hQy']
    · simp only [Option.elim_none, Option.elim_some]
      rw [polar_comm Q y (v j), polar_comm Q y' (w j)]
      exact hyy j
    · simp only [Option.elim_none, Option.elim_some]
      exact hyy i
    · exact hgram i j
  · constructor
    · intro h
      obtain ⟨h0, h1⟩ := rel_step v hy hrv c h
      have h2 := (hrel _).1 h1
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some]
      rw [h0, zero_smul, zero_add]
      exact h2
    · intro h
      obtain ⟨h0, h1⟩ := rel_step w hy' hrw c h
      have h2 := (hrel _).2 h1
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some]
      rw [h0, zero_smul, zero_add]
      exact h2

end Basic

section Regular

variable {F : Type*} [Field F] [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V}

theorem map_eq_zero_of_polar_self {x : V} (h : polar Q x x = 0) : Q x = 0 := by
  have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  rw [polar_self, nsmul_eq_mul] at h
  simpa [h2] using h

variable [FiniteDimensional F V]

theorem exists_vec_polar_eq (hQ : Q.Nondegenerate) {ι : Type*} [Fintype ι] (w : ι → V)
    (t : ι → F) (ht : ∀ c : ι → F, ∑ i, c i • w i = 0 → ∑ i, c i * t i = 0) :
    ∃ y : V, ∀ i, polar Q (w i) y = t i := by
  classical
  have hB : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hτ : Fintype.linearCombination F t ∈
      (LinearMap.ker (Fintype.linearCombination F w)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro c hc
    have hc' : ∑ i, c i • w i = 0 := hc
    have := ht c hc'
    simpa [Fintype.linearCombination_apply] using this
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hτ
  obtain ⟨φ, hφ⟩ := hτ
  refine ⟨(LinearMap.BilinForm.toDual Q.polarBilin hB).symm φ, fun i => ?_⟩
  have h1 : Q.polarBilin ((LinearMap.BilinForm.toDual Q.polarBilin hB).symm φ) (w i) = φ (w i) :=
    LinearMap.BilinForm.apply_toDual_symm_apply _ _
  have h2 : φ (w i) = t i := by
    have := congrArg (fun L => L (Pi.single i (1 : F))) hφ
    simpa using this
  rw [polar_comm, ← polarBilin_apply_apply, h1, h2]

theorem exists_isotropic_partner (hQ : Q.Nondegenerate) {r : V} (hr0 : r ≠ 0) (hQr : Q r = 0) :
    ∃ y : V, polar Q r y = 1 ∧ Q y = 0 := by
  obtain ⟨z, hz⟩ := exists_vec_polar_eq hQ (fun _ : Unit => r) (fun _ => (1 : F)) (by
    intro c hc
    simp only [Finset.univ_unique, Finset.sum_singleton] at hc ⊢
    rcases smul_eq_zero.mp hc with h | h
    · simp [h]
    · exact absurd h hr0)
  have hz' : polar Q r z = 1 := hz ()
  refine ⟨z - Q z • r, ?_, ?_⟩
  · rw [polar_sub_right, polar_smul_right, polar_self, hQr, hz']
    simp
  · exact map_sub_map_smul_eq_zero hQr (by rw [polar_comm]; exact hz')

theorem exists_extend_vectors (hQ : Q.Nondegenerate) {ι : Type*} [Fintype ι] (v w : ι → V)
    (hgram : ∀ i j, polar Q (v i) (v j) = polar Q (w i) (w j))
    (hrel : ∀ c : ι → F, ∑ i, c i • v i = 0 ↔ ∑ i, c i • w i = 0)
    (a : ι → F) {r r' : V} (hr : r = ∑ i, a i • v i) (hr' : r' = ∑ i, a i • w i)
    (hr0 : r ≠ 0) (hrv : ∀ j, polar Q r (v j) = 0) :
    ∃ y y' : V, polar Q r y = 1 ∧ Q y = 0 ∧ (∀ i, polar Q (v i) y = polar Q (w i) y') ∧
      polar Q r' y' = 1 ∧ Q y' = 0 ∧ (∀ j, polar Q r' (w j) = 0) := by
  have hQr : Q r = 0 := by
    apply map_eq_zero_of_polar_self
    calc polar Q r r = polar Q r (∑ j, a j • v j) := by rw [← hr]
      _ = ∑ j, a j * polar Q r (v j) := polar_sum_right _ _ _
      _ = 0 := by simp [hrv]
  have hrw : ∀ j, polar Q r' (w j) = 0 := by
    intro j
    calc polar Q r' (w j) = ∑ i, a i * polar Q (w i) (w j) := by rw [hr', polar_sum_left]
      _ = ∑ i, a i * polar Q (v i) (v j) := by simp only [hgram]
      _ = polar Q r (v j) := by rw [hr, polar_sum_left]
      _ = 0 := hrv j
  have hQr' : Q r' = 0 := by
    apply map_eq_zero_of_polar_self
    calc polar Q r' r' = polar Q r' (∑ j, a j • w j) := by rw [← hr']
      _ = ∑ j, a j * polar Q r' (w j) := polar_sum_right _ _ _
      _ = 0 := by simp [hrw]
  obtain ⟨y, hy1, hy0⟩ := exists_isotropic_partner hQ hr0 hQr
  obtain ⟨y₀, hy₀⟩ := exists_vec_polar_eq hQ w (fun i => polar Q (v i) y) (by
    intro c hc
    have h := (hrel c).2 hc
    have := polar_sum_left (Q := Q) v c y
    rw [h, polar_zero_left] at this
    exact this.symm)
  have hry₀ : polar Q r' y₀ = 1 := by
    calc polar Q r' y₀ = ∑ i, a i * polar Q (w i) y₀ := by rw [hr', polar_sum_left]
      _ = ∑ i, a i * polar Q (v i) y := by simp only [hy₀]
      _ = polar Q r y := by rw [hr, polar_sum_left]
      _ = 1 := hy1
  have hrr' : polar Q r' r' = 0 := by rw [polar_self, hQr']; simp
  refine ⟨y, y₀ - Q y₀ • r', hy1, hy0, ?_, ?_, ?_, hrw⟩
  · intro i
    rw [polar_sub_right, polar_smul_right, polar_comm Q (w i) r', hrw i, smul_zero, sub_zero,
      hy₀ i]
  · rw [polar_sub_right, polar_smul_right, hry₀, hrr']
    simp
  · exact map_sub_map_smul_eq_zero hQr' (by rw [polar_comm]; exact hry₀)

end Regular

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Witt
