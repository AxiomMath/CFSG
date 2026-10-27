module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

@[expose] def radSL (W : Submodule K (Fin n → K)) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | (∀ x, (g : Matrix (Fin n) (Fin n) K) *ᵥ x - x ∈ W) ∧
    ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w}
  one_mem' := ⟨fun x => by simp, fun w _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun x => ?_, fun w hw => ?_⟩
    · rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      have h1 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ x - x) =
          (h : Matrix (Fin n) (Fin n) K) *ᵥ x - x := hg2 _ (hh1 x)
      rw [Matrix.mulVec_sub] at h1
      have h2 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ x) - x =
          ((h : Matrix (Fin n) (Fin n) K) *ᵥ x - x) +
            ((g : Matrix (Fin n) (Fin n) K) *ᵥ x - x) := by
        rw [← sub_eq_zero] at h1 ⊢
        rw [← h1]
        abel
      rw [h2]
      exact W.add_mem (hh1 x) (hg1 x)
    · rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hh2 w hw, hg2 w hw]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hgi : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
    have hig : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
    refine ⟨fun x => ?_, fun w hw => ?_⟩
    · set y := ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x with hy
      have hgy : (g : Matrix (Fin n) (Fin n) K) *ᵥ y = x := by
        rw [hy, Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
      have h1 := hg1 y
      rw [hgy] at h1
      have : y - x = -(x - y) := by abel
      rw [this]
      exact W.neg_mem h1
    · have h1 : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, hig, Matrix.one_mulVec]
      rwa [hg2 w hw] at h1

@[expose] def tvec (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0) : SpecialLinearGroup (Fin n) K :=
  ⟨1 + vecMulVec v φ, by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]⟩

theorem coe_tvec (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0) :
    ((tvec v φ h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + vecMulVec v φ := rfl

theorem tvec_mem_radSL {W : Submodule K (Fin n → K)} {v φ : Fin n → K} (hv : v ∈ W)
    (hφ : ∀ w ∈ W, φ ⬝ᵥ w = 0) :
    tvec v φ (hφ v hv) ∈ radSL W := by
  refine ⟨fun x => ?_, fun w hw => ?_⟩
  · rw [coe_tvec, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, add_sub_cancel_left,
      op_smul_eq_smul]
    exact W.smul_mem _ hv
  · rw [coe_tvec, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, hφ w hw,
      MulOpposite.op_zero, zero_smul, add_zero]

theorem radSL_le_stabilizer (W : Submodule K (Fin n → K)) : radSL W ≤ stabilizer W := by
  rintro g ⟨-, hg2⟩
  change W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W
  refine le_antisymm ?_ fun w hw => ⟨w, hw, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [mulVecLin_apply, hg2 w hw]
    exact hw
  · rw [mulVecLin_apply, hg2 w hw]

theorem mulVec_mem_of_mem_stabilizer {W : Submodule K (Fin n → K)}
    {s : SpecialLinearGroup (Fin n) K} (hs : s ∈ stabilizer W) {w : Fin n → K} (hw : w ∈ W) :
    (s : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  have hs' : W.map (mulVecLin (s : Matrix (Fin n) (Fin n) K)) = W := hs
  have : (s : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W.map (mulVecLin (s : Matrix (Fin n) (Fin n) K)) :=
    ⟨w, hw, mulVecLin_apply _ _⟩
  rwa [hs'] at this

theorem conj_mem_radSL {W : Submodule K (Fin n → K)} {s : SpecialLinearGroup (Fin n) K}
    (hs : s ∈ stabilizer W) {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ radSL W) :
    s * g * s⁻¹ ∈ radSL W := by
  obtain ⟨hg1, hg2⟩ := hg
  have hsi : s⁻¹ ∈ stabilizer W := inv_mem hs
  have hss : (s : Matrix (Fin n) (Fin n) K) * ((s⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  refine ⟨fun x => ?_, fun w hw => ?_⟩
  · set y := ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x with hy
    have hsy : (s : Matrix (Fin n) (Fin n) K) *ᵥ y = x := by
      rw [hy, Matrix.mulVec_mulVec, hss, Matrix.one_mulVec]
    have h1 : (s : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ y - y) ∈ W :=
      mulVec_mem_of_mem_stabilizer hs (hg1 y)
    rw [Matrix.mulVec_sub, hsy] at h1
    simpa [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hy] using h1
  · have h1 : ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W :=
      mulVec_mem_of_mem_stabilizer hsi hw
    simp only [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    rw [hg2 _ h1, Matrix.mulVec_mulVec, hss, Matrix.one_mulVec]

theorem pow_eq_one_of_mem_radSL {r : ℕ} [Fact r.Prime] [CharP K r] (hn : 1 ≤ n)
    {W : Submodule K (Fin n → K)} {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ radSL W) :
    g ^ r = 1 := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hg1, hg2⟩ := hg
  set N : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) - 1 with hN
  have hNW : ∀ x, N *ᵥ x ∈ W := fun x => by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact hg1 x
  have hN0 : ∀ w ∈ W, N *ᵥ w = 0 := fun w hw => by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hg2 w hw, sub_self]
  have hNN : N * N = 0 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hN0 _ (hNW x), map_zero,
      LinearMap.zero_apply]
  have hNr : N ^ r = 0 := by
    have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
    rw [show r = 2 + (r - 2) by omega, pow_add, pow_two, hNN, zero_mul]
  have hgN : (g : Matrix (Fin n) (Fin n) K) = 1 + N := by rw [hN]; abel
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, hgN, add_pow_char_of_commute r (Commute.one_left N), one_pow,
    hNr, add_zero]
  rfl

section Proj

@[expose] def radProj (n : ℕ) (K : Type) [Field K] (W : Submodule K (Fin n → K)) :
    Subgroup (projectiveSL n K) :=
  (radSL W).map (proj n K)

theorem radProj_le_projStabilizer (W : Submodule K (Fin n → K)) :
    radProj n K W ≤ projStabilizer W :=
  Subgroup.map_mono (radSL_le_stabilizer W)

theorem projStabilizer_le_normalizer_radProj (W : Submodule K (Fin n → K)) :
    projStabilizer W ≤ normalizer (radProj n K W : Set (projectiveSL n K)) := by
  have key : ∀ m ∈ projStabilizer W, ∀ h ∈ radProj n K W, m * h * m⁻¹ ∈ radProj n K W := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨g, hg, rfl⟩
    exact ⟨s * g * s⁻¹, conj_mem_radSL hs hg, by simp [map_mul, map_inv]⟩
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key m hm h hh, fun hh => ?_⟩
  have := key m⁻¹ (inv_mem hm) _ hh
  simpa [mul_assoc] using this

theorem isPGroup_radProj {r : ℕ} [Fact r.Prime] [CharP K r] (hn : 1 ≤ n)
    (W : Submodule K (Fin n → K)) : IsPGroup r (radProj n K W) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨_, g, hg, rfl⟩
  have h1 : (⟨proj n K g, g, hg, rfl⟩ : radProj n K W) ^ r = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← map_pow, pow_eq_one_of_mem_radSL hn hg, map_one]
    rfl
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp h2 with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

end Proj

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
