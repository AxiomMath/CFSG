module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeHeisSL3
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix

variable {K : Type*} [Field K]

@[expose] def sl3UnipStab (W : Submodule K (Fin 3 → K)) :
    Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {s | (∀ u, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ u - u ∈ W) ∧
    ∀ w ∈ W, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w}
  mul_mem' {a b} ha hb := by
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨fun u => ?_, fun w hw => ?_⟩
    · have h := ha2 _ (hb1 u)
      rw [mulVec_sub] at h
      change ((a : Matrix (Fin 3) (Fin 3) K) * (b : Matrix (Fin 3) (Fin 3) K)) *ᵥ u - u ∈ W
      rw [← mulVec_mulVec,
        ← sub_add_sub_cancel ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ u)) ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ u) u, h]
      exact W.add_mem (hb1 u) (ha1 u)
    · change ((a : Matrix (Fin 3) (Fin 3) K) * (b : Matrix (Fin 3) (Fin 3) K)) *ᵥ w = w
      rw [← mulVec_mulVec, hb2 w hw, ha2 w hw]
  one_mem' := ⟨fun u => by simp, fun w _ => by simp⟩
  inv_mem' {s} hs := by
    obtain ⟨hs1, hs2⟩ := hs
    have h1 : ((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (s : Matrix (Fin 3) (Fin 3) K) = 1 :=
      congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
        (inv_mul_cancel s)
    have h2 : (s : Matrix (Fin 3) (Fin 3) K) *
        ((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
      congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
        (mul_inv_cancel s)
    refine ⟨fun u => ?_, fun w hw => ?_⟩
    · have h := hs1 (((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u)
      rw [mulVec_mulVec, h2, one_mulVec] at h
      rw [← neg_sub]
      exact W.neg_mem h
    · calc ((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w =
          ((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((s : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by rw [hs2 w hw]
        _ = w := by rw [mulVec_mulVec, h1, one_mulVec]

theorem mem_sl3UnipStab {W : Submodule K (Fin 3 → K)} {s : SpecialLinearGroup (Fin 3) K} :
    s ∈ sl3UnipStab W ↔ (∀ u, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ u - u ∈ W) ∧
      ∀ w ∈ W, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w :=
  Iff.rfl

theorem sl3UnipStab_ne_bot {W : Submodule K (Fin 3 → K)} (h0 : W ≠ ⊥) (h1 : W ≠ ⊤) :
    sl3UnipStab W ≠ ⊥ := by
  classical
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨φ, hφ0, hWφ⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 h1)
  obtain ⟨v, hφv⟩ : ∃ v : Fin 3 → K, ∀ u, φ u = v ⬝ᵥ u := by
    refine ⟨fun i => φ fun j => if i = j then 1 else 0, fun u => ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ φ u, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hvW : ∀ x ∈ W, v ⬝ᵥ x = 0 := fun x hx => by
    rw [← hφv]
    exact hWφ hx
  have hdet : (1 + vecMulVec w v).det = 1 := by
    rw [vecMulVec_eq (Fin 1), det_one_add_replicateCol_mul_replicateRow, hvW w hwW, add_zero]
  have hmul : ∀ u, (1 + vecMulVec w v) *ᵥ u = u + (v ⬝ᵥ u) • w := by
    intro u
    rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  have hs : (⟨1 + vecMulVec w v, hdet⟩ : SpecialLinearGroup (Fin 3) K) ∈ sl3UnipStab W := by
    refine mem_sl3UnipStab.2 ⟨fun u => ?_, fun x hx => ?_⟩
    · change (1 + vecMulVec w v) *ᵥ u - u ∈ W
      rw [hmul, add_sub_cancel_left]
      exact W.smul_mem _ hwW
    · change (1 + vecMulVec w v) *ᵥ x = x
      rw [hmul, hvW x hx, zero_smul, add_zero]
  intro hbot
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra hcon
    refine hφ0 (LinearMap.ext fun x => ?_)
    rw [LinearMap.zero_apply]
    by_contra hx
    exact hcon ⟨x, hx⟩
  have hs1 := (Subgroup.eq_bot_iff_forall _).1 hbot _ hs
  have h := congrArg
    (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u) hs1
  change (1 + vecMulVec w v) *ᵥ u = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ u at h
  rw [hmul, one_mulVec, add_eq_left, ← hφv] at h
  exact smul_ne_zero hu hw0 h

theorem sl3UnipStab_pow_mulVec {W : Submodule K (Fin 3 → K)} {s : SpecialLinearGroup (Fin 3) K}
    (hs : s ∈ sl3UnipStab W) (k : ℕ) (u : Fin 3 → K) :
    ((s ^ k : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u =
      u + (k : K) • ((s : Matrix (Fin 3) (Fin 3) K) *ᵥ u - u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hw : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ ((s : Matrix (Fin 3) (Fin 3) K) *ᵥ u - u) =
        (s : Matrix (Fin 3) (Fin 3) K) *ᵥ u - u :=
      (mem_sl3UnipStab.1 hs).2 _ ((mem_sl3UnipStab.1 hs).1 u)
    rw [pow_succ']
    change ((s : Matrix (Fin 3) (Fin 3) K) *
      ((s ^ k : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *ᵥ u = _
    rw [← mulVec_mulVec, ih, mulVec_add, mulVec_smul, hw, Nat.cast_succ, add_smul, one_smul]
    abel

theorem isPGroup_sl3UnipStab (W : Submodule K (Fin 3 → K)) :
    IsPGroup (ringChar K) (sl3UnipStab W) := by
  intro s
  refine ⟨1, ?_⟩
  have h : (s : SpecialLinearGroup (Fin 3) K) ^ ringChar K = 1 := by
    refine Subtype.ext (ext_iff_mulVec.2 fun u => ?_)
    rw [sl3UnipStab_pow_mulVec s.2, ringChar.Nat.cast_ringChar, zero_smul, add_zero]
    exact (one_mulVec u).symm
  rw [pow_one]
  exact Subtype.ext h

theorem conjSL_mem_sl3UnipStab {W : Submodule K (Fin 3 → K)} {γ : GL (Fin 3) K}
    (hγ : ∀ w ∈ W, (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W)
    (hγ' : ∀ w ∈ W, ((γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W)
    {s : SpecialLinearGroup (Fin 3) K} (hs : s ∈ sl3UnipStab W) :
    conjSL γ s ∈ sl3UnipStab W := by
  obtain ⟨hs1, hs2⟩ := mem_sl3UnipStab.1 hs
  have hγγ : (γ : Matrix (Fin 3) (Fin 3) K) *
      ((γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.mul_inv γ
  have hu : ∀ u, (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, hγγ, one_mulVec]
  have e : ((conjSL γ s : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (γ : Matrix (Fin 3) (Fin 3) K) * (s : Matrix (Fin 3) (Fin 3) K) *
        ((γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    rfl
  refine mem_sl3UnipStab.2 ⟨fun u => ?_, fun w hw => ?_⟩
  · have h := hγ _ (hs1 (((γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u))
    rw [mulVec_sub, hu] at h
    rw [e, ← mulVec_mulVec, ← mulVec_mulVec]
    exact h
  · rw [e, ← mulVec_mulVec, ← mulVec_mulVec, hs2 _ (hγ' w hw), hu]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
