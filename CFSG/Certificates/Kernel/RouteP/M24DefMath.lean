module

public import Certificates.Data.Kernel.RouteP.M24Def
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Arr
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.MaskDual

public section

namespace CFSG.KC.M24Def

open Certificates.RouteP.M24Defect CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem act11_compA {σ τ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) (hτ : τ ∈ AutPerm)
    {a b : Array ℕ} (ha : HasArr σ a) (hb : HasArr τ b) (m : ℕ) :
    act11 (compA a b) m = act11 a (act11 b m) := by
  have h := rho11_toW AutPerm le_rfl (⟨σ, hσ⟩ * ⟨τ, hτ⟩) (a := compA a b) (HasArr.mul ha hb) m
  rw [map_mul, MulAut.mul_apply, rho11_toW AutPerm le_rfl ⟨τ, hτ⟩ hb,
    rho11_toW AutPerm le_rfl ⟨σ, hσ⟩ ha] at h
  exact toW_inj (act11_lt _ _) (act11_lt _ _) h.symm

theorem length_matA (a : Array ℕ) : (matA a).length = 11 := length_matOf 11 _

theorem actM_matA (a : Array ℕ) {w : ℕ} (hw : w < 2 ^ 11) : actM (matA a) w = act11 a w :=
  actM_matOf (xorLin_act11 a) 11 w hw

theorem dualAct_lt : ∀ (cols : List ℕ) (m : ℕ), dualAct cols m < 2 ^ cols.length
  | [], _ => by simp [dualAct]
  | c :: cs, m => by
    have h := dualAct_lt cs m
    have h2 : popc 11 (m &&& c) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rw [dualAct, List.length_cons, pow_succ]
    omega

theorem bp_two_pow (x : ℕ) {j : ℕ} (hj : j < 11) :
    bp x (2 ^ j) = if x.testBit j then (1 : ZMod 2) else 0 := by
  rw [bp_eq_sum, Finset.sum_eq_single j]
  · simp [Nat.testBit_two_pow_self]
  · intro c _ hc
    simp [Nat.testBit_two_pow, Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

theorem eq_of_bp {x y : ℕ} (hx : x < 2 ^ 11) (hy : y < 2 ^ 11)
    (h : ∀ w < 2 ^ 11, bp x w = bp y w) : x = y := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < 11
  · have h1 := h (2 ^ j) (Nat.pow_lt_pow_right (by norm_num) hj)
    rw [bp_two_pow x hj, bp_two_pow y hj] at h1
    cases hxj : x.testBit j <;> cases hyj : y.testBit j <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem dualAct_matA_compA {σ τ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) (hτ : τ ∈ AutPerm)
    {a b : Array ℕ} (ha : HasArr σ a) (hb : HasArr τ b) (m : ℕ) :
    dualAct (matA (compA a b)) m = dualAct (matA b) (dualAct (matA a) m) := by
  have hl : ∀ c, dualAct (matA c) m < 2 ^ 11 := fun c => by
    simpa [length_matA] using dualAct_lt (matA c) m
  refine eq_of_bp (hl _) (by simpa [length_matA] using dualAct_lt (matA b) _) fun w hw => ?_
  rw [bp_dualAct (length_matA _), bp_dualAct (length_matA _), bp_dualAct (length_matA _),
    actM_matA _ hw, actM_matA _ hw, actM_matA _ (act11_lt b w), act11_compA hσ hτ ha hb]

theorem blt_land_shiftLeft (m j : ℕ) : Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 j)) = m.testBit j := by
  have h : Nat.land m (Nat.shiftLeft 1 j) = m &&& 2 ^ j := by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; rfl
  rw [h]
  cases hm : m.testBit j
  · have : m &&& 2 ^ j = 0 := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : j = i
      · subst hi; simp [hm]
      · simp [hi]
    rw [this]; rfl
  · have : m &&& 2 ^ j = 2 ^ j := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hi : j = i
      · subst hi; simp [hm]
      · simp [hi]
    rw [this, Nat.blt_eq]
    exact Nat.two_pow_pos j

theorem ln_lt (D j : ℕ) : ln 11 D j < 2 ^ 11 := by
  unfold ln
  have : Nat.sub (Nat.shiftLeft 1 11) 1 = 2 ^ 11 - 1 := rfl
  rw [this]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem bvec_dapp_aux (D m : ℕ) : ∀ k : ℕ,
    bvec 11 (Nat.rec (motive := fun _ => Nat) 0 (fun j acc =>
      Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (ln 11 D j))
        (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 j)))) k) =
      ∑ j ∈ Finset.range k, if m.testBit j then bvec 11 (ln 11 D j) else 0
  | 0 => by simp [bvec_zero]
  | k + 1 => by
    rw [Finset.sum_range_succ, ← bvec_dapp_aux D m k]
    simp only
    rw [blt_land_shiftLeft]
    cases m.testBit k
    · simp
    · simp only [if_true]
      exact bvec_xor _ _ _

theorem dapp_lt (D m : ℕ) : dapp D m < 2 ^ 11 := by
  unfold dapp
  have key : ∀ k, Nat.rec (motive := fun _ => Nat) 0 (fun j acc =>
      Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (ln 11 D j))
        (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 j)))) k < 2 ^ 11 := by
    intro k
    induction k with
    | zero => exact Nat.two_pow_pos 11
    | succ k ih =>
      simp only
      cases Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 k))
      · exact ih
      · exact Nat.xor_lt_two_pow ih (ln_lt D k)
  exact key 11

theorem dapp_eq_actM (D m : ℕ) : dapp D m = actM ((List.range 11).map (ln 11 D)) m := by
  refine bvec_inj (dapp_lt D m) (actM_lt (fun c hc => ?_) m) ?_
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    exact ln_lt D j
  · rw [dapp, bvec_dapp_aux, bvec_actM, List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.1 hj)]
    simp

theorem dapp_eq_of_lanes {D : ℕ} {f : ℕ → ℕ} (hf : XorLin f) (hD : ∀ j < 11, ln 11 D j = f (2 ^ j))
    {m : ℕ} (hm : m < 2 ^ 11) : dapp D m = f m := by
  rw [dapp_eq_actM, ← actM_matOf hf 11 m hm]
  congr 1
  refine List.ext_getElem (by simp [matOf]) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, matOf]
  exact hD j (by simpa using h1)

theorem xorLin_dualAct_matA (a : Array ℕ) : XorLin (dualAct (matA a)) := fun x y => by
  have hl : ∀ m, dualAct (matA a) m < 2 ^ 11 := fun m => by
    simpa [length_matA] using dualAct_lt (matA a) m
  refine eq_of_bp (hl _) (Nat.xor_lt_two_pow (hl _) (hl _)) fun w _ => ?_
  rw [bp_xor_left, bp_dualAct (length_matA _), bp_dualAct (length_matA _),
    bp_dualAct (length_matA _), bp_xor_left]

theorem dapp_eq_dualAct {D : ℕ} {a : Array ℕ}
    (hD : ∀ j < 11, ln 11 D j = dualAct (matA a) (2 ^ j)) {m : ℕ} (hm : m < 2 ^ 11) :
    dapp D m = dualAct (matA a) m :=
  dapp_eq_of_lanes (xorLin_dualAct_matA a) hD hm

theorem dapp_eq_act11 {D : ℕ} {a : Array ℕ} (hD : ∀ j < 11, ln 11 D j = act11 a (2 ^ j))
    {m : ℕ} (hm : m < 2 ^ 11) : dapp D m = act11 a m :=
  dapp_eq_of_lanes (xorLin_act11 a) hD hm

end CFSG.KC.M24Def

end
