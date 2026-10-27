module

public import Certificates.Data.Kernel.MonsterB.Rem3069
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.Rem3069

open CFSG.KC.FischerK

inductive ReachL : Nat → Prop
  | seed : ReachL remSeedN
  | step {x : Nat} (g : Nat) (hg : g < 4) : ReachL x → ReachL (vecMulL (fourColL g) x)

theorem allFrom_iff (f : Nat → Bool) (lo : Nat) :
    ∀ n, allFrom f lo n = true ↔ ∀ k < n, f (lo + k) = true
  | 0 => by
    constructor
    · intro _ k hk
      exact absurd hk (Nat.not_lt_zero k)
    · intro _
      rfl
  | n + 1 => by
    change (f (Nat.add lo n) && allFrom f lo n) = true ↔ _
    rw [Bool.and_eq_true, allFrom_iff f lo n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem lt_cntOf {i : Nat} (hi : i < remN) : i % 1000 < cntOf (i / 1000) := by
  have hd := Nat.div_add_mod i 1000
  have hm := Nat.mod_lt i (by decide : 1000 > 0)
  unfold cntOf
  cases h : Nat.ble (Nat.mul (Nat.succ (i / 1000)) 1000) remN
  · change i % 1000 < remN - i / 1000 * 1000
    unfold remN at hi ⊢
    omega
  · exact hm

variable {R : Nat → Nat}

theorem recOK_of (h : ∀ c < 695, chunkOK R c = true) {i : Nat} (hi : i < remN) :
    recOK R i = true := by
  have hc : i / 1000 < 695 := by
    unfold remN at hi
    omega
  have := (allFrom_iff _ _ _).1 (h _ hc) (i % 1000) (lt_cntOf hi)
  have e : Nat.mul (i / 1000) 1000 + i % 1000 = i := by
    change i / 1000 * 1000 + i % 1000 = i
    omega
  rwa [e] at this

theorem recOK_spec {i : Nat} (h : recOK R i = true) :
    vecOf (recAt R i) < 2 ^ 78 ∧
      (i + 1 = remN ∨ vecOf (recAt R i) < vecOf (recAt R (i + 1))) ∧
      (depOf (recAt R i) = 0 → vecOf (recAt R i) = remSeedN) ∧
      (depOf (recAt R i) ≠ 0 → parOf (recAt R i) < remN ∧
        depOf (recAt R (parOf (recAt R i))) + 1 = depOf (recAt R i) ∧
        vecOf (recAt R i) =
          vecMulL (fourColL (genOf (recAt R i))) (vecOf (recAt R (parOf (recAt R i))))) := by
  unfold recOK recOKr at h
  generalize recAt R i = r at h ⊢
  have e78 : (302231454903657293676544 : Nat) = 2 ^ 78 := by norm_num
  cases hd : Nat.beq (depOf r) 0
  · rw [hd] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, edgeOK] at h
    have hd' : depOf r ≠ 0 := fun e => by simp [e] at hd
    refine ⟨e78 ▸ h.1.1, h.1.2, fun e => absurd e hd', fun _ => ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩
  · rw [hd] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    have hd' : depOf r = 0 := Nat.eq_of_beq_eq_true hd
    exact ⟨e78 ▸ h.1.1, h.1.2, fun _ => h.2, fun e => absurd hd' e⟩

theorem vec_lt_vec (h : ∀ c < 695, chunkOK R c = true) {i j : Nat} (hij : i < j)
    (hj : j < remN) : vecOf (recAt R i) < vecOf (recAt R j) := by
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero i)
  | succ j ih =>
    have hs := (recOK_spec (recOK_of h (Nat.lt_of_succ_lt hj))).2.1
    have hs' : vecOf (recAt R j) < vecOf (recAt R (j + 1)) := hs.resolve_left (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
    · exact Nat.lt_trans (ih hij (Nat.lt_of_succ_lt hj)) hs'
    · exact hs'

theorem reachL_of_dep (h : ∀ c < 695, chunkOK R c = true) :
    ∀ d i, i < remN → depOf (recAt R i) = d → ReachL (vecOf (recAt R i)) := by
  intro d
  induction d with
  | zero =>
    intro i hi hd
    rw [(recOK_spec (recOK_of h hi)).2.2.1 hd]
    exact ReachL.seed
  | succ d ih =>
    intro i hi hd
    obtain ⟨hp, hpd, hv⟩ := (recOK_spec (recOK_of h hi)).2.2.2 (by omega)
    have hg : genOf (recAt R i) < 4 := by
      have : genOf (recAt R i) ≤ 3 := Nat.and_le_right
      omega
    rw [hv]
    exact ReachL.step _ hg (ih _ hp (by omega))

theorem rem_sound (h : ∀ c < 695, chunkOK R c = true) :
    (∀ i < remN, vecOf (recAt R i) < 2 ^ 78) ∧
      (∀ i j, i < j → j < remN → vecOf (recAt R i) < vecOf (recAt R j)) ∧
      ∀ i < remN, ReachL (vecOf (recAt R i)) :=
  ⟨fun _ hi => (recOK_spec (recOK_of h hi)).1, fun _ _ hij hj => vec_lt_vec h hij hj,
    fun i hi => reachL_of_dep h _ i hi rfl⟩

end CFSG.KC.Rem3069

end
