module

public import CFSG.Sporadic.He.FpSpec
public import Certificates.Data.E27Table

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Sporadic.He.Native

theorem buildN_inv {α : Type} [Inhabited α] (init : Array α) (step : Array α → ℕ → α)
    (P : ℕ → α → Prop) (N : ℕ) (h0 : ∀ k < init.size, P k init[k]!)
    (hs : ∀ n < N, ∀ r : Array α, r.size = init.size + n → (∀ k < r.size, P k r[k]!) →
      P r.size (step r r.size)) :
    (buildN init step N).size = init.size + N ∧ ∀ k < init.size + N, P k (buildN init step N)[k]! := by
  induction N with
  | zero => simpa [buildN] using h0
  | succ N ih =>
    obtain ⟨hsz, hP⟩ := ih (fun n hn => hs n (by omega))
    set r := buildN init step N with hr
    have hb : buildN init step (N + 1) = r.push (step r r.size) := rfl
    have hsz' : (buildN init step (N + 1)).size = init.size + (N + 1) := by
      rw [hb, Array.size_push, hsz]; rfl
    refine ⟨hsz', fun k hk => ?_⟩
    rw [hb]
    by_cases hkr : k < r.size
    · have : (r.push (step r r.size))[k]! = r[k]! := by
        rw [getElem!_pos _ k (by simp; omega), getElem!_pos _ k hkr, Array.getElem_push_lt hkr]
      rw [this]
      exact hP k (by omega)
    · have hk' : k = r.size := by omega
      subst hk'
      have : (r.push (step r r.size))[r.size]! = step r r.size := by
        rw [getElem!_pos _ _ (by simp)]
        simp
      rw [this]
      exact hs N (by omega) r hsz (fun k hk => hP k (by omega))

theorem matEqB_true {p d : ℕ} {X Y : Array (Array ℕ)} (h : matEqB p d X Y = true) :
    toMat p d X = toMat p d Y := by
  unfold matEqB at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  ext i j
  rw [toMat_apply, toMat_apply, ZMod.natCast_eq_natCast_iff']
  exact h i.val i.isLt j.val j.isLt

theorem matEqB_false {p d : ℕ} {X Y : Array (Array ℕ)} (h : matEqB p d X Y = false) :
    toMat p d X ≠ toMat p d Y := by
  intro heq
  unfold matEqB at h
  have : ¬ ∀ i, i < d → ∀ j, j < d → (X[i]!)[j]! % p = (Y[i]!)[j]! % p := by
    intro hall
    have : (List.range d).all (fun i => (List.range d).all fun j =>
        (X[i]!)[j]! % p == (Y[i]!)[j]! % p) = true := by
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
      exact hall
    rw [this] at h
    exact Bool.noConfusion h
  push Not at this
  obtain ⟨i, hi, j, hj, hne⟩ := this
  apply hne
  have := congrFun (congrFun heq ⟨i, hi⟩) ⟨j, hj⟩
  rw [toMat_apply, toMat_apply, ZMod.natCast_eq_natCast_iff'] at this
  exact this

end CFSG.HardMathSupport.Foote.E27
