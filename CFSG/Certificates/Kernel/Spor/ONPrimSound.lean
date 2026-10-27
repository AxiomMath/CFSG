module

public import Certificates.Data.Kernel.Spor.ONPrimK
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CFSG.KS.ONPrim

open CFSG.KC.Enum CFSG.KS

variable {TT UU : Nat → Nat → Nat} {R C : Nat → Nat} {n : Nat}

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

def depOf (r : Nat) : Nat := fld(r, nat_lit 17, nat_lit 63)

def genOf (r : Nat) : Nat := fld(r, nat_lit 23, nat_lit 1)

def parOf (r : Nat) : Nat := Nat.land r (nat_lit 131071)

theorem genOf_lt (r : Nat) : genOf r < 2 := by
  have e : Nat.land (Nat.shiftRight r 23) 1 = Nat.shiftRight r 23 % 2 := Nat.and_one_is_mod _
  change Nat.land (Nat.shiftRight r 23) 1 < 2
  rw [e]
  exact Nat.mod_lt _ (by decide)

theorem primOK_spec {y r : Nat} (h : primOK TT UU R n y r = true) :
    labOf r < 5 ∧ repOf (labOf r) ≤ y ∧
      ((depOf r = 0 ∧ repOf (labOf r) = y ∧ labOf (R (UU 2 y)) = labOf r ∧
          labOf (R (UU 3 y)) = labOf r) ∨
        (depOf r ≠ 0 ∧ parOf r < n ∧ depOf (R (parOf r)) < depOf r ∧
          labOf (R (parOf r)) = labOf r ∧ TT (2 + genOf r) (parOf r) = y ∧
          labOf (R (UU (3 - genOf r) y)) = labOf r)) := by
  unfold primOK at h
  simp only [sB] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.blt_eq.mp h1, Nat.ble_eq.mp h2, ?_⟩
  cases hb : Nat.beq (Nat.land (Nat.shiftRight r (nat_lit 17)) (nat_lit 63)) (nat_lit 0) <;>
    rw [hb] at h <;> dsimp only at h
  · obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h5, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 h
    exact Or.inr ⟨Nat.ne_of_beq_eq_false hb, Nat.blt_eq.mp h3, Nat.blt_eq.mp h4,
      Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7⟩
  · obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
    exact Or.inl ⟨Nat.eq_of_beq_eq_true hb, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
      Nat.eq_of_beq_eq_true h5⟩

theorem primAt_eq (y : Nat) : primAt TT UU R n y =
    if primOK TT UU R n y (R y) = true then 2 ^ (17 * labOf (R y)) else 2 ^ 85 := by
  unfold primAt
  rw [sN]
  cases primOK TT UU R n y (R y) <;> simp [Nat.shiftLeft_eq]

theorem foldBlk_sum (g : Nat → Nat) (b : Nat) : ∀ len s,
    foldBlk b (fun i t => Nat.add (g i) t) len s = s + ∑ l ∈ Finset.range len, g (b + l)
  | 0, s => by simp [foldBlk]
  | len + 1, s => by
    change strictN (Nat.add (g (Nat.add b len)) s) (foldBlk b (fun i t => Nat.add (g i) t) len) = _
    rw [sN, foldBlk_sum g b len, Finset.sum_range_succ]
    simp only [Nat.add_eq]
    omega

theorem sum_blocks (f : Nat → Nat) (w : Nat) : ∀ k,
    ∑ s ∈ Finset.range k, ∑ l ∈ Finset.range w, f (w * s + l) = ∑ y ∈ Finset.range (w * k), f y
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, sum_blocks f w k, Nat.mul_succ, Finset.sum_range_add]

theorem primSizesP_lt : primSizesP < 2 ^ 85 := by decide +kernel

theorem primSizesP_eq : primSizesP = 1 + 6384 * 2 ^ 17 + 52136 * 2 ^ 34 + 58653 * 2 ^ 51 +
    5586 * 2 ^ 68 := by decide +kernel

theorem foldr_lab (hperm : ∀ x < n, TT 2 x < n ∧ TT 3 x < n)
    (hinv : ∀ g, g = 2 ∨ g = 3 → ∀ x < n, labOf (R (TT g x)) = labOf (R x)) {z : Nat}
    (hz : z < n) : ∀ ks : List Nat, (∀ k ∈ ks, k < 2) →
      ks.foldr (fun k z => TT (2 + k) z) z < n ∧
        labOf (R (ks.foldr (fun k z => TT (2 + k) z) z)) = labOf (R z)
  | [], _ => ⟨hz, rfl⟩
  | k :: ks, hk => by
    obtain ⟨h1, h2⟩ := foldr_lab hperm hinv hz ks fun j hj => hk j (List.mem_cons_of_mem _ hj)
    have hk2 := hk k List.mem_cons_self
    simp only [List.foldr_cons]
    have hg : 2 + k = 2 ∨ 2 + k = 3 := by omega
    refine ⟨?_, ?_⟩
    · rcases hg with e | e <;> rw [e]
      · exact (hperm _ h1).1
      · exact (hperm _ h1).2
    · rw [hinv _ hg _ h1, h2]

public section

@[expose] def primSizes : List Nat := [1, 6384, 52136, 58653, 5586]

@[expose] def primReps : List Nat := [0, 1, 2, 4, 9]

theorem repOf_eq : ∀ i < 5, repOf i = primReps.getD i 0
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem primHead_sound (h : primHead TT = true) : TT 2 0 = 0 ∧ TT 3 0 = 0 := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem prim_sound {w k : Nat}
    (hperm : ∀ x < n, TT 2 x < n ∧ UU 2 (TT 2 x) = x ∧ TT 3 x < n ∧ UU 3 (TT 3 x) = x)
    (hB : ∀ s < k, primBlk TT UU R C n w s = true) (hT : primTot C k = true) (hn : w * k = n)
    (hn17 : n < 131072) :
    (∀ y < n, labOf (R y) < 5 ∧ repOf (labOf (R y)) ≤ y) ∧
      (∀ g, g = 2 ∨ g = 3 → ∀ x < n, labOf (R (TT g x)) = labOf (R x)) ∧
      (∀ y < n, ∃ ks : List Nat, (∀ k ∈ ks, k < 2) ∧
        y = ks.foldr (fun k z => TT (2 + k) z) (repOf (labOf (R y)))) ∧
      (∀ i < 5, ((Finset.range n).filter fun y => labOf (R y) = i).card = primSizes.getD i 0) ∧
      (∀ i < 5, repOf i < n ∧ labOf (R (repOf i)) = i) := by
  have hsum : ∑ y ∈ Finset.range n, primAt TT UU R n y = primSizesP := by
    have h0 := Nat.eq_of_beq_eq_true hT
    change foldBlk 0 (fun s t => Nat.add (C s) t) k 0 = primSizesP at h0
    rw [foldBlk_sum] at h0
    simp only [Nat.zero_add] at h0
    have e := sum_blocks (fun y => primAt TT UU R n y) w k
    rw [hn] at e
    rw [← h0, ← e]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hb := Nat.eq_of_beq_eq_true (hB s (Finset.mem_range.1 hs))
    have e2 : primCnt TT UU R n (w * s) w = ∑ l ∈ Finset.range w, primAt TT UU R n (w * s + l) :=
      (foldBlk_sum _ _ _ _).trans (Nat.zero_add _)
    exact e2.symm.trans hb
  have hall : ∀ y < n, primOK TT UU R n y (R y) = true := by
    intro y hy
    by_contra hf
    have hle : primAt TT UU R n y ≤ ∑ y ∈ Finset.range n, primAt TT UU R n y :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hy)
    rw [hsum, primAt_eq, if_neg hf] at hle
    exact absurd primSizesP_lt (Nat.not_lt.2 hle)
  have hsp := fun y hy => primOK_spec (hall y hy)
  have hperm' : ∀ x < n, TT 2 x < n ∧ TT 3 x < n := fun x hx => ⟨(hperm x hx).1, (hperm x hx).2.2.1⟩
  have ha : ∀ y < n, labOf (R y) < 5 ∧ repOf (labOf (R y)) ≤ y :=
    fun y hy => ⟨(hsp y hy).1, (hsp y hy).2.1⟩
  have hc : ∀ g, g = 2 ∨ g = 3 → ∀ x < n, labOf (R (TT g x)) = labOf (R x) := by
    intro g hg x hx
    obtain ⟨hy, hUT, hUTp⟩ : TT g x < n ∧ UU g (TT g x) = x ∧ ∀ p < n, UU g (TT g p) = p := by
      rcases hg with rfl | rfl
      · exact ⟨(hperm x hx).1, (hperm x hx).2.1, fun p hp => (hperm p hp).2.1⟩
      · exact ⟨(hperm x hx).2.2.1, (hperm x hx).2.2.2, fun p hp => (hperm p hp).2.2.2⟩
    rcases (hsp _ hy).2.2 with ⟨_, _, h2, h3⟩ | ⟨_, hp, _, hlp, hTp, hU⟩
    · rcases hg with rfl | rfl
      · rw [← h2, hUT]
      · rw [← h3, hUT]
    · have hg2 := genOf_lt (R (TT g x))
      by_cases hgg : 2 + genOf (R (TT g x)) = g
      · rw [hgg] at hTp
        have hpx : parOf (R (TT g x)) = x := by rw [← hUTp _ hp, hTp, hUT]
        rw [← hlp, hpx]
      · have e3 : 3 - genOf (R (TT g x)) = g := by omega
        rw [e3, hUT] at hU
        exact hU.symm
  have hb : ∀ y < n, ∃ ks : List Nat, (∀ k ∈ ks, k < 2) ∧
      y = ks.foldr (fun k z => TT (2 + k) z) (repOf (labOf (R y))) := by
    suffices H : ∀ d, ∀ y < n, depOf (R y) = d → ∃ ks : List Nat, (∀ k ∈ ks, k < 2) ∧
        y = ks.foldr (fun k z => TT (2 + k) z) (repOf (labOf (R y))) from
      fun y hy => H _ y hy rfl
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
      intro y hy hd
      rcases (hsp y hy).2.2 with ⟨_, hr, _, _⟩ | ⟨_, hp, hdp, hlp, hTp, _⟩
      · exact ⟨[], fun k hk => absurd hk List.not_mem_nil, hr.symm⟩
      · obtain ⟨ks, hks, ep⟩ := ih _ (hd ▸ hdp) _ hp rfl
        refine ⟨genOf (R y) :: ks, ?_, ?_⟩
        · intro j hj
          rcases List.mem_cons.1 hj with e | e
          · rw [e]
            exact genOf_lt _
          · exact hks j e
        · rw [List.foldr_cons, ← hlp, ← ep, hTp]
  have hcnt : ∑ y ∈ Finset.range n, 2 ^ (17 * labOf (R y)) =
      ∑ i ∈ Finset.range 5, ((Finset.range n).filter fun y => labOf (R y) = i).card * 2 ^ (17 * i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range n) (t := Finset.range 5)
      (g := fun y => labOf (R y)) (fun y hy => Finset.mem_range.2 (ha y (Finset.mem_range.1 hy)).1)
      (fun y => 2 ^ (17 * labOf (R y)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_const_nat fun y hy => by rw [(Finset.mem_filter.1 hy).2]
  have hsum' : ∑ y ∈ Finset.range n, 2 ^ (17 * labOf (R y)) = primSizesP := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [primAt_eq, if_pos (hall y (Finset.mem_range.1 hy))]
  rw [hcnt, primSizesP_eq] at hsum'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum'
  have hle : ∀ i, ((Finset.range n).filter fun y => labOf (R y) = i).card < 131072 := fun i =>
    lt_of_le_of_lt ((Finset.card_filter_le _ _).trans (Finset.card_range n).le) hn17
  have hd : ∀ i < 5, ((Finset.range n).filter fun y => labOf (R y) = i).card =
      primSizes.getD i 0 := by
    have l0 := hle 0
    have l1 := hle 1
    have l2 := hle 2
    have l3 := hle 3
    have l4 := hle 4
    intro i hi
    interval_cases i <;> simp only [primSizes, List.getD_cons_zero, List.getD_cons_succ] <;> omega
  refine ⟨ha, hc, hb, hd, fun i hi => ?_⟩
  have hne : ((Finset.range n).filter fun y => labOf (R y) = i).Nonempty := by
    rw [← Finset.card_pos, hd i hi]
    interval_cases i <;> decide
  obtain ⟨y, hy⟩ := hne
  obtain ⟨hyn, hyl⟩ := Finset.mem_filter.1 hy
  have hyn' := Finset.mem_range.1 hyn
  have hrn : repOf i < n := lt_of_le_of_lt (hyl ▸ (ha y hyn').2) hyn'
  obtain ⟨ks, hks, ep⟩ := hb y hyn'
  rw [hyl] at ep
  have := (foldr_lab hperm' hc hrn ks hks).2
  rw [← ep, hyl] at this
  exact ⟨hrn, this.symm⟩

end

end CFSG.KS.ONPrim
