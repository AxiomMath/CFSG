module

public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Base
public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.Kernel.SporSch.HNXOrb
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch

theorem count_foldBlk_succ (b : Nat) (f : Nat → Nat → Nat) (l s : Nat) :
    foldBlk b f (l + 1) s = foldBlk b f l (f (b + l) s) := by
  have e : foldBlk b f (l + 1) s = strictN (f (b + l) s) (foldBlk b f l) := rfl
  rw [e, strictN_eq]

theorem count_foldBlk_eq (b : Nat) (f : Nat → Nat → Nat) (len s : Nat) :
    foldBlk b f len s = (List.range len).foldr (fun l s => f (b + l) s) s := by
  induction len generalizing s with
  | zero => rfl
  | succ len ih =>
    rw [count_foldBlk_succ, ih, List.range_succ, List.foldr_append, List.foldr_cons,
      List.foldr_nil]

theorem count_foldr_range_add (f : Nat → Nat → Nat) (a b s : Nat) :
    (List.range (a + b)).foldr f s =
      (List.range a).foldr f ((List.range b).foldr (fun l s => f (a + l) s) s) := by
  rw [List.range_add, List.foldr_append, List.foldr_map]

theorem count_shiftLeft_six (x : Nat) : Nat.shiftLeft x (nat_lit 6) = x * 64 := by
  change x <<< 6 = x * 64
  rw [Nat.shiftLeft_eq]

theorem count_shiftRight_six (n : Nat) : Nat.shiftRight n (nat_lit 6) = n / 64 :=
  Nat.shiftRight_eq_div_pow n 6

theorem count_land_63 (n : Nat) : Nat.land n (nat_lit 63) = n % 64 :=
  Nat.and_two_pow_sub_one_eq_mod n 6

theorem count_foldN_rec_eq (f : Nat → Nat → Nat) (h : Nat) : ∀ x : Nat,
    Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) h x
      = (List.range (h * 64)).foldr f x := by
  induction h with
  | zero => intro x; rfl
  | succ h ih =>
    intro x
    have hs : Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
        (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
        (h + 1) x
        = strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) x)
            (Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
              (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
              h) :=
      rfl
    rw [hs, strictN_eq, ih, count_foldBlk_eq, count_shiftLeft_six h,
      Nat.add_one_mul h 64, count_foldr_range_add f (h * 64) 64 x]

theorem count_foldN_eq (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = (List.range n).foldr f s := by
  refine Eq.trans (count_foldN_rec_eq f (Nat.shiftRight n (nat_lit 6))
    (foldBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) s)) ?_
  rw [count_foldBlk_eq, count_shiftLeft_six, count_land_63, count_shiftRight_six,
    ← count_foldr_range_add f (n / 64 * 64) (n % 64) s, Nat.div_add_mod' n 64]

theorem count_foldr_add (CNT : Nat → Nat) (n s : Nat) :
    (List.range n).foldr (fun b acc => Nat.add acc (CNT b)) s =
      s + ∑ b ∈ Finset.range n, CNT b := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih,
      Finset.sum_range_succ]
    change s + CNT n + _ = _
    omega

theorem sumK_eq (CNT : Nat → Nat) : sumK CNT = ∑ b ∈ Finset.range 17813, CNT b := by
  unfold sumK
  rw [count_foldN_eq, count_foldr_add, Nat.zero_add]

theorem count_nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = (if c = true then t else e) := by
  cases c <;> rfl

theorem hnxC_eq (b : Nat) : hnxC b = if b < 17812 then 64 else 32 := by
  unfold hnxC
  rw [count_nIf_eq]
  by_cases hb : b < 17812
  · have : Nat.blt b 17812 = true := Nat.blt_eq.mpr hb
    simp only [this, hb, if_true]
  · have : Nat.blt b 17812 = false := by
      cases h : Nat.blt b 17812
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hb
    simp only [this, hb, if_false]
    rfl

theorem hnxS_eq (m : Nat) : hnxS m = if m < 17812 then 64 else 31 := by
  unfold hnxS
  rw [count_nIf_eq]
  by_cases hb : m < 17812
  · have : Nat.blt m 17812 = true := Nat.blt_eq.mpr hb
    simp only [this, hb, if_true]
  · have : Nat.blt m 17812 = false := by
      cases h : Nat.blt m 17812
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hb
    simp only [this, hb, if_false]
    rfl

theorem count_sum_blocks (f : Nat → Nat) (N : Nat) :
    ∑ b ∈ Finset.range N, ∑ r ∈ Finset.range 64, f (64 * b + r) =
      ∑ i ∈ Finset.range (64 * N), f i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]

theorem sum_leaves (f : Nat → Nat) :
    ∑ b ∈ Finset.range 17813, ∑ r ∈ Finset.range (hnxC b), f (64 * b + r) =
      ∑ i ∈ Finset.range 1140000, f i := by
  rw [Finset.sum_range_succ]
  have h1 : ∑ b ∈ Finset.range 17812, ∑ r ∈ Finset.range (hnxC b), f (64 * b + r) =
      ∑ b ∈ Finset.range 17812, ∑ r ∈ Finset.range 64, f (64 * b + r) := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [hnxC_eq, if_pos (Finset.mem_range.mp hb)]
  have h2 : hnxC 17812 = 32 := by
    rw [hnxC_eq, if_neg (Nat.lt_irrefl _)]
  rw [h1, h2, count_sum_blocks, show (1140000 : Nat) = 64 * 17812 + 32 from rfl,
    Finset.sum_range_add]

theorem first_of_count {n : Nat} {pp : Nat → Nat} {q : Nat → Nat → Nat}
    (hq : ∀ i < n, ∀ s < 2, q s i < n) (hpp0 : pp 0 = 0)
    (hcnt : ∑ i ∈ Finset.range n, ((if pp (q 0 i) = 2 * i + 1 then 1 else 0) +
      (if pp (q 1 i) = 2 * i + 2 then 1 else 0)) = n - 1) :
    ∀ t, 0 < t → t < n → ∃ i < n, ∃ s < 2, q s i = t ∧ pp t = 2 * i + s + 1 := by
  classical
  intro t ht0 htn
  set E := (Finset.range n ×ˢ Finset.range 2).filter
    (fun p : Nat × Nat => pp (q p.2 p.1) = 2 * p.1 + p.2 + 1) with hE
  have hcard : E.card = n - 1 := by
    rw [hE, Finset.card_filter, Finset.sum_product, ← hcnt]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    rfl
  have hsub : E.image (fun p => q p.2 p.1) ⊆ (Finset.range n).erase 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨⟨i, s⟩, hp, rfl⟩ := hx
    rw [hE, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨⟨hi, hs⟩, he⟩ := hp
    rw [Finset.mem_erase, Finset.mem_range]
    refine ⟨fun h0 => ?_, hq i hi s hs⟩
    simp only at h0 he
    rw [h0, hpp0] at he
    omega
  have hinj : Set.InjOn (fun p : Nat × Nat => q p.2 p.1) E := by
    intro a ha b hb hab
    rw [Finset.mem_coe, hE, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_range] at ha hb
    simp only at hab
    have h1 := ha.2
    have h2 := hb.2
    rw [hab] at h1
    have : 2 * a.1 + a.2 = 2 * b.1 + b.2 := by omega
    have e1 : a.1 = b.1 := by omega
    have e2 : a.2 = b.2 := by omega
    exact Prod.ext e1 e2
  have hcard2 : (E.image (fun p => q p.2 p.1)).card = ((Finset.range n).erase 0).card := by
    rw [Finset.card_image_of_injOn hinj, hcard, Finset.card_erase_of_mem
      (Finset.mem_range.mpr (by omega)), Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard2.ge
  have ht : t ∈ (Finset.range n).erase 0 := by
    rw [Finset.mem_erase, Finset.mem_range]
    exact ⟨by omega, htn⟩
  rw [← heq, Finset.mem_image] at ht
  obtain ⟨⟨i, s⟩, hp, hqt⟩ := ht
  rw [hE, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  simp only at hqt hp
  refine ⟨i, hp.1.1, s, hp.1.2, hqt, ?_⟩
  rw [← hqt]
  exact hp.2

theorem count_sortChunk_spec (T : Nat → Nat) (RB n SG : Nat) : ∀ c : Nat,
    sortChunk T RB n SG c = true → ∀ k < c,
      fldW SG (21 * k) 21 < n ∧ fldW SG (21 * (k + 1)) 21 < n ∧
      fldW (getRec T RB (fldW SG (21 * k) 21)) 0 399 <
        fldW (getRec T RB (fldW SG (21 * (k + 1)) 21)) 0 399
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | c + 1, h, k, hk => by
    have h' : Bool.rec (motive := fun _ => Bool) false (sortChunk T RB n SG c)
        (bAnd(Nat.blt (fldW SG (21 * c) 21) n, bAnd(Nat.blt (fldW SG (21 * (c + 1)) 21) n,
          Nat.blt (fldW (getRec T RB (fldW SG (21 * c) 21)) 0 399)
            (fldW (getRec T RB (fldW SG (21 * (c + 1)) 21)) 0 399)))) = true := h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact count_sortChunk_spec T RB n SG c h2 k hk
    · obtain ⟨a1, h1⟩ := (CFSG.KS.bAnd_iff _ _).1 h1
      obtain ⟨a2, a3⟩ := (CFSG.KS.bAnd_iff _ _).1 h1
      exact ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a2, Nat.blt_eq.mp a3⟩

noncomputable def count_sig (SGT : Nat → Nat) (p : Nat) : Nat :=
  fldW (SGT (p / 64)) (21 * (p % 64)) 21

theorem count_link {SGT : Nat → Nat} (hl : linkK SGT = true) :
    ∀ m < 17812, fldW (SGT m) 1344 21 = fldW (SGT (m + 1)) 0 21 := by
  intro m hm
  exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec hl m hm)

theorem count_step {T SGT : Nat → Nat}
    (hs : ∀ m < 17813, sortChunk T 464 1140000 (SGT m) (hnxS m) = true)
    (hl : linkK SGT = true) : ∀ p < 1139999,
      count_sig SGT p < 1140000 ∧ count_sig SGT (p + 1) < 1140000 ∧
      xv T (count_sig SGT p) < xv T (count_sig SGT (p + 1)) := by
  intro p hp
  have hm : p / 64 < 17813 := by omega
  have hk : p % 64 < hnxS (p / 64) := by
    rw [hnxS_eq]
    split <;> omega
  have H := count_sortChunk_spec T 464 1140000 (SGT (p / 64)) _ (hs _ hm) _ hk
  have hnext : count_sig SGT (p + 1) = fldW (SGT (p / 64)) (21 * (p % 64 + 1)) 21 := by
    unfold count_sig
    by_cases h63 : p % 64 = 63
    · have hm' : p / 64 < 17812 := by omega
      have e1 : (p + 1) / 64 = p / 64 + 1 := by omega
      have e2 : (p + 1) % 64 = 0 := by omega
      rw [e1, e2, h63, ← count_link hl _ hm']
    · have e1 : (p + 1) / 64 = p / 64 := by omega
      have e2 : (p + 1) % 64 = p % 64 + 1 := by omega
      rw [e1, e2]
  rw [hnext]
  exact H

theorem count_sig_lt {T SGT : Nat → Nat}
    (hs : ∀ m < 17813, sortChunk T 464 1140000 (SGT m) (hnxS m) = true)
    (hl : linkK SGT = true) : ∀ p < 1140000, count_sig SGT p < 1140000 := by
  intro p hp
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · exact (count_step hs hl 0 (by omega)).1
  · have := (count_step hs hl (p - 1) (by omega)).2.1
    rwa [Nat.sub_add_cancel hp0] at this

theorem count_mono {T SGT : Nat → Nat}
    (hs : ∀ m < 17813, sortChunk T 464 1140000 (SGT m) (hnxS m) = true)
    (hl : linkK SGT = true) (p : Nat) : ∀ d, p + d + 1 < 1140000 →
      xv T (count_sig SGT p) < xv T (count_sig SGT (p + d + 1)) := by
  intro d
  induction d with
  | zero => intro h; exact (count_step hs hl p (by omega)).2.2
  | succ d ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := (count_step hs hl (p + d + 1) (by omega)).2.2
    rw [show p + (d + 1) + 1 = p + d + 1 + 1 by omega]
    exact Nat.lt_trans h1 h2

theorem count_sig_inj {T SGT : Nat → Nat}
    (hs : ∀ m < 17813, sortChunk T 464 1140000 (SGT m) (hnxS m) = true)
    (hl : linkK SGT = true) : ∀ p < 1140000, ∀ p' < 1140000,
      xv T (count_sig SGT p) = xv T (count_sig SGT p') → p = p' := by
  intro p hp p' hp' he
  rcases Nat.lt_trichotomy p p' with h | h | h
  · have := count_mono hs hl p (p' - p - 1) (by omega)
    rw [show p + (p' - p - 1) + 1 = p' by omega] at this
    omega
  · exact h
  · have := count_mono hs hl p' (p - p' - 1) (by omega)
    rw [show p' + (p - p' - 1) + 1 = p by omega] at this
    omega

theorem count_sig_surj {T SGT : Nat → Nat}
    (hs : ∀ m < 17813, sortChunk T 464 1140000 (SGT m) (hnxS m) = true)
    (hl : linkK SGT = true) : ∀ i < 1140000, ∃ p < 1140000, count_sig SGT p = i := by
  classical
  intro i hi
  have hsub : (Finset.range 1140000).image (count_sig SGT) ⊆ Finset.range 1140000 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact Finset.mem_range.mpr (count_sig_lt hs hl p (Finset.mem_range.mp hp))
  have hinj : Set.InjOn (count_sig SGT) (Finset.range 1140000 : Finset Nat) := by
    intro a ha b hb hab
    exact count_sig_inj hs hl a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb)
      (congrArg (xv T) hab)
  have hcard : (Finset.range 1140000).card ≤
      ((Finset.range 1140000).image (count_sig SGT)).card := by
    rw [Finset.card_image_of_injOn hinj]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hi' : i ∈ (Finset.range 1140000).image (count_sig SGT) := by
    rw [heq]; exact Finset.mem_range.mpr hi
  rw [Finset.mem_image] at hi'
  obtain ⟨p, hp, hpi⟩ := hi'
  exact ⟨p, Finset.mem_range.mp hp, hpi⟩

theorem sort_inj {T SGT : Nat → Nat}
    (hs : ∀ m < 17813, sortChunk T 464 1140000 (SGT m) (hnxS m) = true)
    (hl : linkK SGT = true) : ∀ i < 1140000, ∀ j < 1140000, xv T i = xv T j → i = j := by
  intro i hi j hj he
  obtain ⟨p, hp, rfl⟩ := count_sig_surj hs hl i hi
  obtain ⟨p', hp', rfl⟩ := count_sig_surj hs hl j hj
  rw [count_sig_inj hs hl p hp p' hp' he]

end CFSG.KS.SporSch.HNXP

end
