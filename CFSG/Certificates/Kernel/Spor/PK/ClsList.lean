module

public import CFSG.Certificates.Kernel.Spor.PK.Cls
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.M11Class

private theorem bpos_zero (nw pm S c x lo hi : Nat) :
    bpos nw pm S c x 0 lo hi = if lo < hi ∧ blk S nw pm lo = x then lo else c := by
  show nIf(bAnd(Nat.blt lo hi, Nat.beq (blk S nw pm lo) x), lo, c) = _
  simp only [nIf_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]

private theorem bpos_succ (nw pm S c x d lo hi : Nat) :
    bpos nw pm S c x (d + 1) lo hi =
      if hi ≤ lo + 1 then (if lo < hi ∧ blk S nw pm lo = x then lo else c)
      else if x < blk S nw pm ((lo + hi) >>> 1) then bpos nw pm S c x d lo ((lo + hi) >>> 1)
        else bpos nw pm S c x d ((lo + hi) >>> 1) hi := by
  show nIf(Nat.ble hi (Nat.succ lo),
      nIf(bAnd(Nat.blt lo hi, Nat.beq (blk S nw pm lo) x), lo, c),
      strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) (fun mid =>
        nIf(Nat.blt x (blk S nw pm mid), bpos nw pm S c x d lo mid,
          bpos nw pm S c x d mid hi))) = _
  simp only [nIf_eq, bAnd_eq, strictN_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq]
  rfl

theorem bpos_sound {nw S c x : Nat} : ∀ {d lo hi : Nat}, hi ≤ c →
    bpos nw (mask nw) S c x d lo hi < c →
      blk S nw (mask nw) (bpos nw (mask nw) S c x d lo hi) = x := by
  intro d
  induction d with
  | zero =>
    intro lo hi _ hlt
    rw [bpos_zero] at hlt ⊢
    by_cases h : lo < hi ∧ blk S nw (mask nw) lo = x
    · rw [if_pos h]
      exact h.2
    · rw [if_neg h] at hlt
      exact absurd hlt (Nat.lt_irrefl c)
  | succ d ih =>
    intro lo hi hhi hlt
    rw [bpos_succ] at hlt ⊢
    by_cases hle : hi ≤ lo + 1
    · rw [if_pos hle] at hlt ⊢
      by_cases h : lo < hi ∧ blk S nw (mask nw) lo = x
      · rw [if_pos h]
        exact h.2
      · rw [if_neg h] at hlt
        exact absurd hlt (Nat.lt_irrefl c)
    · rw [if_neg hle] at hlt ⊢
      have hmid : (lo + hi) >>> 1 ≤ hi := by
        rw [Nat.shiftRight_eq_div_pow]
        omega
      by_cases hx : x < blk S nw (mask nw) ((lo + hi) >>> 1)
      · rw [if_pos hx] at hlt ⊢
        exact ih (Nat.le_trans hmid hhi) hlt
      · rw [if_neg hx] at hlt ⊢
        exact ih hhi hlt

theorem bmem_sound {nw S c x : Nat} (h : bmem nw (mask nw) S c x = true) :
    ∃ q < c, blk S nw (mask nw) q = x := by
  have h1 : bpos nw (mask nw) S c x 32 0 c < c := by
    have h' : Nat.blt (bpos nw (mask nw) S c x 32 0 c) c = true := h
    rwa [Nat.blt_eq] at h'
  exact ⟨_, h1, bpos_sound (Nat.le_refl c) h1⟩

private theorem perm_range_of_cover {c : Nat} {l : List Nat} (hlen : l.length = c)
    (hcov : ∀ i < c, i ∈ l) : (List.range c).Perm l :=
  (List.subperm_of_subset List.nodup_range
    (fun i hi => hcov i (List.mem_range.1 hi))).perm_of_length_le
    (Nat.le_of_eq (by rw [hlen, List.length_range]))

private theorem bpos44_sound {SP c x : Nat} (h : bpos 44 17592186044415 SP c x 32 0 c < c) :
    blk SP 44 (mask 44) (bpos 44 17592186044415 SP c x 32 0 c) = x := by
  have hm : (17592186044415 : Nat) = mask 44 := rfl
  rw [hm] at h ⊢
  exact bpos_sound (Nat.le_refl c) h

private theorem maskP_nil (SP c : Nat) : maskP SP c [] = 0 := rfl

private theorem maskP_cons (SP c : Nat) (p : Nat × Nat) (L : List (Nat × Nat)) :
    maskP SP c (p :: L) = maskP SP c L ||| (1 <<< bpos 44 17592186044415 SP c p.1 32 0 c) := by
  obtain ⟨x, xi⟩ := p
  show strictN (maskP SP c L) (fun M => strictN (bpos 44 17592186044415 SP c x 32 0 c)
    (fun pos => Nat.lor M (Nat.shiftLeft 1 pos))) = _
  simp only [strictN_eq]
  rfl

private theorem testBit_maskP (SP c : Nat) (L : List (Nat × Nat)) (i : Nat) :
    (maskP SP c L).testBit i = true ↔ ∃ p ∈ L, bpos 44 17592186044415 SP c p.1 32 0 c = i := by
  induction L with
  | nil => simp [maskP_nil]
  | cons p L ih =>
    rw [maskP_cons, Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact Or.comm

theorem sameSet_perm {SP c : Nat} {L : List (Nat × Nat)}
    (h : sameSet SP c L = true) :
    (L.map Prod.fst).Perm ((List.range c).map fun q => blk SP 44 (mask 44) q) := by
  simp only [sameSet, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hlen : L.length = c := by rw [← lenP_eq]; exact h1
  have hM : maskP SP c L = 2 ^ c - 1 := by
    rw [h2, show Nat.shiftLeft 1 c = 2 ^ c from Nat.one_shiftLeft c]
    rfl
  have hbit : ∀ i, (∃ p ∈ L, bpos 44 17592186044415 SP c p.1 32 0 c = i) ↔ i < c := by
    intro i
    rw [← testBit_maskP, hM, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  have hlt : ∀ p ∈ L, bpos 44 17592186044415 SP c p.1 32 0 c < c :=
    fun p hp => (hbit _).1 ⟨p, hp, rfl⟩
  have hcov : ∀ i < c, i ∈ L.map fun p => bpos 44 17592186044415 SP c p.1 32 0 c := by
    intro i hi
    obtain ⟨p, hp, hpi⟩ := (hbit i).2 hi
    exact List.mem_map.2 ⟨p, hp, hpi⟩
  have hperm := perm_range_of_cover (by rw [List.length_map, hlen]) hcov
  have heq : L.map Prod.fst = (L.map fun p => bpos 44 17592186044415 SP c p.1 32 0 c).map
      (fun q => blk SP 44 (mask 44) q) := by
    rw [List.map_map]
    exact List.map_congr_left fun p hp => (bpos44_sound (hlt p hp)).symm
  rw [heq]
  exact (hperm.map _).symm

theorem blk_packL {S : List Nat} (hS : ∀ x ∈ S, x < 2 ^ 44) {q : Nat} (hq : q < S.length) :
    blk (packL 44 S) 44 (mask 44) q = S.getD q 0 := by
  have hf : ∀ i < S.length, S.getD i 0 < 2 ^ 44 := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hS _ (List.getElem_mem hi)
  rw [packL_eq hS, blk_eq]
  exact fd_enc hf hq

theorem nodup_of_increasing {SP c : Nat}
    (h : allN (Nat.sub c 1) (fun k => Nat.blt (blk SP 44 17592186044415 k)
      (blk SP 44 17592186044415 (Nat.succ k))) = true) :
    ((List.range c).map fun q => blk SP 44 (mask 44) q).Nodup := by
  have hm : (17592186044415 : Nat) = mask 44 := rfl
  rw [hm, allN_iff] at h
  have step : ∀ i, i + 1 < c → blk SP 44 (mask 44) i < blk SP 44 (mask 44) (i + 1) := by
    intro i hi
    have h1 := h i (show i < c - 1 by omega)
    rwa [Nat.blt_eq] at h1
  have mono : ∀ d i, i + d + 1 < c → blk SP 44 (mask 44) i < blk SP 44 (mask 44) (i + d + 1) := by
    intro d
    induction d with
    | zero => intro i hi; exact step i hi
    | succ d ih =>
      intro i hi
      exact Nat.lt_trans (ih i (by omega)) (step (i + d + 1) (by omega))
  refine List.Nodup.map_on ?_ List.nodup_range
  intro x hx y hy hxy
  rw [List.mem_range] at hx hy
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨d, rfl⟩ : ∃ d, y = x + d + 1 := ⟨y - x - 1, by omega⟩
    exact absurd hxy (Nat.ne_of_lt (mono d x hy))
  · obtain ⟨d, rfl⟩ : ∃ d, x = y + d + 1 := ⟨x - y - 1, by omega⟩
    exact absurd hxy.symm (Nat.ne_of_lt (mono d y hx))

private theorem testBit_or_shiftLeft (M q i : Nat) :
    (M ||| 1 <<< q).testBit i = (M.testBit i || decide (q = i)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

private theorem fold_spec (c : Nat) (q : Nat → Nat) (f : Nat → Nat → Nat)
    (hf : ∀ M k, f M k =
      if q k < c ∧ M.testBit (q k) = false then M ||| 1 <<< q k else M ||| 1 <<< c) (j : Nat) :
    ((List.range j).foldl f 0).testBit c = false →
      (∀ k < j, q k < c) ∧ (∀ k < j, ∀ k' < j, q k = q k' → k = k') ∧
        ∀ i, ((List.range j).foldl f 0).testBit i = true ↔ ∃ k < j, q k = i := by
  induction j with
  | zero =>
    intro _
    refine ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (Nat.not_lt_zero k),
      fun i => ?_⟩
    simp
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range j).foldl f 0 = M at ih ⊢
    rw [hf]
    by_cases hcond : q j < c ∧ M.testBit (q j) = false
    · rw [if_pos hcond]
      intro hc
      rw [testBit_or_shiftLeft, Bool.or_eq_false_iff] at hc
      obtain ⟨hlt, hinj, hbits⟩ := ih hc.1
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact hlt k hk
        · exact hcond.1
      · intro k hk k' hk' hkk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
        · exact hinj k hk k' hk' hkk
        · exfalso
          have := (hbits (q k)).2 ⟨k, hk, rfl⟩
          rw [hkk, hcond.2] at this
          exact Bool.false_ne_true this
        · exfalso
          have := (hbits (q k')).2 ⟨k', hk', rfl⟩
          rw [← hkk, hcond.2] at this
          exact Bool.false_ne_true this
        · rfl
      · intro i
        rw [testBit_or_shiftLeft, Bool.or_eq_true, hbits i, decide_eq_true_eq]
        constructor
        · rintro (⟨k, hk, hki⟩ | h)
          · exact ⟨k, Nat.lt_succ_of_lt hk, hki⟩
          · exact ⟨j, Nat.lt_succ_self j, h⟩
        · rintro ⟨k, hk, hki⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact Or.inl ⟨k, hk, hki⟩
          · exact Or.inr hki
    · rw [if_neg hcond]
      intro hc
      rw [testBit_or_shiftLeft, Bool.or_eq_false_iff] at hc
      simp at hc

private theorem perm_map_of_inj {c : Nat} {f g q : Nat → Nat} (hlt : ∀ k < c, q k < c)
    (hinj : ∀ k < c, ∀ k' < c, q k = q k' → k = k') (hfg : ∀ k < c, g (q k) = f k) :
    ((List.range c).map f).Perm ((List.range c).map g) := by
  have hnodup : ((List.range c).map q).Nodup :=
    List.Nodup.map_on
      (fun x hx y hy hxy => hinj x (List.mem_range.1 hx) y (List.mem_range.1 hy) hxy)
      List.nodup_range
  have hperm : ((List.range c).map q).Perm (List.range c) :=
    (List.subperm_of_subset hnodup (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact List.mem_range.2 (hlt k (List.mem_range.1 hk)))).perm_of_length_le (by simp)
  have heq : (List.range c).map f = ((List.range c).map q).map g := by
    rw [List.map_map]
    exact List.map_congr_left fun k hk => (hfg k (List.mem_range.1 hk)).symm
  rw [heq]
  exact hperm.map g

private theorem fold_pos {c S : Nat} (x : Nat → Nat)
    (hfold : Nat.shiftRight (foldUp c (fun k M =>
        strictN (bpos 44 17592186044415 S c (x k) 32 0 c)
          (fun q => nIf(bAnd(Nat.blt q c, bIf(hasBit M q, false, true)),
            Nat.lor M (Nat.shiftLeft 1 q), Nat.lor M (Nat.shiftLeft 1 c)))) 0) c = 0) :
    (∀ k < c, bpos 44 17592186044415 S c (x k) 32 0 c < c) ∧
      ∀ k < c, ∀ k' < c, bpos 44 17592186044415 S c (x k) 32 0 c =
        bpos 44 17592186044415 S c (x k') 32 0 c → k = k' := by
  rw [foldUp_eq] at hfold
  have hfin := Nat.testBit_lt_two_pow ((shiftRight_eq_zero_iff _ _).1 hfold)
  refine (fun key => ⟨key.1, key.2.1⟩)
    (fold_spec c (fun k => bpos 44 17592186044415 S c (x k) 32 0 c) _ ?_ c hfin)
  intro M k
  simp only [strictN_eq, nIf_eq, bAnd_eq, bIf_eq, hasBit_eq, Bool.and_eq_true, Nat.blt_eq]
  generalize bpos 44 17592186044415 S c (x k) 32 0 c = q
  by_cases h1 : q < c <;> by_cases h2 : M.testBit q = true <;> simp [h1, h2] <;> rfl

theorem clsOK_spec {A Ai B Bi mx cap R Bl S c : Nat} {P Lb : List Nat}
    (h : clsOK 11 4 15 44 17592186044415 A Ai B Bi mx cap R Bl P Lb S c = true) :
    ordC 11 4 15 R = mx ∧ blk Bl 44 (mask 44) 0 = R ∧
      (∀ k < c, (∃ q < c, blk S 44 (mask 44) q = conjK 11 4 15 A Ai (blk S 44 (mask 44) k)) ∧
        ∃ q < c, blk S 44 (mask 44) q = conjK 11 4 15 B Bi (blk S 44 (mask 44) k)) ∧
      (∀ k < c, 0 < k → ∃ p < k, blk Bl 44 (mask 44) k = conjK 11 4 15 A Ai (blk Bl 44 (mask 44) p) ∨
        blk Bl 44 (mask 44) k = conjK 11 4 15 B Bi (blk Bl 44 (mask 44) p)) ∧
      ((List.range c).map fun k => blk Bl 44 (mask 44) k).Perm
        ((List.range c).map fun q => blk S 44 (mask 44) q) := by
  simp only [clsOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨-, hord, hR, -, -, -, -, hclos, htree, hfold⟩ := h
  refine ⟨hord, hR, ?_, ?_, ?_⟩
  · intro k hk
    have h1 := allN_iff.1 hclos k hk
    simp only [strictB_eq, Bool.and_eq_true] at h1
    exact ⟨bmem_sound h1.1, bmem_sound h1.2⟩
  · intro k hk hpos
    have h1 := allN_iff.1 htree k hk
    have hk0 : Nat.beq k 0 = false := by
      cases hb : Nat.beq k 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) (Nat.pos_iff_ne_zero.1 hpos)
    simp only [hk0, strictB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, nIf_eq] at h1
    obtain ⟨hp, hl, he⟩ := h1
    refine ⟨nget P k, hp, ?_⟩
    by_cases hl0 : nget Lb k = 0
    · rw [if_pos hl0] at he
      exact Or.inl he
    · rw [if_neg hl0] at he
      exact Or.inr he
  · obtain ⟨hlt, hinj⟩ := fold_pos (fun k => blk Bl 44 17592186044415 k) hfold
    exact perm_map_of_inj hlt hinj fun k hk => bpos44_sound (hlt k hk)

end CFSG.KS.PK

end
