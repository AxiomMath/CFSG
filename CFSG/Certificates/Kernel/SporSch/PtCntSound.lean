module

public import CFSG.Certificates.Kernel.SporSch.ChainIdxSound
public import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.SporSch.PtCnt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Certificates
open CFSG.Sporadic.Schreier CFSG.Certificates.ChainArrays Finset
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

theorem sum_list_range (c : Nat) (g : Nat → Nat) :
    ((List.range c).map g).sum = ∑ k ∈ range c, g k := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem sum_map_getD (f : Nat → Nat) : ∀ CS : List Nat,
    (CS.map f).sum = ∑ b ∈ range CS.length, f (CS.getD b 0)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.sum_cons, List.length_cons, sum_range_succ', sum_map_getD f l]
    simp [Nat.add_comm]

theorem foldUp_add {F : Nat → Nat → Nat} {g : Nat → Nat} (hF : ∀ t s, F t s = s + g t)
    (len s : Nat) : foldUp len F s = s + ∑ t ∈ range len, g t := by
  rw [CFSG.KC.Pack.foldUp_eq]
  induction len generalizing s with
  | zero => simp
  | succ len ih => rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      hF, sum_range_succ, Nat.add_assoc]

theorem sum_blocks (f : Nat → Nat) (L : Nat) : ∀ B,
    ∑ b ∈ range B, ∑ l ∈ range L, f (b * L + l) = ∑ k ∈ range (B * L), f k
  | 0 => by simp
  | B + 1 => by
    rw [sum_range_succ, sum_blocks f L B, Nat.succ_mul, sum_range_add]

theorem sum_range_ind {f : Nat → Nat} {c M : Nat} (hc : c ≤ M) :
    ∑ k ∈ range M, (if k < c then f k else 0) = ∑ k ∈ range c, f k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  rw [sum_range_add]
  have h1 : ∑ k ∈ range d, (if c + k < c then f (c + k) else 0) = 0 :=
    sum_eq_zero fun k _ => ite_eq_right (by omega)
  rw [h1, Nat.add_zero]
  exact sum_congr rfl fun k hk => ite_eq_left (mem_range.1 hk)

variable {n w m nw BP mx my r s : Nat} {LR TR : Nat → Nat} {R : List Nat}

noncomputable abbrev dJ (w m BP mx my r s : Nat) (R T : List Nat) : Nat := stepJ w m BP 3 mx my r s R T 0

theorem stepJ_add (T : List Nat) (c : Nat) :
    stepJ w m BP 3 mx my r s R T c = c + dJ w m BP mx my r s R T := by
  unfold dJ stepJ
  cases ordF w m BP 3 (apL w m T) mx
  · cases ordF w m BP 3 (apL w m T) my
    · rfl
    · change c + 1048576 + _ = c + (0 + 1048576 + _)
      omega
  · rfl

theorem dJ_mod (T : List Nat) : dJ w m BP mx my r s R T % 1048576 =
    if ordF w m BP 3 (apL w m T) mx = true then 1 else 0 := by
  have key : ∀ b : Bool,
      (0 + 1048576 + Bool.rec (motive := fun _ => Nat) 0 1099511627776 b) % 1048576 = 0 := by
    intro b
    cases b <;> rfl
  unfold dJ stepJ
  cases h1 : ordF w m BP 3 (apL w m T) mx
  · cases h2 : ordF w m BP 3 (apL w m T) my
    · rfl
    · exact key _
  · rfl

variable (n w m nw BP mx my r s LR TR R) in
noncomputable abbrev T3 (k0 k1 k2 : Nat) : List Nat :=
  [TR (roff n nw (LR 0) + k0), TR (roff n nw (LR 1) + k1), TR (roff n nw (LR 2) + k2)]

theorem enumJ_succ (d i : Nat) (L : List Nat) (c : Nat) :
    enumJ n w m nw BP 3 mx my r s LR TR R (d + 1) i L c =
      foldUp (rcnt (LR i)) (fun k c => enumJ n w m nw BP 3 mx my r s LR TR R d (i + 1)
        (TR (roff n nw (LR i) + k) :: L) c) c := by
  change strictN (LR i) (fun Q => foldUp (rcnt Q) (fun k c => strictN (TR (roff n nw Q + k))
    (fun t => enumJ n w m nw BP 3 mx my r s LR TR R d (i + 1) (t :: L) c)) c) = _
  rw [CIdx.strictN_eq]
  simp only [CIdx.strictN_eq]

theorem cntJ_eq (k0 : Nat) : cntJ n w m nw BP 3 mx my r s LR TR R k0 =
    ∑ k1 ∈ range (rcnt (LR 1)), ∑ k2 ∈ range (rcnt (LR 2)),
      dJ w m BP mx my r s R (T3 n nw LR TR k0 k1 k2) := by
  unfold cntJ
  rw [CIdx.strictN_eq, CIdx.strictN_eq]
  change enumJ n w m nw BP 3 mx my r s LR TR R (1 + 1) 1 _ 0 = _
  rw [enumJ_succ, foldUp_add (g := fun k1 => ∑ k2 ∈ range (rcnt (LR 2)),
    dJ w m BP mx my r s R (T3 n nw LR TR k0 k1 k2)), Nat.zero_add]
  intro k1 c
  rw [enumJ_succ, foldUp_add (g := fun k2 => dJ w m BP mx my r s R (T3 n nw LR TR k0 k1 k2))]
  intro k2 c'
  change stepJ w m BP 3 mx my r s R _ c' = _
  rw [stepJ_add]
  rfl

theorem cntJB_eq (lo len : Nat) : cntJB n w m nw BP 3 mx my r s LR TR R lo len =
    ∑ l ∈ range len, if lo + l < rcnt (LR 0) then cntJ n w m nw BP 3 mx my r s LR TR R (lo + l)
      else 0 := by
  unfold cntJB
  rw [foldUp_add, Nat.zero_add]
  intro l c
  rw [CIdx.strictN_eq]
  change Bool.rec (motive := fun _ => Nat) c (c + _) (Nat.blt (lo + l) (rcnt (LR 0))) = _
  by_cases h : lo + l < rcnt (LR 0)
  · rw [show Nat.blt (lo + l) (rcnt (LR 0)) = true by rw [Nat.blt_eq]; exact h, ite_eq_left h]
    rfl
  · rw [show Nat.blt (lo + l) (rcnt (LR 0)) = false from Bool.eq_false_iff.2 fun e =>
      h (by rw [Nat.blt_eq] at e; exact e), ite_eq_right h, Nat.add_zero]

theorem countP_products_cons {M : Type} [Monoid M] (p : M → Bool) (Gs : List M)
    (rest : List (List M)) : (products (Gs :: rest)).countP p =
      (Gs.map fun t => (products rest).countP fun h => p (t * h)).sum := by
  rw [products, List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [Function.comp_apply, List.countP_map]
  rfl

section Chain

variable {n w kS kO BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}
  (hQ : ChainCK n w PS PSI LR TR TRI kS kO 3 BP S base D)
include hQ

theorem n32 : n < 2 ^ 32 := by have := n_lt hQ; omega

theorem rep_levTable {i k : Nat} (hi : i < 3) (hk : k < sz n S base i) :
    CFSG.Sporadic.Th.Rep n (levTable n (lev n S base i) k) (trP n S base i k) := by
  intro x hx
  have hr := rep_tr (hd hQ) (by rw [base_size hQ]; exact hi) hk
  rw [CFSG.Sporadic.Th.idx_of_lt _ hx, levTable, CFSG.Sporadic.Th.ap_ofFn _ hx,
    UInt32.toNat_ofNat', hr ⟨x, hx⟩,
    Nat.mod_eq_of_lt ((trP n S base i k ⟨x, hx⟩).isLt.trans (n32 hQ))]
  rfl

theorem forall₂_levTables : List.Forall₂ (List.Forall₂ (CFSG.Sporadic.Th.Rep n))
    (levTables n S base 3) (trLists n S base 0 3) := by
  unfold levTables trLists
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun i hi => ?_
  rw [List.mem_range] at hi
  rw [Nat.zero_add, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun k hk => rep_levTable hQ hi (List.mem_range.1 hk)

omit hQ in
theorem countP_products3 (p : Equiv.Perm (Fin n) → Bool) :
    (products (trLists n S base 0 3)).countP p =
      ∑ k0 ∈ range (sz n S base 0), ∑ k1 ∈ range (sz n S base 1), ∑ k2 ∈ range (sz n S base 2),
        if p (trP n S base 0 k0 * (trP n S base 1 k1 * (trP n S base 2 k2 * 1))) then 1 else 0 := by
  rw [show (0 : Nat) = 0 + 0 from rfl, show (3 : Nat) = 2 + 1 from rfl, trLists_succ,
    countP_products_cons, List.map_map, sum_list_range]
  refine sum_congr rfl fun k0 _ => ?_
  rw [Function.comp_apply, show (0 + 0 + 1 : Nat) = 1 from rfl, show (2 : Nat) = 1 + 1 from rfl,
    trLists_succ, countP_products_cons, List.map_map, sum_list_range]
  refine sum_congr rfl fun k1 _ => ?_
  rw [Function.comp_apply, show (1 + 1 : Nat) = 2 from rfl, show (1 : Nat) = 0 + 1 from rfl,
    trLists_succ, countP_products_cons, List.map_map, sum_list_range]
  refine sum_congr rfl fun k2 _ => ?_
  simp [trLists, products, List.countP_cons]

theorem acts_T3 {k0 k1 k2 : Nat} (h0 : k0 < sz n S base 0) (h1 : k1 < sz n S base 1)
    (h2 : k2 < sz n S base 2) :
    Acts n (apL w (mask w) (T3 n (n * w) LR TR k0 k1 k2))
      (trP n S base 0 k0 * (trP n S base 1 k1 * (trP n S base 2 k2 * 1))) := by
  intro y
  rw [apL_cons, apL_cons, apL_cons, apL_nil, mul_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [pg_TR hQ (by norm_num) h2 y, pg_TR hQ (by norm_num) h1, pg_TR hQ (by norm_num) h0]

theorem T3_mem {k0 k1 k2 : Nat} (h0 : k0 < sz n S base 0) (h1 : k1 < sz n S base 1)
    (h2 : k2 < sz n S base 2) :
    trP n S base 0 k0 * (trP n S base 1 k1 * (trP n S base 2 k2 * 1)) ∈ Gen n S kO := by
  have m : ∀ {i k : Nat}, i < 3 → k < sz n S base i → trP n S base i k ∈ Gen n S kO :=
    fun hi hk => (tr_fix hQ hi hk).1
  exact Subgroup.mul_mem _ (m (by norm_num) h0) (Subgroup.mul_mem _ (m (by norm_num) h1)
    (Subgroup.mul_mem _ (m (by norm_num) h2) (Subgroup.one_mem _)))

theorem ptLen_sound {mx my r s : Nat} {R : List Nat} {CS : List Nat} {L : Nat} (hmx : 0 < mx)
    (hCS : rcnt (LR 0) ≤ CS.length * L)
    (hc : ∀ b < CS.length,
      cntJB n w (mask w) (n * w) BP 3 mx my r s LR TR R (b * L) L = CS.getD b 0)
    (hblk : L * (rcnt (LR 1) * rcnt (LR 2)) < 1048576) :
    (filterProducts n (ordTest n mx) (levTables n S base 3) (idT n) []).length =
      (CS.map (· % 1048576)).sum := by
  have e0 := rcnt_eq hQ (i := 0) (by norm_num)
  have e1 := rcnt_eq hQ (i := 1) (by norm_num)
  have e2 := rcnt_eq hQ (i := 2) (by norm_num)
  let A : Nat → Nat → Nat → Nat := fun k0 k1 k2 =>
    if ordF w (mask w) BP 3 (apL w (mask w) (T3 n (n * w) LR TR k0 k1 k2)) mx = true then 1 else 0
  let F : Nat → Nat := fun k0 => ∑ k1 ∈ range (rcnt (LR 1)), ∑ k2 ∈ range (rcnt (LR 2)), A k0 k1 k2
  have hW : ∀ b < CS.length, CS.getD b 0 % 1048576 =
      ∑ l ∈ range L, if b * L + l < rcnt (LR 0) then F (b * L + l) else 0 := by
    intro b hb
    rw [← hc b hb, cntJB_eq]
    simp only [cntJ_eq]
    have hd : ∀ T, dJ w (mask w) BP mx my r s R T =
        (if ordF w (mask w) BP 3 (apL w (mask w) T) mx = true then 1 else 0) +
          1048576 * (dJ w (mask w) BP mx my r s R T / 1048576) := fun T => by
      rw [← dJ_mod T]
      exact (Nat.mod_add_div _ _).symm
    let Q : Nat → Nat := fun k0 => ∑ k1 ∈ range (rcnt (LR 1)), ∑ k2 ∈ range (rcnt (LR 2)),
      dJ w (mask w) BP mx my r s R (T3 n (n * w) LR TR k0 k1 k2) / 1048576
    have hsplit : ∀ k0, ∑ k1 ∈ range (rcnt (LR 1)), ∑ k2 ∈ range (rcnt (LR 2)),
        dJ w (mask w) BP mx my r s R (T3 n (n * w) LR TR k0 k1 k2) = F k0 + 1048576 * Q k0 := by
      intro k0
      simp only [F, Q, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun k1 _ => sum_congr rfl fun k2 _ => hd _
    have hsum : (∑ l ∈ range L, if b * L + l < rcnt (LR 0) then
        ∑ k1 ∈ range (rcnt (LR 1)), ∑ k2 ∈ range (rcnt (LR 2)),
          dJ w (mask w) BP mx my r s R (T3 n (n * w) LR TR (b * L + l) k1 k2) else 0) =
        (∑ l ∈ range L, if b * L + l < rcnt (LR 0) then F (b * L + l) else 0) +
          1048576 * ∑ l ∈ range L, if b * L + l < rcnt (LR 0) then Q (b * L + l) else 0 := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun l _ => ?_
      split_ifs
      · exact hsplit _
      · rfl
    rw [hsum, Nat.add_mul_mod_self_left]
    apply Nat.mod_eq_of_lt
    refine lt_of_le_of_lt ?_ hblk
    calc (∑ l ∈ range L, if b * L + l < rcnt (LR 0) then F (b * L + l) else 0)
        ≤ ∑ _l ∈ range L, rcnt (LR 1) * rcnt (LR 2) := by
          refine sum_le_sum fun l _ => ?_
          split_ifs
          · calc F (b * L + l) ≤ ∑ _k1 ∈ range (rcnt (LR 1)), ∑ _k2 ∈ range (rcnt (LR 2)), 1 :=
                  sum_le_sum fun k1 _ => sum_le_sum fun k2 _ => by
                    simp only [A]
                    split <;> omega
              _ = rcnt (LR 1) * rcnt (LR 2) := by simp
          · exact Nat.zero_le _
      _ = L * (rcnt (LR 1) * rcnt (LR 2)) := by simp
  have hK : (CS.map (· % 1048576)).sum = ∑ k0 ∈ range (rcnt (LR 0)), F k0 := by
    rw [sum_map_getD, sum_congr rfl fun b hb => hW b (mem_range.1 hb), sum_blocks
      (fun k => if k < rcnt (LR 0) then F k else 0) L, sum_range_ind hCS]
  have hf := filterProducts_spec (n := n) (G := Equiv.Perm (Fin n)) (f := ordTest n mx)
    (P := fun g => orderOf g = mx) (fun T g hTg => ordTest_iff perm_faithful hTg hmx)
    (forall₂_levTables hQ) (gT := idT n) (g := 1) (CFSG.Sporadic.Th.Rep.idT (n32 hQ))
    (acc := []) (accG := []) List.Forall₂.nil
  rw [hf.length_eq, List.append_nil, List.length_reverse, ← List.countP_eq_length_filter,
    List.countP_map, hK, countP_products3]
  rw [← e0, ← e1, ← e2]
  refine sum_congr rfl fun k0 h0 => sum_congr rfl fun k1 h1 => sum_congr rfl fun k2 h2 => ?_
  rw [mem_range] at h0 h1 h2
  simp only [A, Function.comp_apply, one_mul]
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  have := ordF_iff hQ (e := mx) (acts_T3 hQ h0 h1 h2) (T3_mem hQ h0 h1 h2)
  by_cases ho : orderOf (trP n S base 0 k0 * (trP n S base 1 k1 * (trP n S base 2 k2 * 1))) = mx
  · rw [this.2 ho, decide_eq_true ho]
  · have h' : ordF w (mask w) BP 3 (apL w (mask w) (T3 n (n * w) LR TR k0 k1 k2)) mx = false :=
      Bool.eq_false_iff.2 fun h => ho (this.1 h)
    rw [h', decide_eq_false ho]

end Chain

end CFSG.KS.SporSch.PtCnt

end
