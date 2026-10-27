module

public import CFSG.Certificates.Kernel.Fi22LH.Bits
public import Mathlib.Logic.Function.Iterate
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.Acc
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KC.Enum

variable {Q : Nat → Nat} {al be lb m0 : Nat}

theorem setK_at (hs : ∀ s < 20, setSl Q al be s = true) {k : Nat} (hk : k < 14080) :
    setK Q masks al be k = true := by
  have h := hs (k / 704) (by omega)
  unfold setSl at h
  rw [strictB_eq] at h
  have := allN_iff.1 h (k % 704) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul (nat_lit 704) (k / 704)) (k % 704) = k := by
    change 704 * (k / 704) + k % 704 = k
    omega
  rw [e] at this
  exact this

theorem setK_spec (hs : ∀ s < 20, setSl Q al be s = true) {k : Nat} (hk : k < 14080) :
    sb (Q k) = bs (Q k) ∧ popK masks (sb (Q k)) = 351 ∧ fd (Q k) 7722 16383 < 14080 ∧
      fd (Q k) 7736 16383 < 14080 ∧
      bsF 351 (fun j => ent al (ent (Q k) j)) 9 0 = sb (Q (fd (Q k) 7722 16383)) ∧
      bsF 351 (fun j => ent be (ent (Q k) j)) 9 0 = sb (Q (fd (Q k) 7736 16383)) := by
  have h := setK_at hs hk
  unfold setK at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem sb_mem (hs : ∀ s < 20, setSl Q al be s = true) {k : Nat} (hk : k < 14080) (x : Nat) :
    (sb (Q k)).testBit x = true ↔ ∃ j < 351, ent (Q k) j = x := by
  rw [(setK_spec hs hk).1, testBit_bs]

theorem mem_lt (hs : ∀ s < 20, setSl Q al be s = true) {k j : Nat} (hk : k < 14080)
    (hj : j < 351) : ent (Q k) j < 3510 := by
  have h := (sb_mem hs hk (ent (Q k) j)).2 ⟨j, hj, rfl⟩
  rw [testBit_sb] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem sb_pop (hs : ∀ s < 20, setSl Q al be s = true) {k : Nat} (hk : k < 14080) :
    popK masks (sb (Q k)) = 351 := (setK_spec hs hk).2.1

theorem pa_lt (hs : ∀ s < 20, setSl Q al be s = true) {k : Nat} (hk : k < 14080) :
    fd (Q k) 7722 16383 < 14080 := (setK_spec hs hk).2.2.1

theorem pb_lt (hs : ∀ s < 20, setSl Q al be s = true) {k : Nat} (hk : k < 14080) :
    fd (Q k) 7736 16383 < 14080 := (setK_spec hs hk).2.2.2.1

theorem sb_pa (hs : ∀ s < 20, setSl Q al be s = true) {k : Nat} (hk : k < 14080) (x : Nat) :
    (sb (Q (fd (Q k) 7722 16383))).testBit x = true ↔ ∃ j < 351, ent al (ent (Q k) j) = x := by
  rw [← (setK_spec hs hk).2.2.2.2.1, testBit_bsF_zero (by decide)]

theorem sb_pb (hs : ∀ s < 20, setSl Q al be s = true) {k : Nat} (hk : k < 14080) (x : Nat) :
    (sb (Q (fd (Q k) 7736 16383))).testBit x = true ↔ ∃ j < 351, ent be (ent (Q k) j) = x := by
  rw [← (setK_spec hs hk).2.2.2.2.2, testBit_bsF_zero (by decide)]

theorem foldr_const_iter (g : Nat → Nat) : ∀ (n s : Nat),
    (List.range n).foldr (fun _ c => g c) s = g^[n] s
  | 0, s => rfl
  | n + 1, s => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil,
      foldr_const_iter g n (g s), Function.iterate_succ_apply]

theorem walkStep_spec {c : Nat} (h : walkStep Q c < 14080) :
    c < 14080 ∧ walkStep Q c = fd (Q c) 7766 16383 ∧ sb (Q c) < sb (Q (walkStep Q c)) := by
  unfold walkStep at h ⊢
  by_cases hc : c < 14080
  · rw [blt_true hc] at h ⊢
    change strictN (Q c) _ < 14080 at h
    change c < 14080 ∧ strictN (Q c) _ = _ ∧ _ < sb (Q (strictN (Q c) _))
    simp only [strictN_eq, nIf_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h ⊢
    split_ifs at h ⊢ with h2
    · exact ⟨hc, rfl, h2.2⟩
    · omega
  · rw [blt_false hc] at h
    change 16383 < 14080 at h
    omega

theorem walk_core (g S : Nat → Nat) {M m0 : Nat}
    (hspec : ∀ c, g c < M → c < M ∧ S c < S (g c)) : ∀ N, g^[N] m0 < M →
      (∀ i ≤ N, g^[i] m0 < M) ∧ ∀ i j, i < j → j ≤ N → S (g^[i] m0) < S (g^[j] m0) := by
  intro N
  induction N with
  | zero =>
    intro h
    exact ⟨fun i hi => by rw [Nat.le_zero.1 hi]; exact h, fun i j hij hj => by omega⟩
  | succ N ih =>
    intro h
    rw [Function.iterate_succ_apply'] at h
    obtain ⟨h1, h2⟩ := hspec _ h
    obtain ⟨ih1, ih2⟩ := ih h1
    refine ⟨fun i hi => ?_, fun i j hij hj => ?_⟩
    · rcases Nat.lt_or_ge i (N + 1) with hl | hl
      · exact ih1 i (by omega)
      · rw [show i = N + 1 by omega, Function.iterate_succ_apply']
        exact h
    · rcases Nat.lt_or_ge j (N + 1) with hl | hl
      · exact ih2 i j hij (by omega)
      · rw [show j = N + 1 by omega, Function.iterate_succ_apply']
        rcases Nat.lt_or_ge i N with hi | hi
        · exact Nat.lt_trans (ih2 i N hi (le_refl _)) h2
        · rw [show i = N by omega]
          exact h2

theorem walk_inj (hw : walkOK Q lb m0 = true) :
    ∀ i < 14080, ∀ j < 14080, sb (Q i) = sb (Q j) → i = j := by
  unfold walkOK at hw
  rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, foldN_eq, foldr_const_iter] at hw
  obtain ⟨hlt, hmono⟩ := walk_core (walkStep Q) (fun c => sb (Q c))
    (fun c h => ⟨(walkStep_spec h).1, (walkStep_spec h).2.2⟩) _ hw.1
  let w : Nat → Nat := fun i => (walkStep Q)^[i] m0
  let f : Fin 14080 → Fin 14080 := fun i => ⟨w i, hlt i (by change i.val ≤ 14079; omega)⟩
  have hf : Function.Injective f := by
    intro a b e
    have e' : w a = w b := congrArg Fin.val e
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hmono a b h (by change b.val ≤ 14079; omega)
      change sb (Q (w a)) < sb (Q (w b)) at this
      rw [e'] at this
      omega
    · have := hmono b a h (by change a.val ≤ 14079; omega)
      change sb (Q (w b)) < sb (Q (w a)) at this
      rw [e'] at this
      omega
  have hsurj := Finite.surjective_of_injective hf
  intro i hi j hj e
  obtain ⟨a, ha⟩ := hsurj ⟨i, hi⟩
  obtain ⟨b, hb⟩ := hsurj ⟨j, hj⟩
  have ea : w a = i := congrArg Fin.val ha
  have eb : w b = j := congrArg Fin.val hb
  rw [← ea, ← eb] at e ⊢
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (fun h : (a : Nat) = b => hne (by rw [h])) with h | h
  · have := hmono a b h (by change b.val ≤ 14079; omega)
    change sb (Q (w a)) < sb (Q (w b)) at this
    omega
  · have := hmono b a h (by change a.val ≤ 14079; omega)
    change sb (Q (w b)) < sb (Q (w a)) at this
    omega

theorem sb_inj (hw : walkOK Q lb m0 = true) {i j : Nat} (hi : i < 14080) (hj : j < 14080)
    (e : sb (Q i) = sb (Q j)) : i = j := walk_inj hw i hi j hj e

theorem walk_rest (hw : walkOK Q lb m0 = true) :
    sb (Q 0) = bs lb ∧ incK lb = true ∧ ent lb 0 = 0 := by
  unfold walkOK at hw
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hw
  exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2⟩

theorem sb_zero (hw : walkOK Q lb m0 = true) : sb (Q 0) = bs lb := (walk_rest hw).1

theorem incK_spec {q : Nat} (h : incK q = true) :
    (∀ i j, i < j → j < 351 → ent q i < ent q j) ∧ ∀ j < 351, ent q j < 3510 := by
  unfold incK at h
  rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hs : ∀ j < 350, ent q j < ent q (j + 1) := fun j hj => by
    have := allN_iff.1 h1 j hj
    rw [Nat.blt_eq] at this
    exact this
  have hinc : ∀ i j, i < j → j < 351 → ent q i < ent q j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_or_ge i j with h | h
      · exact Nat.lt_trans (ih h (by omega)) (hs j (by omega))
      · have : i = j := by omega
        subst this
        exact hs i (by omega)
  refine ⟨hinc, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j 350 with h | h
  · exact Nat.lt_trans (hinc j 350 h (by omega)) h2
  · have : j = 350 := by omega
    subst this
    exact h2

theorem orbDec_sets_eq (Q : Nat → Nat) :
    (orbDec Q).sets = Array.ofFn (n := 14080) fun k => bitsOfNat (sb (Q k.val)) := by
  simp only [orbDec]

theorem orbDec_size (Q : Nat → Nat) : (orbDec Q).sets.size = 14080 := by
  rw [orbDec_sets_eq, Array.size_ofFn]

theorem orbDec_sets (Q : Nat → Nat) {k : Nat} (hk : k < 14080) :
    (orbDec Q).sets[k]! = bitsOfNat (sb (Q k)) := by
  rw [orbDec_sets_eq, getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem foldl_insert_of (K : Nat → Bits) {n : Nat} (hinj : ∀ i < n, ∀ j < n, K i = K j → i = j)
    {k : Nat} (hk : k < n) :
    ((List.range n).foldl (fun t k => t.insert (K k) k) (∅ : Std.HashMap Bits Nat))[K k]? =
      some k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getElem?_insert]
    rcases Nat.lt_or_ge k n with h | h
    · have hne : (K n == K k) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        have := hinj n (by omega) k (by omega) e
        omega
      rw [hne]
      exact ih (fun i hi j hj e => hinj i (by omega) j (by omega) e) h
    · have : k = n := by omega
      subst this
      rw [beq_self_eq_true]
      rfl

theorem foldl_insert_none (K : Nat → Bits) {n : Nat} {B : Bits} (hB : ∀ k < n, K k ≠ B) :
    ((List.range n).foldl (fun t k => t.insert (K k) k) (∅ : Std.HashMap Bits Nat))[B]? =
      none := by
  induction n with
  | zero => exact Std.HashMap.getElem?_empty
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getElem?_insert]
    have hne : (K n == B) = false := by
      rw [beq_eq_false_iff_ne]
      exact hB n (by omega)
    rw [hne]
    exact ih fun k hk => hB k (by omega)

theorem orbDec_tbl (Q : Nat → Nat) : (orbDec Q).tbl =
    (List.range 14080).foldl (fun t k => t.insert (bitsOfNat (sb (Q k))) k) ∅ := by
  simp only [orbDec]

theorem sb_lt_3520 (q : Nat) : sb q < 2 ^ 3520 :=
  Nat.lt_of_lt_of_le (sb_lt q) (Nat.pow_le_pow_right (by decide) (by decide))

theorem find_orbDec_of (hinj : ∀ i < 14080, ∀ j < 14080, sb (Q i) = sb (Q j) → i = j) {k : Nat}
    (hk : k < 14080) {B : Bits} (hB : B = bitsOfNat (sb (Q k))) : (orbDec Q).find B = k := by
  unfold LHOrb.find
  rw [Std.HashMap.get?_eq_getElem?, orbDec_tbl, hB,
    foldl_insert_of (fun k => bitsOfNat (sb (Q k))) (fun i hi j hj e => hinj i hi j hj
      (bitsOfNat_inj (sb_lt_3520 _) (sb_lt_3520 _) e)) hk]
  rfl

theorem find_orbDec_none (hinj : ∀ i < 14080, ∀ j < 14080, sb (Q i) = sb (Q j) → i = j)
    {B : Bits} (hB : ∀ k < 14080, B ≠ bitsOfNat (sb (Q k))) : (orbDec Q).find B = 14080 := by
  unfold LHOrb.find
  rw [Std.HashMap.get?_eq_getElem?, orbDec_tbl,
    foldl_insert_none (fun k => bitsOfNat (sb (Q k))) fun k hk e => hB k hk e.symm, orbDec_size]
  rfl

variable {D : LHData}

set_option maxRecDepth 8000 in
theorem lhData0_size : (lhData ())[0]!.size = 351 := rfl

set_option maxRecDepth 8000 in
theorem lhData1_size : (lhData ())[1]!.size = 351 := rfl

theorem mem_lhData_iff {S : Array Nat} (hS : S.size = 351) {lb : Nat}
    (hb : ∀ j < 351, ent lb j = S[j]!) (x : Nat) :
    (bs lb).testBit x = true ↔ x ∈ S := by
  rw [testBit_bs, Array.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, by rw [hb j hj, getElem!_pos S j (by omega)]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, by rw [hb j (by omega), getElem!_pos S j hj]⟩

theorem lb0_mem (h : LHChecks D) (x : Nat) :
    (bs D.lb0).testBit x = true ↔ x ∈ (lhData ())[0]! :=
  mem_lhData_iff lhData0_size h.lb0 x

theorem lb1_mem (h : LHChecks D) (x : Nat) :
    (bs D.lb1).testBit x = true ↔ x ∈ (lhData ())[1]! :=
  mem_lhData_iff lhData1_size h.lb1 x

theorem bitsOf_root {S : Array Nat} (hS : S.size = 351) {lb : Nat}
    (hb : ∀ j < 351, ent lb j = S[j]!) (hinc : incK lb = true) {q : Nat} (hq : sb q = bs lb) :
    bitsOf S = bitsOfNat (sb q) := by
  have hlt : ∀ a ∈ S, a < 3520 := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 ha
    have := (incK_spec hinc).2 j (by omega)
    rw [hb j (by omega), getElem!_pos S j hj] at this
    omega
  refine BitsIs.eq_bitsOfNat (bitsIs_bitsOf hlt) fun y _ => ?_
  rw [hq, mem_lhData_iff hS hb]

theorem B0_eq (h : LHChecks D) : bitsOf (lhData ())[0]! = bitsOfNat (sb (D.QA 0)) :=
  bitsOf_root lhData0_size h.lb0 (walk_rest h.walkA).2.1 (sb_zero h.walkA)

theorem B1_eq (h : LHChecks D) : bitsOf (lhData ())[1]! = bitsOfNat (sb (D.QB 0)) :=
  bitsOf_root lhData1_size h.lb1 (walk_rest h.walkB).2.1 (sb_zero h.walkB)

end CFSG.KS.Fi22LH
