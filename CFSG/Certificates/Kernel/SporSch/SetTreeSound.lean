
module

public import Certificates.Data.Kernel.SporSch.SetTree
public import CFSG.Certificates.Kernel.SporSch.KeySearchOrbit
public import CFSG.Certificates.Kernel.Co2InvS.Enum
public import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.SporSch.SetTree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.SporSch.KeySearch
open CFSG.Certificates.Native

@[expose] noncomputable def ptsOf (w s x : Nat) : List Nat := (List.range s).map (pg w (mask w) x)

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem testBit_foldr (g : Nat → Nat) (b : Nat) :
    ∀ (l : List Nat) (a : Nat), (l.foldr (fun q acc => Nat.lor acc
      (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (g q)))) a).testBit (64 + b) =
        (a.testBit (64 + b) || decide (b ∈ l.map g))
  | [], a => by simp
  | q :: l, a => by
    rw [List.foldr_cons]
    have e : ∀ x y : Nat, Nat.lor x y = x ||| y := fun _ _ => rfl
    have e2 : Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (g q)) = 2 ^ (64 + g q) := by
      change 1 <<< (64 + g q) = _
      rw [Nat.one_shiftLeft]
    rw [e, e2, Nat.testBit_or, testBit_foldr g b l a, Nat.testBit_two_pow]
    by_cases h : b = g q
    · subst h
      simp
    · have : ¬ 64 + g q = 64 + b := by omega
      simp [this, h, Ne.symm h]

theorem tag_bit {t : Nat} (ht : t < 2 ^ 64) (b : Nat) : t.testBit (64 + b) = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem shr64 (n b : Nat) : (Nat.shiftRight n (nat_lit 64)).testBit b = n.testBit (64 + b) := by
  change (n >>> 64).testBit b = _
  rw [Nat.testBit_shiftRight]

theorem maskK_bit (w s : Nat) {t : Nat} (ht : t < 2 ^ 64) (x b : Nat) :
    (maskK w s t x).testBit b = decide (b ∈ ptsOf w s x) := by
  unfold maskK
  rw [strictN_eq', strictN_eq', shr64, CFSG.KC.Pack.foldN_eq, testBit_foldr, tag_bit ht,
    Bool.false_or]
  rfl

theorem imgMK_bit (w s : Nat) {t : Nat} (ht : t < 2 ^ 64) (G x b : Nat) :
    (imgMK w s t G x).testBit b = decide (b ∈ (ptsOf w s x).map (pg w (mask w) G)) := by
  unfold imgMK
  rw [strictN_eq', strictN_eq', strictN_eq', shr64, CFSG.KC.Pack.foldN_eq,
    testBit_foldr (fun q => pg w (mask w) G (pg w (mask w) x q)), tag_bit ht, Bool.false_or]
  unfold ptsOf
  rw [List.map_map]
  rfl

theorem eltK_good {n w s x : Nat} (h : eltK n w s x = true) : Good n (ptsOf w s x) := by
  have hq : ∀ q < s, pg w (mask w) x q < n ∧ (0 < q → pg w (mask w) x (q - 1) < pg w (mask w) x q) := by
    intro q hq
    have h1 := allN_spec h q hq
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h1
    refine ⟨by rwa [Nat.blt_eq] at a, fun h0 => ?_⟩
    have hb : Nat.beq q 0 = false := Bool.eq_false_iff.2 fun e => by
      have := Nat.eq_of_beq_eq_true e
      omega
    rw [hb] at b
    change Nat.blt _ _ = true at b
    rwa [Nat.blt_eq] at b
  have mono : ∀ a b, a < b → b < s → pg w (mask w) x a < pg w (mask w) x b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hs := (hq (b + 1) hb).2 (by omega)
      rw [Nat.add_sub_cancel] at hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
      · exact lt_trans (ih h' (by omega)) hs
      · rw [h']
        exact hs
  refine ⟨?_, fun p hp => ?_⟩
  · unfold ptsOf
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range).imp_of_mem fun {a b} ha hb hab =>
      mono a b hab (List.mem_range.1 hb)
  · obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hp
    exact (hq q (List.mem_range.1 hq')).1

theorem ptsFrom_spec {w x : Nat} :
    ∀ (l : List Nat) (q : Nat), ptsFrom w x l q = true →
      ∀ t (ht : t < l.length), pg w (mask w) x (q + t) = l[t]
  | [], _, _, t, ht => absurd ht (by simp)
  | p :: l, q, h, t, ht => by
    have h' : Bool.rec (motive := fun _ => Bool) false (ptsFrom w x l (Nat.succ q))
        (Nat.beq (pg w (mask w) x q) p) = true := h
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h'
    cases t with
    | zero => exact Nat.eq_of_beq_eq_true a
    | succ t =>
      have := ptsFrom_spec l (Nat.succ q) b t (by simpa using ht)
      rw [show q + (t + 1) = Nat.succ q + t by omega, this]
      rfl

theorem lenN_eq (l : List Nat) : CFSG.KS.Mathieu.lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Nat.succ (CFSG.KS.Mathieu.lenN l) = _
    rw [ih]
    rfl

theorem startK_spec {w s x : Nat} {start : List Nat} (h : startK w s x start = true) :
    ptsOf w s x = start := by
  unfold startK at h
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h
  obtain ⟨b, -⟩ := (bAnd_iff _ _).1 b
  have hl : start.length = s := by rw [← lenN_eq]; exact Nat.eq_of_beq_eq_true a
  have hp := ptsFrom_spec start 0 b
  refine List.ext_getElem (by simp [ptsOf, hl]) fun t h1 h2 => ?_
  simp only [ptsOf, List.getElem_map, List.getElem_range]
  rw [← hp t h2, Nat.zero_add]

theorem setTree_bound {n w s kg c : Nat} {G X SO : Nat → Nat} {gens : Array (Array Nat)}
    {start : List Nat} (hgs : gens.size = kg) (hg : ∀ k < kg, gens[k]! = unpack n w (G k))
    (hperm : ∀ k < kg, PermA n gens[k]!) (hc : 0 < c) (hc' : c < 2 ^ 20)
    (helt : ∀ i < c, eltK n w s (X i) = true) (hst : startK w s (X 0) start = true)
    (htree : ∀ i < c, treeK w s G X kg i = true)
    (hsort : ∀ i < c, sortMK w s X SO c i = true) :
    ∀ F : Finset (List Nat), start ∈ F →
      (∀ t ∈ F, ∀ k < gens.size, imgSorted gens[k]! t ∈ F) → c ≤ F.card := by
  intro F h0 hF
  have hgood : ∀ i < c, Good n (ptsOf w s (X i)) := fun i hi => eltK_good (helt i hi)
  have hmem : ∀ i < c, ptsOf w s (X i) ∈ F := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [startK_spec hst]
        exact h0
      · have ht := htree i hi
        unfold treeK at ht
        have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun e => by
          have := Nat.eq_of_beq_eq_true e
          omega
        rw [hb] at ht
        change strictB (X i) _ = true at ht
        rw [strictB_eq'] at ht
        obtain ⟨a, b⟩ := (bAnd_iff _ _).1 ht
        obtain ⟨b, e⟩ := (bAnd_iff _ _).1 b
        have hp : parX w s (X i) < i := by rwa [Nat.blt_eq] at a
        have hl : labX w s (X i) < kg := by rwa [Nat.blt_eq] at b
        have he := Nat.eq_of_beq_eq_true e
        set p := parX w s (X i)
        set k := labX w s (X i)
        have hpF := ih p hp (by omega)
        have hgp := hgood p (by omega)
        have hpts : ptsOf w s (X i) = imgSorted gens[k]! (ptsOf w s (X p)) := by
          refine eq_of_mem_iff (hgood i hi) (imgSorted_good (hperm k hl) hgp) fun q => ?_
          have hb1 := maskK_bit w s (t := i) (by omega) (X i) q
          rw [he, imgMK_bit w s (t := Nat.add i 1048576) (by rw [Nat.add_eq]; omega)] at hb1
          have e1 : q ∈ ptsOf w s (X i) ↔ q ∈ (ptsOf w s (X p)).map (pg w (mask w) (G k)) :=
            (decide_eq_decide.1 hb1).symm
          rw [e1]
          have hmap : (ptsOf w s (X p)).map (pg w (mask w) (G k)) =
              (ptsOf w s (X p)).map fun r => (gens[k]!)[r]! := by
            refine List.map_congr_left fun r hr => ?_
            rw [hg k hl, CFSG.KC.Misc.PairCount.unpack_get (hgp.2 r hr)]
          rw [hmap, imgSorted, (List.mergeSort_perm _ _).mem_iff]
        rw [hpts]
        exact hF _ hpF k (by rw [hgs]; exact hl)
  have hs : ∀ i < c, SO i < c := fun i hi => by
    have h := hsort i hi
    unfold sortMK at h
    rw [strictB_eq'] at h
    obtain ⟨a, -⟩ := (bAnd_iff _ _).1 h
    rwa [Nat.blt_eq] at a
  have hlt : ∀ i, i + 1 < c →
      maskK w s (SO i) (X (SO i)) < maskK w s (SO (i + 1)) (X (SO (i + 1))) := by
    intro i hi
    have h := hsort i (by omega)
    unfold sortMK at h
    rw [strictB_eq'] at h
    obtain ⟨-, b⟩ := (bAnd_iff _ _).1 h
    have hb : Nat.blt (Nat.succ i) c = true := by rwa [Nat.blt_eq]
    rw [hb] at b
    change strictB _ _ = true at b
    rw [strictB_eq'] at b
    change Nat.blt _ _ = true at b
    rwa [Nat.blt_eq] at b
  have hinj := CFSG.KC.Co2InvS.sorted_inj (f := fun i => maskK w s i (X i)) hs hlt
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range c) (t := F)
    (fun i => ptsOf w s (X i)) (fun i hi => hmem i (Finset.mem_range.1 hi))
    (fun a ha b hb e => hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb)
      (Nat.eq_of_testBit_eq fun q => by
        rw [maskK_bit w s (by have := Finset.mem_range.1 ha; omega),
          maskK_bit w s (by have := Finset.mem_range.1 hb; omega)]
        exact congrArg (fun l => decide (q ∈ l)) e))
  rwa [Finset.card_range] at hcard

end CFSG.KS.SporSch.SetTree

end
