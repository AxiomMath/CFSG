module

public import Certificates.Data.Kernel.M24G.TrioSexts
public import CFSG.Certificates.Kernel.M24G.PairsCount
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def code6 (f : Nat → Bool) : Nat :=
  (if f 0 then 1 else 0) + (if f 1 then 2 else 0) + (if f 2 then 4 else 0) +
    (if f 3 then 8 else 0) + (if f 4 then 16 else 0) + (if f 5 then 32 else 0)

@[expose] def pairCode (a b : Nat) : Nat := code6 fun i => i == a || i == b

@[expose] def codes15 : List Nat :=
  (List.range 6).flatMap fun a => ((List.range 6).filter (a < ·)).map (pairCode a)

@[expose] def match15 : List (Nat × Nat × Nat) :=
  codes15.flatMap fun x => codes15.flatMap fun y =>
    (codes15.filter fun z => x < y && y < z && x &&& y == 0 && x &&& z == 0 && y &&& z == 0).map
      fun z => (x, y, z)

theorem match15_length : match15.length = 15 := by decide

theorem code6_congr {f g : Nat → Bool} (h : ∀ i < 6, f i = g i) : code6 f = code6 g := by
  unfold code6
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega)]

theorem pairCode_mem : ∀ a < 6, ∀ b < 6, a ≠ b → pairCode a b ∈ codes15 := by decide

@[expose] def all6 (f : Nat → Bool) : Bool := (List.range 6).all f

theorem all6_spec {f : Nat → Bool} (h : all6 f = true) {a : Nat} (ha : a < 6) : f a = true :=
  List.all_eq_true.1 h a (List.mem_range.2 ha)

theorem pairCode_inj_all : (all6 fun a => all6 fun b => all6 fun c => all6 fun d =>
    a == b || c == d || pairCode a b != pairCode c d || (a == c && b == d) ||
      (a == d && b == c)) = true := by decide

theorem pairCode_disj_all : (all6 fun a => all6 fun b => all6 fun c => all6 fun d =>
    a == c || a == d || b == c || b == d || pairCode a b &&& pairCode c d == 0) = true := by
  decide

theorem pairCode_inj {a b c d : Nat} (ha : a < 6) (hb : b < 6) (hc : c < 6) (hd : d < 6)
    (hab : a ≠ b) (hcd : c ≠ d) (h : pairCode a b = pairCode c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have := all6_spec (all6_spec (all6_spec (all6_spec pairCode_inj_all ha) hb) hc) hd
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  tauto

theorem pairCode_disj {a b c d : Nat} (ha : a < 6) (hb : b < 6) (hc : c < 6) (hd : d < 6)
    (e1 : a ≠ c) (e2 : a ≠ d) (e3 : b ≠ c) (e4 : b ≠ d) : pairCode a b &&& pairCode c d = 0 := by
  have := all6_spec (all6_spec (all6_spec (all6_spec pairCode_disj_all ha) hb) hc) hd
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  tauto

theorem codes15_ne_zero : ∀ x ∈ codes15, x ≠ 0 := by decide

theorem sort3_sorted (a b c : Nat) :
    (Native.sort3 a b c).1 ≤ (Native.sort3 a b c).2.1 ∧
      (Native.sort3 a b c).2.1 ≤ (Native.sort3 a b c).2.2 := by
  unfold Native.sort3
  split_ifs <;> simp <;> omega

theorem mem_octsT_sort3 {a b c x : Nat} (h : x = a ∨ x = b ∨ x = c) :
    x ∈ Native.octsT (Native.sort3 a b c) := by
  have hp := sort3_mem a b c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with e | e | e | e | e | e <;> rw [e] <;>
    simp only [Native.octsT, List.mem_cons, List.not_mem_nil, or_false] <;> omega

theorem and_ne_of_ne {x y : Nat} (hx : x ≠ 0) (h : x &&& y = 0) : x ≠ y := by
  rintro rfl
  rw [Nat.and_self] at h
  exact hx h

theorem sort3_mem_match15 {x y z : Nat} (hx : x ∈ codes15) (hy : y ∈ codes15) (hz : z ∈ codes15)
    (hxy : x &&& y = 0) (hxz : x &&& z = 0) (hyz : y &&& z = 0) :
    Native.sort3 x y z ∈ match15 := by
  have nxy := and_ne_of_ne (codes15_ne_zero x hx) hxy
  have nxz := and_ne_of_ne (codes15_ne_zero x hx) hxz
  have nyz := and_ne_of_ne (codes15_ne_zero y hy) hyz
  have hyx : y &&& x = 0 := by rw [Nat.and_comm]; exact hxy
  have hzx : z &&& x = 0 := by rw [Nat.and_comm]; exact hxz
  have hzy : z &&& y = 0 := by rw [Nat.and_comm]; exact hyz
  have hs := sort3_sorted x y z
  have hp := sort3_mem x y z
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with e | e | e | e | e | e <;> rw [e] at hs ⊢ <;>
    simp only [match15, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq, Prod.mk.injEq] at hs ⊢
  · exact ⟨x, hx, y, hy, z, ⟨hz, ⟨⟨⟨⟨by omega, by omega⟩, hxy⟩, hxz⟩, hyz⟩⟩, rfl, rfl, rfl⟩
  · exact ⟨x, hx, z, hz, y, ⟨hy, ⟨⟨⟨⟨by omega, by omega⟩, hxz⟩, hxy⟩, hzy⟩⟩, rfl, rfl, rfl⟩
  · exact ⟨z, hz, x, hx, y, ⟨hy, ⟨⟨⟨⟨by omega, by omega⟩, hzx⟩, hzy⟩, hxy⟩⟩, rfl, rfl, rfl⟩
  · exact ⟨y, hy, x, hx, z, ⟨hz, ⟨⟨⟨⟨by omega, by omega⟩, hyx⟩, hyz⟩, hxz⟩⟩, rfl, rfl, rfl⟩
  · exact ⟨y, hy, z, hz, x, ⟨hx, ⟨⟨⟨⟨by omega, by omega⟩, hyz⟩, hyx⟩, hzx⟩⟩, rfl, rfl, rfl⟩
  · exact ⟨z, hz, y, hy, x, ⟨hx, ⟨⟨⟨⟨by omega, by omega⟩, hzy⟩, hzx⟩, hyx⟩⟩, rfl, rfl, rfl⟩

theorem getD_of_lt {α : Type} (L : List α) (i : Nat) (d : α) (h : i < L.length) :
    L.getD i d = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem sextItem_tets {s : List Nat} (h : sextItem s = true) :
    s.length = 6 ∧ s.Pairwise (· < ·) ∧ (∀ i < 6, s.getD i 0 ≠ 0) ∧
      ∀ i < 6, ∀ j < 6, i ≠ j → s.getD i 0 &&& s.getD j 0 = 0 := by
  unfold sextItem at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hl, -⟩, hpw⟩, hpop⟩, -⟩, hdis⟩ := h
  have hnd : s.Nodup := hpw.imp (fun h => Nat.ne_of_lt h)
  refine ⟨hl, hpw, fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · have hi' : i < s.length := by omega
    rw [getD_of_lt s i 0 hi']
    intro h0
    have := (hpop _ (List.getElem_mem hi')).1
    rw [h0] at this
    exact absurd this (by decide)
  · have hi' : i < s.length := by omega
    have hj' : j < s.length := by omega
    rw [getD_of_lt s i 0 hi', getD_of_lt s j 0 hj']
    rcases hdis _ (List.getElem_mem hi') _ (List.getElem_mem hj') with e | e
    · exact absurd ((hnd.getElem_inj_iff).1 e) hij
    · exact e

theorem mem_octsS {s : List Nat} (hl : s.length = 6) {o : Nat} (h : o ∈ Native.octsS s) :
    ∃ a < 6, ∃ b < 6, a ≠ b ∧ o = s.getD a 0 ||| s.getD b 0 := by
  unfold Native.octsS at h
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨B, hB, B', ⟨hB', hlt⟩, rfl⟩ := h
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hB
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hB'
  refine ⟨a, by omega, b, by omega, fun e => ?_, ?_⟩
  · subst e
    exact absurd hlt (Nat.lt_irrefl _)
  · rw [getD_of_lt s a 0 ha, getD_of_lt s b 0 hb]

@[expose] def meetCode (s : List Nat) (o : Nat) : Nat := code6 fun i => s.getD i 0 &&& o != 0

section Sext

variable {s : List Nat} (hs : sextItem s = true)

include hs in
theorem meetCode_pair {a b : Nat} (ha : a < 6) (hb : b < 6) (hab : a ≠ b) :
    meetCode s (s.getD a 0 ||| s.getD b 0) = pairCode a b := by
  obtain ⟨-, -, hnz, hdis⟩ := sextItem_tets hs
  refine code6_congr fun i hi => ?_
  rw [Nat.and_or_distrib_left]
  by_cases hia : i = a
  · subst hia
    rw [Nat.and_self]
    have := hnz i hi
    simp only [bne_iff_ne, ne_eq, Nat.or_eq_zero_iff, beq_self_eq_true, Bool.true_or,
      iff_true]
    exact fun h => this h.1
  · by_cases hib : i = b
    · subst hib
      rw [Nat.and_self]
      have := hnz i hi
      simp only [bne_iff_ne, ne_eq, Nat.or_eq_zero_iff, beq_self_eq_true, Bool.or_true,
        iff_true]
      exact fun h => this h.2
    · rw [hdis i hi a ha hia, hdis i hi b hb hib]
      simp [hia, hib]

include hs in
theorem disj_pair {a b c d : Nat} (ha : a < 6) (hb : b < 6) (hc : c < 6) (hd : d < 6)
    (h : (s.getD a 0 ||| s.getD b 0) &&& (s.getD c 0 ||| s.getD d 0) = 0) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  obtain ⟨-, -, hnz, -⟩ := sextItem_tets hs
  have absorb : ∀ x y w : Nat, (x ||| y) &&& (x ||| w) = 0 → x = 0 := by
    intro x y w h
    rw [Nat.and_or_distrib_left, Nat.or_eq_zero_iff] at h
    have h1 := h.1
    rw [Nat.and_comm, Nat.and_or_distrib_left, Nat.and_self, Nat.or_eq_zero_iff] at h1
    exact h1.1
  have key : ∀ x y z w : Nat, x ≠ 0 → (x ||| y) &&& (z ||| w) = 0 → x ≠ z ∧ x ≠ w := by
    intro x y z w hx h
    refine ⟨fun e => ?_, fun e => ?_⟩ <;> subst e
    · exact hx (absorb x y w h)
    · rw [Nat.or_comm z x] at h
      exact hx (absorb x y z h)
  have h' : (s.getD b 0 ||| s.getD a 0) &&& (s.getD c 0 ||| s.getD d 0) = 0 := by
    rw [Nat.or_comm]; exact h
  have k1 := key _ _ _ _ (hnz a ha) h
  have k2 := key _ _ _ _ (hnz b hb) h'
  refine ⟨fun e => k1.1 (e ▸ rfl), fun e => k1.2 (e ▸ rfl), fun e => k2.1 (e ▸ rfl),
    fun e => k2.2 (e ▸ rfl)⟩

@[expose] def trioCode (s : List Nat) (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  Native.sort3 (meetCode s t.1) (meetCode s t.2.1) (meetCode s t.2.2)

include hs in
theorem meetCode_mem {o : Nat} (ho : o ∈ Native.octsS s) : meetCode s o ∈ codes15 := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_octsS (sextItem_tets hs).1 ho
  rw [meetCode_pair hs ha hb hab]
  exact pairCode_mem a ha b hb hab

include hs in
theorem meetCode_disj {o o' : Nat} (ho : o ∈ Native.octsS s) (ho' : o' ∈ Native.octsS s)
    (h : o &&& o' = 0) : meetCode s o &&& meetCode s o' = 0 := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_octsS (sextItem_tets hs).1 ho
  obtain ⟨c, hc, d, hd, hcd, rfl⟩ := mem_octsS (sextItem_tets hs).1 ho'
  obtain ⟨e1, e2, e3, e4⟩ := disj_pair hs ha hb hc hd h
  rw [meetCode_pair hs ha hb hab, meetCode_pair hs hc hd hcd]
  exact pairCode_disj ha hb hc hd e1 e2 e3 e4

include hs in
theorem meetCode_inj {o o' : Nat} (ho : o ∈ Native.octsS s) (ho' : o' ∈ Native.octsS s)
    (h : meetCode s o = meetCode s o') : o = o' := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_octsS (sextItem_tets hs).1 ho
  obtain ⟨c, hc, d, hd, hcd, rfl⟩ := mem_octsS (sextItem_tets hs).1 ho'
  rw [meetCode_pair hs ha hb hab, meetCode_pair hs hc hd hcd] at h
  rcases pairCode_inj ha hb hc hd hab hcd h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Nat.or_comm _ _

theorem trioIn_octs {t : Nat × Nat × Nat} (h : Native.trioIn t s = true) :
    ∀ x ∈ Native.octsT t, x ∈ Native.octsS s := by
  intro x hx
  unfold Native.trioIn at h
  exact List.elem_iff.1 (List.all_eq_true.1 h x hx)

include hs in
theorem trioCode_mem {t : Nat × Nat × Nat} (ht : trioItem t = true)
    (hin : Native.trioIn t s = true) : trioCode s t ∈ match15 := by
  obtain ⟨-, -, d1, d2, d3, -⟩ := trioItem_facts ht
  have ho := trioIn_octs hin
  have o1 := ho t.1 (by simp [Native.octsT])
  have o2 := ho t.2.1 (by simp [Native.octsT])
  have o3 := ho t.2.2 (by simp [Native.octsT])
  exact sort3_mem_match15 (meetCode_mem hs o1) (meetCode_mem hs o2) (meetCode_mem hs o3)
    (meetCode_disj hs o1 o2 d1) (meetCode_disj hs o1 o3 d2) (meetCode_disj hs o2 o3 d3)

theorem eq_of_octsT_sub {t t' : Nat × Nat × Nat} (h1 : t.1 < t.2.1) (h2 : t.2.1 < t.2.2)
    (h1' : t'.1 < t'.2.1) (h2' : t'.2.1 < t'.2.2)
    (hsub : ∀ x ∈ Native.octsT t, x ∈ Native.octsT t') : t = t' := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨a', b', c'⟩ := t'
  simp only [Native.octsT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hsub h1 h2 h1' h2'
  obtain ⟨ha, hb, hc⟩ := hsub
  have : a = a' ∧ b = b' ∧ c = c' := by
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      rcases hc with hc | hc | hc <;> omega
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

include hs in
theorem trioCode_inj {t t' : Nat × Nat × Nat} (ht : trioItem t = true) (ht' : trioItem t' = true)
    (hin : Native.trioIn t s = true) (hin' : Native.trioIn t' s = true)
    (h : trioCode s t = trioCode s t') : t = t' := by
  obtain ⟨a1, a2, -⟩ := trioItem_facts ht
  obtain ⟨b1, b2, -⟩ := trioItem_facts ht'
  refine eq_of_octsT_sub a1 a2 b1 b2 fun x hx => ?_
  have hx' : meetCode s x ∈ Native.octsT (trioCode s t') := by
    rw [← h]
    unfold trioCode
    apply mem_octsT_sort3
    simp only [Native.octsT, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp
  unfold trioCode at hx'
  have hy := mem_sort3 hx'
  have hox := trioIn_octs hin x hx
  have ho' := trioIn_octs hin'
  rcases hy with e | e | e
  · rw [meetCode_inj hs hox (ho' _ (by simp [Native.octsT])) e]; simp [Native.octsT]
  · rw [meetCode_inj hs hox (ho' _ (by simp [Native.octsT])) e]; simp [Native.octsT]
  · rw [meetCode_inj hs hox (ho' _ (by simp [Native.octsT])) e]; simp [Native.octsT]

end Sext

section Count

variable {TL : List (Nat × Nat × Nat)} {SL : List (List Nat)} {TS : List (List Nat)}
  (hTl : TL.length = 3795) (hSl : SL.length = 1771) (hTi : TL.all trioItem = true)
  (hSi : SL.all sextItem = true)
  (hinj : ∀ i j (hi : i < TL.length) (hj : j < TL.length), TL[i] = TL[j] → i = j)
  (hR : tsRowsOK TL SL TS = true)

@[expose] def incid (TL : List (Nat × Nat × Nat)) (SL : List (List Nat)) : Finset (Nat × Nat) :=
  (Finset.range 3795 ×ˢ Finset.range 1771).filter
    fun x => Native.trioIn (TL.getD x.1 default) (SL.getD x.2 default) = true

@[expose] def recInc (TS : List (List Nat)) : Finset (Nat × Nat) :=
  (Finset.range 3795 ×ˢ Finset.range 1771).filter fun x => x.2 ∈ TS.getD x.1 []

include hR in
theorem row_facts {p : Nat} (hp : p < 3795) :
    TS.length = 3795 ∧ (TS.getD p []).length = 7 ∧ (TS.getD p []).Pairwise (· < ·) ∧
      ∀ q ∈ TS.getD p [], q < 1771 ∧ Native.trioIn (TL.getD p default) (SL.getD q default) =
        true := by
  unfold tsRowsOK at hR
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hR
  obtain ⟨⟨hTl', hTSl⟩, hall⟩ := hR
  have hz : p < (TL.zip TS).length := by simp [hTl', hTSl, hp]
  have hrow := hall _ (List.getElem_mem hz)
  rw [List.getElem_zip] at hrow
  unfold tsRowOK at hrow
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hrow
  rw [getD_of_lt TS p [] (by omega), getD_of_lt TL p default (by omega)]
  exact ⟨hTSl, hrow.1.1, hrow.1.2, fun q hq => hrow.2 q hq⟩

include hR in
theorem recInc_sub : recInc TS ⊆ incid TL SL := by
  intro x hx
  simp only [recInc, incid, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, ((row_facts hR hx.1.1).2.2.2 _ hx.2).2⟩

theorem card_filter_mem_row {r : List Nat} (hr : r.Pairwise (· < ·)) (hlt : ∀ q ∈ r, q < 1771) :
    ((Finset.range 1771).filter fun q => q ∈ r).card = r.length := by
  have : ((Finset.range 1771).filter fun q => q ∈ r) = r.toFinset := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hlt q h, h⟩⟩
  rw [this, List.toFinset_card_of_nodup (hr.imp fun h => Nat.ne_of_lt h)]

include hR in
theorem card_recInc : (recInc TS).card = 26565 := by
  unfold recInc
  rw [Finset.card_filter, Finset.sum_product]
  have : ∀ p ∈ Finset.range 3795,
      (∑ q ∈ Finset.range 1771, if (p, q).2 ∈ TS.getD (p, q).1 [] then 1 else 0) = 7 := by
    intro p hp
    rw [Finset.mem_range] at hp
    obtain ⟨-, hl, hpw, hq⟩ := row_facts hR hp
    rw [← Finset.card_filter, card_filter_mem_row hpw fun q h => (hq q h).1, hl]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range]
  rfl

theorem card_trios_le (hTi : TL.all trioItem = true)
    (hinj : ∀ i j (hi : i < TL.length) (hj : j < TL.length), TL[i] = TL[j] → i = j)
    (hTl : TL.length = 3795) {s : List Nat} (hs : sextItem s = true) :
    ((Finset.range 3795).filter fun p => Native.trioIn (TL.getD p default) s = true).card ≤ 15 := by
  have hti : ∀ p < 3795, trioItem (TL.getD p default) = true := fun p hp => by
    rw [getD_of_lt TL p default (by omega)]
    exact List.all_eq_true.1 hTi _ (List.getElem_mem _)
  calc _ ≤ match15.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun p => trioCode s (TL.getD p default)) ?_ ?_
        · intro p hp
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hp
          rw [Finset.mem_coe, List.mem_toFinset]
          exact trioCode_mem hs (hti p hp.1) hp.2
        · intro p hp p' hp' e
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hp hp'
          have := trioCode_inj hs (hti p hp.1) (hti p' hp'.1) hp.2 hp'.2 e
          rw [getD_of_lt TL p default (by omega), getD_of_lt TL p' default (by omega)] at this
          exact hinj p p' (by omega) (by omega) this
    _ ≤ match15.length := List.toFinset_card_le _
    _ = 15 := match15_length

include hTl hSl hTi hSi hinj in
theorem card_incid_le : (incid TL SL).card ≤ 26565 := by
  unfold incid
  rw [Finset.card_filter, Finset.sum_product_right]
  calc _ ≤ ∑ _q ∈ Finset.range 1771, 15 := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [Finset.mem_range] at hq
        dsimp only
        rw [← Finset.card_filter]
        have hs : sextItem (SL.getD q default) = true := by
          rw [getD_of_lt SL q default (by omega)]
          exact List.all_eq_true.1 hSi _ (List.getElem_mem _)
        exact card_trios_le hTi hinj hTl hs
    _ = 26565 := by rw [Finset.sum_const, Finset.card_range]; rfl

include hTl hSl hTi hSi hinj hR in
theorem incidence_iff {p q : Nat} (hp : p < 3795) (hq : q < 1771) :
    Native.trioIn (TL.getD p default) (SL.getD q default) = true ↔ q ∈ TS.getD p [] := by
  have he := Finset.eq_of_subset_of_card_le (recInc_sub hR)
    ((card_incid_le hTl hSl hTi hSi hinj).trans (card_recInc hR).ge)
  have := congrArg (fun F => (p, q) ∈ F) he
  simp only [recInc, incid, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    eq_iff_iff] at this
  simp only [hp, hq, true_and] at this
  exact this.symm

include hTl hSl hTi hSi hinj hR in
theorem trioSexts_of_rows (hT : Native.trioList () = TL.toArray)
    (hS : Native.sextList () = SL.toArray) : Native.trioSexts () = TS.toArray := by
  have hTSl := (row_facts hR (p := 0) (by omega)).1
  unfold Native.trioSexts
  simp only [hT, hS]
  refine Array.ext (by simp [hTSl, Native.nTrio]) fun p h1 h2 => ?_
  have hp : p < 3795 := by simpa [Native.nTrio] using h1
  simp only [Array.getElem_map, Array.getElem_range, List.getElem_toArray]
  rw [← getD_of_lt TS p [] (by omega)]
  obtain ⟨-, -, hpw, hrow⟩ := row_facts hR hp
  refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h h' => Nat.le_antisymm h h')
    ((List.pairwise_lt_range.filter _).imp Nat.le_of_lt) (hpw.imp Nat.le_of_lt) ?_
  refine (List.perm_ext_iff_of_nodup ((List.pairwise_lt_range.filter _).imp Nat.ne_of_lt)
    (hpw.imp Nat.ne_of_lt)).2 fun q => ?_
  simp only [List.mem_filter, List.mem_range, Native.nSext]
  rw [toArray_getElem!_eq_getD, toArray_getElem!_eq_getD]
  constructor
  · rintro ⟨hq, h⟩
    exact (incidence_iff hTl hSl hTi hSi hinj hR hp hq).1 h
  · intro h
    have hq := (hrow q h).1
    exact ⟨hq, (incidence_iff hTl hSl hTi hSi hinj hR hp hq).2 h⟩

end Count

end CFSG.KC.M24G
