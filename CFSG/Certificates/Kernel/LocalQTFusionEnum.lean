module

public import Certificates.Data.Kernel.LocalQT.Fusion
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

import CFSG.Certificates.Kernel.LocalQTBaseSProved
import all CFSG.Certificates.Kernel.LocalQTBaseProved
public import Std.Data.HashMap.Lemmas

namespace CFSG.KC.LQT.FU

open CFSG.KC.Ord CFSG.KC.LQT.L CFSG.KC.LQT.BC CFSG.KC.LQT.BC.Pf
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BS.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm

variable {n : Nat}

theorem can_ext {c d : Nat} (hc : Can n c) (hd : Can n d) (h : ∀ i < n, P.img c i = P.img d i) :
    c = d := by
  rw [hc.2, hd.2]
  exact P.E_congr h

theorem can_mul (hn : n ≤ 32) {c d : Nat} (hc : Can n c) (hd : Can n d) : Can n (P.mul n c d) :=
  can_ofFn hn (g := fun i => P.img c (P.img d i)) fun j hj => hc.1 _ (hd.1 j hj)

theorem can_one (hn : n ≤ 32) : Can n (P.one n) :=
  can_ofFn hn (g := fun i => i) fun j hj => hj

theorem mul_assoc' (hn : n ≤ 32) {a b c : Nat} (ha : Can n a) (hb : Can n b) (hc : Can n c) :
    P.mul n (P.mul n a b) c = P.mul n a (P.mul n b c) :=
  can_ext (can_mul hn (can_mul hn ha hb) hc) (can_mul hn ha (can_mul hn hb hc)) fun i hi => by
    rw [img_mul hi, img_mul (hc.1 i hi), img_mul hi, img_mul hi]

theorem one_mul' (hn : n ≤ 32) {a : Nat} (ha : Can n a) : P.mul n (P.one n) a = a :=
  can_ext (can_mul hn (can_one hn) ha) ha fun i hi => by
    rw [img_mul hi, img_one hn (ha.1 i hi)]

theorem mul_one' (hn : n ≤ 32) {a : Nat} (ha : Can n a) : P.mul n a (P.one n) = a :=
  can_ext (can_mul hn ha (can_one hn)) ha fun i hi => by
    rw [img_mul hi, img_one hn hi]

noncomputable def Tab (n : Nat) (G : List (Array Nat)) (c : Nat) : List Nat :=
  (ptsOf (List.range n) G).map (P.img c)

theorem tab_getD {G : List (Array Nat)} {c q : Nat} (hq : q < n) :
    (Tab n G c).getD q 0 = P.img c q := by
  rw [Tab, getD_map_lt (by rw [ptsOf_length]; omega), ptsOf_getD hq]

theorem tab_val {G : List (Array Nat)} (hG : ∀ s ∈ G, ∀ q < n, img s q < n) {c : Nat}
    (hc : Can n c) : Val n (n + n * G.length) (Tab n G c) := by
  refine ⟨by simp [Tab, ptsOf_length], fun x hx => ?_⟩
  simp only [Tab, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact hc.1 p (ptsOf_lt hG p hp)

theorem tab_inj {G : List (Array Nat)} (hG : ∀ s ∈ G, ∀ q < n, img s q < n) {c d : Nat}
    (hc : Can n c) (hd : Can n d) (e : keyNat n n (Tab n G c) = keyNat n n (Tab n G d)) :
    c = d := by
  rw [BW.Pf.keyNat_eq_iff (tab_val hG hc) (tab_val hG hd)] at e
  refine can_ext hc hd fun q hq => ?_
  have := congrArg (fun l => l.getD q 0) e
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq] at this
  rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, tab_getD hq,
    tab_getD hq] at this
  exact this

theorem tab_apply {G : List (Array Nat)} (hG : ∀ s ∈ G, ∀ q < n, img s q < n) {g x : Nat}
    {s : Array Nat} (hg : NodeRep n g s) (hx : Can n x) :
    applyTab s (Tab n G x) = Tab n G (P.mul n g x) := by
  simp only [applyTab, Tab, List.map_map]
  apply List.map_congr_left
  intro p hp
  have hp' := ptsOf_lt hG p hp
  show img s (P.img x p) = P.img (P.mul n g x) p
  rw [img_mul hp', hg.2.2 _ (hx.1 p hp')]

theorem tab_one {G : List (Array Nat)} (hn : n ≤ 32) (hG : ∀ s ∈ G, ∀ q < n, img s q < n) :
    Tab n G (P.one n) = ptsOf (List.range n) G := by
  simp only [Tab]
  conv_rhs => rw [← List.map_id (ptsOf (List.range n) G)]
  apply List.map_congr_left
  intro p hp
  rw [img_one hn (ptsOf_lt hG p hp)]
  rfl

noncomputable def outerK (n : Nat) (G : List Nat) : List Nat → NT → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => NT → List Nat → Nat → Bool)
    (fun _ R _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) R)
    (fun x _ ih t R s => CFSG.KC.Ord.andB (Nat.blt 0 s) (kidsK n x G ih t R (Nat.sub s 1)))

theorem bfsOrdK_cons (n : Nat) (G : List Nat) (x0 : Nat) (R0 : List Nat) :
    bfsOrdK n G (x0 :: R0) = CFSG.KC.Ord.andB (Nat.beq x0 (P.one n))
      (outerK n G (x0 :: R0) (NT.nd NT.lf x0 NT.lf) R0 1) := rfl

theorem outerK_cons (n : Nat) (G : List Nat) (x : Nat) (Q : List Nat) (t : NT) (R : List Nat)
    (s : Nat) : outerK n G (x :: Q) t R s =
      CFSG.KC.Ord.andB (Nat.blt 0 s) (kidsK n x G (outerK n G Q) t R (Nat.sub s 1)) := rfl

theorem kidsK_nil (n x : Nat) (k : NT → List Nat → Nat → Bool) (t : NT) (R : List Nat)
    (s : Nat) : kidsK n x [] k t R s = k t R s := rfl

theorem kidsK_cons_true {n x : Nat} {g : Nat} {G : List Nat} {k : NT → List Nat → Nat → Bool}
    {t : NT} {R : List Nat} {s : Nat} (h : memT t (P.mul n g x) = true) :
    kidsK n x (g :: G) k t R s = kidsK n x G k t R s := by
  change P.letB (P.mul n g x) (fun c => Bool.rec (motive := fun _ => Bool)
    (List.rec (motive := fun _ => Bool) false
      (fun r R' _ => CFSG.KC.Ord.andB (Nat.beq c r) (kidsK n x G k (insT t c) R' (Nat.succ s))) R)
    (kidsK n x G k t R s) (memT t c)) = _
  rw [P.letB_eq, h]

theorem kidsK_cons_false {n x : Nat} {g : Nat} {G : List Nat} {k : NT → List Nat → Nat → Bool}
    {t : NT} {R : List Nat} {s : Nat} (h : memT t (P.mul n g x) = false) :
    kidsK n x (g :: G) k t R s =
      List.rec (motive := fun _ => Bool) false
        (fun r R' _ => CFSG.KC.Ord.andB (Nat.beq (P.mul n g x) r)
          (kidsK n x G k (insT t (P.mul n g x)) R' (Nat.succ s))) R := by
  change P.letB (P.mul n g x) (fun c => Bool.rec (motive := fun _ => Bool)
    (List.rec (motive := fun _ => Bool) false
      (fun r R' _ => CFSG.KC.Ord.andB (Nat.beq c r) (kidsK n x G k (insT t c) R' (Nat.succ s))) R)
    (kidsK n x G k t R s) (memT t c)) = _
  rw [P.letB_eq, h]

theorem body_found {nb i : Nat} {T : List Nat} {acc : St} {s : Array Nat}
    (h : acc.2.2.contains (keyNat n nb (applyTab s T)) = true) : bodyB n nb i T acc s = acc := by
  unfold bodyB
  rw [if_pos h]

theorem body_new {nb i : Nat} {T : List Nat} {acc : St} {s : Array Nat}
    (h : ¬ acc.2.2.contains (keyNat n nb (applyTab s T)) = true) :
    bodyB n nb i T acc s = (acc.1.push (applyTab s T), acc.2.1.push i,
      acc.2.2.insert (keyNat n nb (applyTab s T)) acc.1.size) := by
  unfold bodyB
  rw [if_neg h]

section Body

variable {nb : Nat} {G : List (Array Nat)} {Ul : List (List Nat)} {o : List Nat}

theorem body_inv' {S : St} (hc : BInv n nb G Ul o S) {i : Nat} (hi : i < S.1.size)
    {s : Array Nat} (hsG : s ∈ G) (hcU : applyTab s S.1[i]! ∈ Ul) :
    BInv n nb G Ul o (bodyB n nb i S.1[i]! S s) := by
  obtain ⟨hps, hpos, h0, hU, hmc, hmg, hpar⟩ := hc
  unfold bodyB
  by_cases hf : S.2.2.contains (keyNat n nb (applyTab s S.1[i]!)) = true
  · rw [ite_eq_left hf]
    exact ⟨hps, hpos, h0, hU, hmc, hmg, hpar⟩
  · rw [ite_eq_right hf]
    generalize hcdef : applyTab s S.1[i]! = c at hf hcU
    have hnotN : ∀ j < S.1.size, keyNat n nb S.1[j]! ≠ keyNat n nb c := fun j hj e =>
      hf ((hmc _).2 ⟨j, hj, e⟩)
    have hext : BW.Pf.Ext S (S.1.push c, S.2.1.push i, S.2.2.insert (keyNat n nb c) S.1.size)
        [c] := by
      simp [BW.Pf.Ext]
    have hgetS : ∀ j < S.1.size, (S.1.push c)[j]! = S.1[j]! := fun j hj => ext_get hext hj
    have hgetN : (S.1.push c)[S.1.size]! = c := by
      rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]
    refine ⟨by simp [hps], by simp, by rw [hgetS 0 hpos, h0], ?_, ?_, ?_, ?_⟩
    · intro T hT
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hT
      rcases hT with hT | rfl
      · exact hU T hT
      · exact hcU
    · intro y
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hmc]
      constructor
      · rintro (rfl | ⟨j, hj, e⟩)
        · exact ⟨S.1.size, by simp, by rw [hgetN]⟩
        · exact ⟨j, by simp; omega, by rw [hgetS j hj, e]⟩
      · rintro ⟨j, hj, e⟩
        simp only [Array.size_push] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inr ⟨j, hj, by rw [← hgetS j hj, e]⟩
        · exact Or.inl (by rw [← e, hgetN])
    · intro j hj
      rw [Std.HashMap.getD_insert]
      simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hgetS j hj, ite_eq_right (by rw [beq_iff_eq]; exact fun e => hnotN j hj e.symm)]
        exact hmg j hj
      · rw [hgetN, ite_eq_left (by rw [beq_iff_eq])]
    · intro j hj hj0
      simp only [Array.size_push] at hj
      have hpget : ∀ k < S.1.size, (S.2.1.push i)[k]! = S.2.1[k]! := by
        intro k hk
        rw [arr_getN, arr_getN, Array.toList_push, getD_append_left (by simp; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨h1, s', hs', h2⟩ := hpar j hj hj0
        rw [hpget j hj, hgetS j hj, hgetS _ (by omega)]
        exact ⟨h1, s', hs', h2⟩
      · have e : (S.2.1.push i)[S.1.size]! = i := by
          rw [arr_getN, Array.toList_push, ← hps]
          rw [show S.2.1.size = S.2.1.toList.length by simp, getD_append_len]
        rw [e, hgetN, hgetS i hi, ← hcdef]
        exact ⟨hi, s, hsG, rfl⟩

end Body

section Sim

variable {G : List (Array Nat)} {L : List Nat}

def Inv (n : Nat) (G : List (Array Nat)) (L : List Nat) (m : Nat) (S : St) : Prop :=
  1 ≤ m ∧ m ≤ L.length ∧ (∀ x ∈ L.take m, Can n x) ∧
  S.1.toList = (L.take m).map (Tab n G) ∧
  BInv n n G (L.map (Tab n G)) (ptsOf (List.range n) G) S

theorem inv_size {m : Nat} {S : St} (h : Inv n G L m S) : S.1.size = m := by
  have := congrArg List.length h.2.2.2.1
  simp only [Array.length_toList, List.length_map, List.length_take] at this
  have := h.2.1
  omega

theorem mem_take_getD {j m : Nat} (hj : j < m) (hm : m ≤ L.length) : L.getD j 0 ∈ L.take m := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact List.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩

theorem mem_take_idx {c m : Nat} (h : c ∈ L.take m) : ∃ j < m, L.getD j 0 = c := by
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 h
  simp only [List.length_take] at hj
  refine ⟨j, by omega, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simpa using e

theorem inv_get {m : Nat} {S : St} (h : Inv n G L m S) {i : Nat} (hi : i < m) :
    S.1[i]! = Tab n G (L.getD i 0) := by
  have hm := h.2.1
  rw [arr_getL, h.2.2.2.1, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_take_of_lt hi, List.getElem?_eq_getElem (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < L.length by omega)]

theorem take_succ' {m : Nat} (h : m < L.length) : L.take (m + 1) = L.take m ++ [L.getD m 0] := by
  rw [List.take_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem drop_cons' {m : Nat} {r : Nat} {R' : List Nat} (h : r :: R' = L.drop m) :
    m < L.length ∧ r = L.getD m 0 ∧ R' = L.drop (m + 1) := by
  have hm : m < L.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    exact absurd h (by simp)
  rw [List.drop_eq_getElem_cons hm] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
  obtain ⟨h1, h2⟩ := List.cons.inj h
  exact ⟨hm, h1, h2⟩

theorem take_mono {m m' y : Nat} (h : m ≤ m') (hm' : m' ≤ L.length) (hy : y ∈ L.take m) :
    y ∈ L.take m' := by
  obtain ⟨j, hj, rfl⟩ := mem_take_idx hy
  exact mem_take_getD (by omega) hm'

theorem kids_sim (hn : n ≤ 32) (hG : ∀ s ∈ G, ∀ q < n, img s q < n) {i x : Nat} {T : List Nat}
    (hT : T = Tab n G x) :
    ∀ (Gp : List (Nat × Array Nat)), (∀ p ∈ Gp, NodeRep n p.1 p.2 ∧ p.2 ∈ G) →
    ∀ (k : NT → List Nat → Nat → Bool) (t : NT) (R : List Nat) (s m : Nat) (S : St),
    Inv n G L m S → x ∈ L.take m → OrdN t → (∀ y, memN t y ↔ y ∈ L.take m) → R = L.drop m →
    s + i + 1 = m → S.1[i]! = T →
    kidsK n x (Gp.map Prod.fst) k t R s = true →
    ∃ m' t' R' s', Inv n G L m' ((Gp.map Prod.snd).foldl (bodyB n n i T) S) ∧ x ∈ L.take m' ∧
      m ≤ m' ∧ (∀ q ∈ Gp, P.mul n q.1 x ∈ L.take m') ∧
      OrdN t' ∧ (∀ y, memN t' y ↔ y ∈ L.take m') ∧ R' = L.drop m' ∧ s' + i + 1 = m' ∧
      k t' R' s' = true := by
  intro Gp
  induction Gp with
  | nil =>
    intro _ k t R s m S hI hx ho hm hR hs hS hk
    refine ⟨m, t, R, s, hI, hx, le_refl _, fun q hq => absurd hq (by simp), ho, hm, hR, hs, ?_⟩
    simpa [kidsK_nil] using hk
  | cons p Gp ih =>
    intro hGp k t R s m S hI hx ho hm hR hs hS hk
    have hp := hGp p (List.mem_cons_self ..)
    have hGp' : ∀ q ∈ Gp, NodeRep n q.1 q.2 ∧ q.2 ∈ G :=
      fun q hq => hGp q (List.mem_cons_of_mem _ hq)
    have hxC : Can n x := hI.2.2.1 x hx
    have hcC : Can n (P.mul n p.1 x) := can_mul hn hp.1.2.1 hxC
    have hap : applyTab p.2 T = Tab n G (P.mul n p.1 x) := by
      rw [hT]
      exact tab_apply hG hp.1 hxC
    have hsize := inv_size hI
    have him : i < S.1.size := by omega
    have hB := hI.2.2.2.2
    have hmL := hI.2.1
    rw [List.map_cons] at hk
    simp only [List.map_cons, List.foldl_cons]
    by_cases hmem : memT t (P.mul n p.1 x) = true
    · rw [kidsK_cons_true hmem] at hk
      have hmN := (memT_iff ho _).1 hmem
      have hmL' : P.mul n p.1 x ∈ L.take m := (hm _).1 hmN
      obtain ⟨j, hj, hjv⟩ := mem_take_idx hmL'
      have hcont : S.2.2.contains (keyNat n n (applyTab p.2 T)) = true := by
        rw [hap, hB.2.2.2.2.1]
        refine ⟨j, by omega, ?_⟩
        rw [inv_get hI hj, hjv]
      rw [body_found hcont]
      obtain ⟨m', t', R'', s', hI', hx', hmm', hcl, ho', hm', hR', hs', hk'⟩ :=
        ih hGp' k t R s m S hI hx ho hm hR hs hS hk
      refine ⟨m', t', R'', s', hI', hx', hmm', fun q hq => ?_, ho', hm', hR', hs', hk'⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact take_mono hmm' hI'.2.1 hmL'
      · exact hcl q hq
    · have hfalse : memT t (P.mul n p.1 x) = false := by simpa using hmem
      rw [kidsK_cons_false hfalse] at hk
      cases R with
      | nil => exact absurd hk (by simp)
      | cons r R' =>
        change CFSG.KC.Ord.andB (Nat.beq (P.mul n p.1 x) r) _ = true at hk
        rw [P.andB_iff, P.beq_iff] at hk
        obtain ⟨hcr, hk⟩ := hk
        obtain ⟨hmlt, hrL, hR'⟩ := drop_cons' hR
        have hcL : P.mul n p.1 x = L.getD m 0 := hcr.trans hrL
        have hnc : ¬ S.2.2.contains (keyNat n n (applyTab p.2 T)) = true := by
          rw [hap, hB.2.2.2.2.1]
          rintro ⟨j, hj, e⟩
          have hjm : j < m := by omega
          rw [inv_get hI hjm] at e
          have hjc : L.getD j 0 = P.mul n p.1 x :=
            tab_inj hG (hI.2.2.1 _ (mem_take_getD hjm hmL)) hcC e
          exact hmem ((memT_iff ho _).2 ((hm _).2 (hjc ▸ mem_take_getD hjm hmL)))
        have hext : BW.Pf.Ext S (S.1.push (applyTab p.2 T), S.2.1.push i,
            S.2.2.insert (keyNat n n (applyTab p.2 T)) S.1.size) [applyTab p.2 T] := by
          simp [BW.Pf.Ext]
        have hnew := body_new (i := i) hnc
        have hcU : applyTab p.2 S.1[i]! ∈ L.map (Tab n G) := by
          rw [hS, hap, hcL]
          exact List.mem_map_of_mem (getD_mem hmlt)
        have hB1 := body_inv' hB him hp.2 hcU
        rw [hS] at hB1
        have hI1 : Inv n G L (m + 1) (bodyB n n i T S p.2) := by
          refine ⟨by omega, by omega, ?_, ?_, hB1⟩
          · rw [take_succ' hmlt]
            intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · exact hI.2.2.1 y hy
            · rw [List.mem_singleton.1 hy, ← hcL]
              exact hcC
          · rw [hnew, Array.toList_push, hI.2.2.2.1, take_succ' hmlt, List.map_append, hap, hcL]
            rfl
        have hx1 : x ∈ L.take (m + 1) := by
          rw [take_succ' hmlt]
          exact List.mem_append_left _ hx
        have hm1 : ∀ y, memN (insT t (P.mul n p.1 x)) y ↔ y ∈ L.take (m + 1) := by
          intro y
          rw [mem_insT, hm, take_succ' hmlt, List.mem_append, List.mem_singleton, hcL]
          tauto
        have hS1 : (bodyB n n i T S p.2).1[i]! = T := by
          rw [hnew]
          exact (ext_get hext him).trans hS
        obtain ⟨m', t', R'', s', hI', hx', hmm', hcl, ho', hm', hR'', hs', hk'⟩ :=
          ih hGp' k (insT t (P.mul n p.1 x)) R' (s + 1) (m + 1) _ hI1 hx1 (ord_insT _ ho) hm1
            (by rw [hR']) (by omega) hS1 hk
        refine ⟨m', t', R'', s', hI', hx', by omega, fun q hq => ?_, ho', hm', hR'', hs', hk'⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · refine take_mono hmm' hI'.2.1 ?_
          rw [take_succ' hmlt, hcL]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · exact hcl q hq

theorem outer_sim (hn : n ≤ 32) (hG : ∀ s ∈ G, ∀ q < n, img s q < n)
    {Gp : List (Nat × Array Nat)} (hGp : ∀ p ∈ Gp, NodeRep n p.1 p.2 ∧ p.2 ∈ G)
    (hGG : Gp.map Prod.snd = G) :
    ∀ (Q : List Nat) (i f : Nat) (t : NT) (R : List Nat) (s m : Nat) (S : St),
    Q = L.drop i → Inv n G L m S → OrdN t → (∀ y, memN t y ↔ y ∈ L.take m) → R = L.drop m →
    s + i = m → L.length ≤ f + i → outerK n (Gp.map Prod.fst) Q t R s = true →
    Inv n G L L.length (bfsLoopB n n G f i S) ∧
      ∀ i', i ≤ i' → i' < L.length → ∀ q ∈ Gp, P.mul n q.1 (L.getD i' 0) ∈ L := by
  intro Q
  induction Q with
  | nil =>
    intro i f t R s m S hQ hI ho hm hR hs hf hk
    have hi : L.length ≤ i := by
      by_contra hc
      have hlt : i < L.length := by omega
      rw [List.drop_eq_getElem_cons hlt] at hQ
      exact List.cons_ne_nil _ _ hQ.symm
    have hmL := hI.2.1
    have hmi : m = L.length := by omega
    have hsz := inv_size hI
    have hi' : i = S.1.size := by omega
    rw [hi', bfsLoopB_stop]
    rw [hmi] at hI
    exact ⟨hI, fun i' h1 h2 => by omega⟩
  | cons x Q ih =>
    intro i f t R s m S hQ hI ho hm hR hs hf hk
    rw [outerK_cons, P.andB_iff, P.blt_iff] at hk
    obtain ⟨hs0, hk⟩ := hk
    have hiL : i < L.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hQ
      exact absurd hQ (by simp)
    rw [List.drop_eq_getElem_cons hiL] at hQ
    obtain ⟨hx, hQ'⟩ := List.cons.inj hQ
    have hx' : x = L.getD i 0 := by
      rw [hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL, Option.getD_some]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have him : i < m := by omega
    have hsz := inv_size hI
    have hxm : x ∈ L.take m := hx' ▸ mem_take_getD him hI.2.1
    have hSi : S.1[i]! = Tab n G x := by rw [inv_get hI him, hx']
    have hs' : Nat.sub s 1 + i + 1 = m := by
      simp only [Nat.sub_eq]
      omega
    obtain ⟨m', t', R', s', hI', -, hmm', hcl, ho', hm', hR', hs'', hk'⟩ := kids_sim hn hG hSi Gp hGp
      (outerK n (Gp.map Prod.fst) Q) t R (Nat.sub s 1) m S hI hxm ho hm hR hs' rfl hk
    rw [hGG] at hI'
    rw [bfsLoopB_succ, if_pos (by omega)]
    obtain ⟨hIf, hcf⟩ := ih (i + 1) f' t' R' s' m' _ (by rw [hQ']) hI' ho' hm' hR' (by omega)
      (by omega) hk'
    refine ⟨hIf, fun i' h1 h2 q hq => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · rw [← hx']
      exact List.mem_of_mem_take (hcl q hq)
    · exact hcf i' h1 h2 q hq

theorem enum_loop (hn : n ≤ 32) (hG : ∀ s ∈ G, ∀ q < n, img s q < n)
    {Gp : List (Nat × Array Nat)} (hGp : ∀ p ∈ Gp, NodeRep n p.1 p.2 ∧ p.2 ∈ G)
    (hGG : Gp.map Prod.snd = G) {fuel : Nat} (hfuel : L.length ≤ fuel)
    (hord : bfsOrdK n (Gp.map Prod.fst) L = true) :
    Inv n G L L.length
      (bfsLoopB n n G fuel 0 (#[ptsOf (List.range n) G], #[0],
        (∅ : Std.HashMap Nat Nat).insert (keyNat n n (ptsOf (List.range n) G)) 0)) ∧
      ∀ i', i' < L.length → ∀ q ∈ Gp, P.mul n q.1 (L.getD i' 0) ∈ L := by
  cases L with
  | nil => exact absurd hord (by simp [bfsOrdK])
  | cons x0 R0 =>
    rw [bfsOrdK_cons, P.andB_iff, P.beq_iff] at hord
    obtain ⟨hx0, hout⟩ := hord
    have hone := tab_one hn hG
    have hoU : ptsOf (List.range n) G ∈ (x0 :: R0).map (Tab n G) := by
      rw [← hone, ← hx0]
      exact List.mem_map_of_mem (List.mem_cons_self ..)
    have hS0 : Inv n G (x0 :: R0) 1 (#[ptsOf (List.range n) G], #[0],
        (∅ : Std.HashMap Nat Nat).insert (keyNat n n (ptsOf (List.range n) G)) 0) := by
      refine ⟨le_refl _, by simp, ?_, ?_, ?_⟩
      · intro x hx
        simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hx
        rw [hx, hx0]
        exact can_one hn
      · simp [hx0, hone]
      · have hget : ∀ i < 1, (#[ptsOf (List.range n) G] : Array (List Nat))[i]! =
            ptsOf (List.range n) G := by
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          rfl
        refine ⟨rfl, by simp, rfl, fun T' hT' => ?_, fun y => ?_, fun i hi => ?_,
          fun i hi hi0 => ?_⟩
        · rw [show T' = ptsOf (List.range n) G by simpa using hT']
          exact hoU
        · simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
            beq_iff_eq]
          constructor
          · rintro rfl
            exact ⟨0, by simp, rfl⟩
          · rintro ⟨i, hi, rfl⟩
            have hi0 : i = 0 := by simpa using hi
            subst hi0
            rfl
        · have hi' : i < 1 := by simpa using hi
          rw [hget i hi']
          simp only [Std.HashMap.getD_insert, beq_self_eq_true, ite_true]
          omega
        · have hi' : i < 1 := by simpa using hi
          omega
    obtain ⟨h1, h2⟩ := outer_sim hn hG hGp hGG (x0 :: R0) 0 fuel (NT.nd NT.lf x0 NT.lf) R0 1 1 _
      rfl hS0 (by simp [OrdN, memN]) (fun y => by simp [memN]) rfl rfl (by simpa using hfuel) hout
    exact ⟨h1, fun i' hi' => h2 i' (Nat.zero_le _) hi'⟩

structure CayL (n N g gi : Nat) (par cl : Array Nat) (Gc : List Nat) (Lx : Nat → Nat) : Prop where
  pos : 0 < N
  zero : Lx 0 = P.one n
  can : ∀ i < N, Can n (Lx i)
  inj : ∀ i < N, ∀ k < N, Lx i = Lx k → i = k
  step : ∀ i < N, ∀ j < g, cl[i * (g + gi) + j]! < N ∧
    Lx (cl[i * (g + gi) + j]!) = P.mul n (Gc.getD j 0) (Lx i)
  parent : ∀ i < N, 0 < i → par[i]! < i ∧
    ∃ j < g, Lx i = P.mul n (Gc.getD j 0) (Lx par[i]!)

theorem ord_zero {Gc : List Nat} (hord : bfsOrdK n Gc L = true) : L.getD 0 0 = P.one n := by
  cases L with
  | nil => exact absurd hord (by simp [bfsOrdK])
  | cons x0 R0 =>
    rw [bfsOrdK_cons, P.andB_iff, P.beq_iff] at hord
    exact hord.1

theorem gen_idx {Gp : List (Nat × Array Nat)} {j : Nat} (hj : j < Gp.length) :
    ∃ p ∈ Gp, p.2 = (Gp.map Prod.snd)[j]! ∧ p.1 = (Gp.map Prod.fst).getD j 0 := by
  refine ⟨Gp[j], List.getElem_mem hj, ?_, ?_⟩
  · rw [getElem!_pos _ j (by simpa using hj), List.getElem_map]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
    rfl

theorem enum_cay (hn : n ≤ 32) {Gp : List (Nat × Array Nat)}
    (hG : ∀ s ∈ Gp.map Prod.snd, ∀ q < n, img s q < n)
    (hGp : ∀ p ∈ Gp, NodeRep n p.1 p.2 ∧ p.2 ∈ Gp.map Prod.snd) (Gi : List (Array Nat))
    {fuel : Nat} (hfuel : L.length ≤ fuel)
    (hord : bfsOrdK n (Gp.map Prod.fst) L = true) :
    (bfsEnumB n (List.range n) (Gp.map Prod.snd) Gi fuel).1.size = L.length ∧
    (∀ i < L.length, (bfsEnumB n (List.range n) (Gp.map Prod.snd) Gi fuel).1[i]! =
      Tab n (Gp.map Prod.snd) (L.getD i 0)) ∧
    CayL n L.length Gp.length Gi.length (bfsEnumB n (List.range n) (Gp.map Prod.snd) Gi fuel).2.1
      (bfsEnumB n (List.range n) (Gp.map Prod.snd) Gi fuel).2.2 (Gp.map Prod.fst)
      (fun i => L.getD i 0) := by
  obtain ⟨hI, hcl⟩ := enum_loop hn hG hGp rfl hfuel hord
  generalize hSf : bfsLoopB n n (Gp.map Prod.snd) fuel 0 (#[ptsOf (List.range n) (Gp.map Prod.snd)],
    #[0], (∅ : Std.HashMap Nat Nat).insert
      (keyNat n n (ptsOf (List.range n) (Gp.map Prod.snd))) 0) = S at hI
  have hbe : bfsEnumB n (List.range n) (Gp.map Prod.snd) Gi fuel = (S.1, S.2.1,
      (List.range S.1.size).foldl (fun acc i => ((Gp.map Prod.snd) ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n n (applyTab s S.1[i]!)) 0)) acc) #[]) := by
    simp only [bfsEnumB, List.length_range, hSf]
  have hsz := inv_size hI
  obtain ⟨hps, hpos, h0, hU, hmc, hmg, hpar⟩ := hI.2.2.2.2
  have hclget : ∀ i < S.1.size, ∀ j < ((Gp.map Prod.snd) ++ Gi).length,
      ((List.range S.1.size).foldl (fun acc i => ((Gp.map Prod.snd) ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n n (applyTab s S.1[i]!)) 0)) acc)
        (#[] : Array Nat))[i * ((Gp.map Prod.snd).length + Gi.length) + j]! =
      S.2.2.getD (keyNat n n (applyTab ((Gp.map Prod.snd) ++ Gi)[j]! S.1[i]!)) 0 := by
    intro i hi j hj
    rw [arr_getN, cl_fold, ← List.length_append]
    exact (flatMap_getD ((Gp.map Prod.snd) ++ Gi) _ S.1.size).2 i hi j hj
  have hclget' : ∀ i < S.1.size, ∀ j < ((Gp.map Prod.snd) ++ Gi).length,
      ((List.range S.1.size).foldl (fun acc i => ((Gp.map Prod.snd) ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n n (applyTab s S.1[i]!)) 0)) acc)
        (#[] : Array Nat))[i * (Gp.length + Gi.length) + j]! =
      S.2.2.getD (keyNat n n (applyTab ((Gp.map Prod.snd) ++ Gi)[j]! S.1[i]!)) 0 := by
    intro i hi j hj
    have := hclget i hi j hj
    rwa [List.length_map] at this
  have hget : ∀ i < L.length, S.1[i]! = Tab n (Gp.map Prod.snd) (L.getD i 0) :=
    fun i hi => inv_get hI hi
  have hcan : ∀ i < L.length, Can n (L.getD i 0) :=
    fun i hi => hI.2.2.1 _ (mem_take_getD hi (le_refl _))
  rw [hbe]
  dsimp only
  refine ⟨hsz, hget, ?_⟩
  refine ⟨by have := hI.1; omega, ord_zero hord, hcan, ?_, ?_, ?_⟩
  · intro i hi k hk e
    have h1 := hmg i (by omega)
    have h2 := hmg k (by omega)
    rw [hget i hi] at h1
    rw [hget k hk] at h2
    rw [e] at h1
    exact h1.symm.trans h2
  · intro i hi j hj
    obtain ⟨p, hp, hp2, hp1⟩ := gen_idx hj
    have hrep := (hGp p hp).1
    have hjG : j < (Gp.map Prod.snd).length := by simpa using hj
    have hc : P.mul n p.1 (L.getD i 0) ∈ L := hcl i hi p hp
    obtain ⟨k, hk, hkc⟩ := mem_take_idx (L := L) (m := L.length) (by rwa [List.take_length])
    have hkey : S.2.2.getD (keyNat n n (applyTab ((Gp.map Prod.snd) ++ Gi)[j]! S.1[i]!)) 0 = k := by
      rw [getBang_append_left hjG, ← hp2, hget i hi, tab_apply hG hrep (hcan i hi), ← hkc,
        ← hget k hk]
      exact hmg k (by omega)
    refine ⟨?_, ?_⟩
    · rw [hclget' i (by omega) j (by simp; omega), hkey]
      exact hk
    · rw [hclget' i (by omega) j (by simp; omega), hkey, hkc, hp1]
  · intro i hi hi0
    obtain ⟨h1, s', hs', h2⟩ := hpar i (by omega) hi0
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs'
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hp
    have hrep := (hGp _ (List.getElem_mem hj)).1
    refine ⟨h1, j, hj, ?_⟩
    have hpar' : S.2.1[i]! < L.length := by omega
    rw [hget i hi, hget _ hpar', tab_apply hG hrep (hcan _ hpar')] at h2
    have := tab_inj hG (hcan i hi) (can_mul hn hrep.2.1 (hcan _ hpar')) (by rw [h2])
    rw [this]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
    rfl

end Sim

end CFSG.KC.LQT.FU
