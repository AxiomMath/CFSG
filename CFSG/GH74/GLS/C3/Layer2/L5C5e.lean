module

public import CFSG.GH74.GLS.C3.Layer2.L5C5d
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5d
public import CFSG.GH74.GLS.C3.Layer2.L5C5eInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5eInputs
public import Certificates.Certificate5051
public import Certificates.Certificate5065
public import Certificates.Certificate5066
public import Certificates.Certificate5068

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem mem_all2 {p : Nat × Bool} : p ∈ all2 ↔ p.1 < 128 := by
  obtain ⟨i, b⟩ := p
  simp only [all2, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨j, hj, h | h⟩ <;> simp_all
  · intro h
    cases b
    · exact ⟨i, h, Or.inl rfl⟩
    · exact ⟨i, h, Or.inr rfl⟩

@[expose] def dec2
    (m : Fin 4) (p : Nat × Bool) : Sh2 m := ⟨dec0 p.1, p.2⟩

theorem dec2_surj
    {m : Fin 4} (x : Sh2 m) : ∃ p : Nat × Bool, p.1 < 128 ∧ dec2 m p = x := by
  obtain ⟨i, hi, hx⟩ := dec0_surj x.fst
  exact ⟨(i, x.snd), hi, Ext2.ext hx rfl⟩

theorem dec2_inj
    {m : Fin 4} {p q : Nat × Bool} (hp : p.1 < 128) (hq : q.1 < 128)
    (h : dec2 m p = dec2 m q) : p = q := by
  have h1 : dec0 p.1 = dec0 q.1 := congrArg Ext2.fst h
  have h2 : p.2 = q.2 := congrArg Ext2.snd h
  exact Prod.ext (dec0_inj hp hq h1) h2

theorem gamTab_lt
    {m : Fin 4} {j : Nat} (hj : j < 128) : (gamTabs.getD m.val #[]).getD j 0 < 128 :=
  ((gam_facts m.2).2.1 j hj).1

theorem mul2_lt
    (m : Fin 4) {p q : Nat × Bool} (hp : p.1 < 128) (hq : q.1 < 128) :
    (mul2 m.val p q).1 < 128 := by
  obtain ⟨i, b⟩ := p
  obtain ⟨j, c⟩ := q
  cases b <;> cases c <;> simp only [mul2]
  · exact mt0_lt hp hq
  · exact mt0_lt hp hq
  · exact mt0_lt hp (gamTab_lt hq)
  · exact mt0_lt (mt0_lt hp (gamTab_lt hq)) (gam_facts m.2).1

theorem dec2_mul
    (m : Fin 4) {p q : Nat × Bool} (hp : p.1 < 128) (hq : q.1 < 128) :
    dec2 m (mul2 m.val p q) = dec2 m p * dec2 m q := by
  obtain ⟨i, b⟩ := p
  obtain ⟨j, c⟩ := q
  cases b <;> cases c <;> simp only [mul2, dec2]
  · rw [Ext2.mul_ff, dec0_mul hp hq]
  · rw [Ext2.mul_ft, dec0_mul hp hq]
  · rw [Ext2.mul_tf]
    simp only [ext2Data]
    rw [gam_dec0 m hq, dec0_mul hp (gamTab_lt hq)]
  · rw [Ext2.mul_tt]
    simp only [ext2Data]
    rw [gam_dec0 m hq, dec0_mul (mt0_lt hp (gamTab_lt hq)) (gam_facts m.2).1,
      dec0_mul hp (gamTab_lt hq)]

theorem inv2_lt
    (m : Fin 4) {p : Nat × Bool} (hp : p.1 < 128) : (inv2 m.val p).1 < 128 := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp only [inv2]
  · exact inv0_lt hp
  · exact mt0_lt (inv0_lt (gam_facts m.2).1) (gamTab_lt (inv0_lt hp))

theorem dec2_inv
    (m : Fin 4) {p : Nat × Bool} (hp : p.1 < 128) :
    dec2 m (inv2 m.val p) = (dec2 m p)⁻¹ := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp only [inv2, dec2]
  · rw [Ext2.inv_f, dec0_inv hp]
  · rw [Ext2.inv_t]
    refine Ext2.ext ?_ rfl
    show dec0 _ = (dec0 (ssData.getD m.val 0))⁻¹ * (gam m) (dec0 i)⁻¹
    rw [← dec0_inv hp, ← dec0_inv (gam_facts m.2).1, gam_dec0 m (inv0_lt hp),
      ← dec0_mul (inv0_lt (gam_facts m.2).1) (gamTab_lt (inv0_lt hp))]

theorem dec2_one
    (m : Fin 4) : dec2 m (0, false) = 1 := by
  show (⟨dec0 0, false⟩ : Ext2 (ext2Data m)) = ⟨1, false⟩
  rw [dec0_zero]

theorem sh2Chks_true :
    (List.range 4).all (fun m => sh2E16Chk1 m && sh2E16Chk2 m && sh2MoveChk m) = true :=
  Certificates.certificate5068

theorem chks_of {m : Fin 4} :
    sh2E16Chk1 m.val = true ∧ sh2E16Chk2 m.val = true ∧ sh2MoveChk m.val = true := by
  have h := sh2Chks_true
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  have := h m.val m.2
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem isInv2_of
    {m : Fin 4} {p : Nat × Bool} (hp : p.1 < 128) (h : dec2 m p * dec2 m p = 1) :
    isInv2 m.val p = true := by
  unfold isInv2
  apply decide_eq_true
  apply dec2_inj (m := m) (mul2_lt m hp hp) (by simp)
  rw [dec2_mul m hp hp, h, dec2_one]

theorem cent2_of
    {m : Fin 4} {p q : Nat × Bool} (hp : p.1 < 128) (hq : q.1 < 128)
    (h : dec2 m p * dec2 m q = dec2 m q * dec2 m p) : cent2 m.val p q = true := by
  unfold cent2
  apply decide_eq_true
  apply dec2_inj (m := m) (mul2_lt m hp hq) (mul2_lt m hq hp)
  rw [dec2_mul m hp hq, dec2_mul m hq hp, h]

theorem card_le_of_covered {X : Type*} (B : Set X) (l : List X) (h : ∀ b ∈ B, b ∈ l) :
    B.ncard ≤ l.length := by
  classical
  calc B.ncard ≤ (l.toFinset : Set X).ncard :=
        Set.ncard_le_ncard (fun b hb => by simpa using h b hb) (Finset.finite_toSet _)
    _ = l.toFinset.card := Set.ncard_coe_finset _
    _ ≤ l.length := List.toFinset_card_le l

theorem card_subgroup_le
    {m : Fin 4} (B : Subgroup (Sh2 m)) (S : List (Nat × Bool))
    (h : ∀ y ∈ B, ∃ q ∈ S, dec2 m q = y) : Nat.card B ≤ S.length := by
  have h1 : Nat.card B = (B : Set (Sh2 m)).ncard := Nat.card_coe_set_eq _
  rw [h1]
  calc (B : Set (Sh2 m)).ncard ≤ (S.map (dec2 m)).length :=
        card_le_of_covered _ _ (fun y hy => by
          obtain ⟨q, hq, rfl⟩ := h y hy
          exact List.mem_map.2 ⟨q, hq, rfl⟩)
    _ = S.length := List.length_map _

theorem B_cover
    {m : Fin 4} (B : Subgroup (Sh2 m)) (hel : ∀ b ∈ B, b * b = 1)
    (hab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) {p : Nat × Bool} (hp : p.1 < 128)
    (hpB : dec2 m p ∈ B) {y : Sh2 m} (hy : y ∈ B) :
    ∃ q, q.1 < 128 ∧ dec2 m q = y ∧ isInv2 m.val q = true ∧ cent2 m.val p q = true := by
  obtain ⟨q, hq, rfl⟩ := dec2_surj y
  exact ⟨q, hq, rfl, isInv2_of hq (hel _ hy), cent2_of hp hq (hab _ hpB _ hy)⟩

section E16

variable
  {m : Fin 4} (B : Subgroup (Sh2 m)) (hcard : Nat.card B = 16)
  (hel : ∀ b ∈ B, b * b = 1) (hab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)

include hcard hel hab

theorem B_inner :
    ∀ b ∈ B, b.snd = false := by
  intro b hb
  by_contra hs
  rw [Bool.not_eq_false] at hs
  obtain ⟨i, hi, hbe⟩ := dec0_surj b.fst
  have hbp : dec2 m (i, true) = b := Ext2.ext hbe hs.symm
  have hBb : dec2 m (i, true) ∈ B := hbp ▸ hb
  have hc := (chks_of (m := m)).1
  simp only [sh2E16Chk1, List.all_eq_true, mem_all2] at hc
  have hc1 := hc (i, true) hi
  have hinv : isInv2 m.val (i, true) = true := isInv2_of hi (hel _ hBb)
  simp only [Bool.true_and, hinv, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc1
  have hle := card_subgroup_le B (all2.filter fun q => isInv2 m.val q && cent2 m.val (i, true) q)
    (fun y hy => by
      obtain ⟨q, hq, hqy, h1, h2⟩ := B_cover B hel hab hi hBb hy
      exact ⟨q, List.mem_filter.2 ⟨mem_all2.2 hq, by simp [h1, h2]⟩, hqy⟩)
  omega

theorem B_RR1 :
    ∀ b ∈ B, ∃ i, (i ∈ RIdx ∨ i ∈ R1Idx) ∧ b = dec2 m (i, false) := by
  intro b hb
  have hs := B_inner B hcard hel hab b hb
  obtain ⟨i, hi, hbe⟩ := dec0_surj b.fst
  have hbp : dec2 m (i, false) = b := Ext2.ext hbe hs.symm
  refine ⟨i, ?_, hbp.symm⟩
  by_contra hn
  rw [not_or] at hn
  have hBb : dec2 m (i, false) ∈ B := hbp ▸ hb
  have hc := (chks_of (m := m)).2.1
  simp only [sh2E16Chk2, List.all_eq_true, mem_all2] at hc
  have hc1 := hc (i, false) hi
  have hinv : isInv2 m.val (i, false) = true := isInv2_of hi (hel _ hBb)
  simp only [Bool.not_false, hinv, hn.1, hn.2, decide_false, Bool.not_true,
    Bool.and_true, Bool.false_or, decide_eq_true_eq] at hc1
  have hle := card_subgroup_le B
    (all2.filter fun q => !q.2 && isInv2 m.val q && cent2 m.val (i, false) q)
    (fun y hy => by
      obtain ⟨q, hq, hqy, h1, h2⟩ := B_cover B hel hab hi hBb hy
      have hqs : q.2 = false := by
        have := B_inner B hcard hel hab y hy
        rw [← hqy] at this
        exact this
      exact ⟨q, List.mem_filter.2 ⟨mem_all2.2 hq, by simp [hqs, h1, h2]⟩, hqy⟩)
  omega

end E16

@[expose] def PK
    (m : Fin 4) (K : Subgroup (Perm (Fin 16))) (b : Sh2 m) : Prop :=
  ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ K ∧ b = inc m r

theorem PK_mul
    {m : Fin 4} {K : Subgroup (Perm (Fin 16))} {b b' : Sh2 m} (h : PK m K b)
    (h' : PK m K b') : PK m K (b * b') := by
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨r', hr', rfl⟩ := h'
  exact ⟨r * r', K.mul_mem hr hr', (map_mul (inc m) r r').symm⟩

theorem PK_inv
    {m : Fin 4} {K : Subgroup (Perm (Fin 16))} {b : Sh2 m} (h : PK m K b) :
    PK m K b⁻¹ := by
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨r⁻¹, K.inv_mem hr, (map_inv (inc m) r).symm⟩

theorem sh2_E16
    (ty : Fin 4) (B : Subgroup (Sh2 ty)) (hcard : Nat.card B = 16)
    (hel : ∀ b ∈ B, b * b = 1) (hab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    (∀ b ∈ B, ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 ∧ b = inc ty r) ∨
    (∀ b ∈ B, ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ R1subP ∧ b = inc ty r) := by
  have hRR : ∀ b ∈ B, PK ty RsubP0 b ∨ PK ty R1subP b := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := B_RR1 B hcard hel hab b hb
    rcases hi with hi | hi
    · exact Or.inl ⟨dec0 i, (mem_RIdx (lt_of_mem_RIdx hi)).1 hi, rfl⟩
    · exact Or.inr ⟨dec0 i, (mem_R1Idx (lt_of_mem_R1Idx hi)).1 hi, rfl⟩
  by_cases hP0 : ∀ b ∈ B, PK ty RsubP0 b
  · exact Or.inl hP0
  by_cases hP1 : ∀ b ∈ B, PK ty R1subP b
  · exact Or.inr hP1
  exfalso
  obtain ⟨b1, hb1, hn1⟩ : ∃ b ∈ B, ¬ PK ty RsubP0 b := by
    by_contra hc
    exact hP0 fun b hb => by_contra fun h => hc ⟨b, hb, h⟩
  obtain ⟨b2, hb2, hn2⟩ : ∃ b ∈ B, ¬ PK ty R1subP b := by
    by_contra hc
    exact hP1 fun b hb => by_contra fun h => hc ⟨b, hb, h⟩
  have hp1 : PK ty R1subP b1 := (hRR b1 hb1).resolve_left hn1
  have hp2 : PK ty RsubP0 b2 := (hRR b2 hb2).resolve_right hn2
  rcases hRR (b1 * b2) (B.mul_mem hb1 hb2) with h | h
  · apply hn1
    have := PK_mul h (PK_inv hp2)
    rwa [mul_inv_cancel_right] at this
  · apply hn2
    have := PK_mul (PK_inv hp1) h
    rwa [inv_mul_cancel_left] at this

theorem sh2_move
    (ty : Fin 4) (s : Sh2 ty) (hs : s ∉ (inc ty).range) :
    ∀ r1 : ↥Sh0, (r1 : Perm (Fin 16)) ∈ R1subP →
      ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 ∧ inc ty r1 = s * inc ty r * s⁻¹ := by
  intro r1 hr1
  have hsnd : s.snd = true := by
    by_contra h
    exact hs ((mem_range_inc ty).2 (by simpa using h))
  obtain ⟨i, hi, hse⟩ := dec0_surj s.fst
  have hsp : dec2 ty (i, true) = s := Ext2.ext hse hsnd.symm
  obtain ⟨j, hj, rfl⟩ := dec0_surj r1
  have hjR1 : j ∈ R1Idx := (mem_R1Idx hj).2 hr1
  have hmv := (chks_of (m := ty)).2.2
  simp only [sh2MoveChk, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq] at hmv
  obtain ⟨r, hrR, hmr⟩ := hmv i hi j hjR1
  have hr128 := lt_of_mem_RIdx hrR
  refine ⟨dec0 r, (mem_RIdx hr128).1 hrR, ?_⟩
  have hi' : ((i, true) : Nat × Bool).1 < 128 := hi
  have hr' : ((r, false) : Nat × Bool).1 < 128 := hr128
  have e1 : inc ty (dec0 j) = dec2 ty (j, false) := rfl
  have e2 : inc ty (dec0 r) = dec2 ty (r, false) := rfl
  rw [← hsp, e1, e2, ← dec2_inv ty hi', ← dec2_mul ty hi' hr',
    ← dec2_mul ty (mul2_lt ty hi' hr') (inv2_lt ty hi'), hmr]

end CFSG.GH74.GLS.C3.Layer2.L5
