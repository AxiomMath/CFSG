module

public import Certificates.Data.Kernel.J2Max76Fast

public section

namespace CFSG.KC.J2Max76

open Certificates.K76J2Max Certificates.G2ThreeMax CFSG.Monster.B.TwoA.Census CFSG.KC.Bfs

theorem forceJ_eq (y : ℕ) (k : ℕ → ℕ) : forceJ y k = k y := by
  cases y <;> rfl

theorem blt_land_shiftLeft (n i : ℕ) :
    Nat.blt (nat_lit 0) (Nat.land n (Nat.shiftLeft (nat_lit 1) i)) = n.testBit i := by
  have e : Nat.land n (Nat.shiftLeft (nat_lit 1) i) = n &&& 2 ^ i := by
    rw [← Nat.one_shiftLeft]
    rfl
  have h : ∀ j, (n &&& 2 ^ i).testBit j = (n.testBit j && decide (i = j)) := fun j => by
    rw [Nat.testBit_and, Nat.testBit_two_pow]
  rw [e]
  cases hb : n.testBit i
  · have h0 : n &&& 2 ^ i = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [h, Nat.zero_testBit]
      by_cases hij : i = j
      · subst hij
        rw [hb]
        rfl
      · simp [hij]
    rw [h0]
    rfl
  · have hx : 0 < n &&& 2 ^ i := Nat.pos_of_ne_zero fun h0 => by
      have := h i
      rw [h0, Nat.zero_testBit, hb] at this
      simp at this
    simpa using hx

theorem imgW_cons (n t : ℕ) (l : List ℕ) (i acc : ℕ) :
    imgW n (t :: l) i acc = imgW n l (i + 1) (if n.testBit i then acc ||| 2 ^ t else acc) := by
  change forceJ (Nat.succ i) (fun j => forceJ (Bool.rec (motive := fun _ => ℕ) acc
    (Nat.lor acc (Nat.shiftLeft (nat_lit 1) t))
    (Nat.blt (nat_lit 0) (Nat.land n (Nat.shiftLeft (nat_lit 1) i)))) fun a => imgW n l j a) = _
  rw [forceJ_eq, forceJ_eq, blt_land_shiftLeft]
  cases n.testBit i
  · rfl
  · rw [if_pos rfl, ← Nat.one_shiftLeft]
    rfl

theorem imgW_eq (n : ℕ) (l : List ℕ) (i acc : ℕ) :
    imgW n l i acc = (List.range l.length).foldl
      (fun acc j => if n.testBit (i + j) then acc ||| 2 ^ l[j]! else acc) acc := by
  induction l generalizing i acc with
  | nil => rfl
  | cons t l ih =>
    rw [imgW_cons, ih, List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [Nat.add_zero, List.getElem!_cons_zero, List.getElem!_cons_succ, Nat.add_assoc,
      Nat.add_comm 1]

theorem imgSet_eq_imgW (t : Array ℕ) (h : t.size = 315) (n : ℕ) :
    imgSet t n = imgW n t.toList 0 0 := by
  rw [imgW_eq, Array.length_toList, h]
  unfold imgSet
  simp only [Nat.zero_add, Array.getElem!_toList]

theorem act_eq_actK (G : List (List ℕ)) (hG : gensOK G = true) : act = actK G := by
  funext k n
  unfold actK
  cases hk : Nat.blt k (nat_lit 5)
  · rfl
  · have hk' : k < 5 := by simpa using hk
    unfold gensOK at hG
    rw [List.all_eq_true] at hG
    have hk2 := hG k (List.mem_range.mpr hk')
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hk2
    rw [forceJ_eq, hk2.1]
    exact imgSet_eq_imgW _ hk2.2 n

theorem arrEq (a b : Array (Array ℕ))
    (h : (a.toList.map Array.toList == b.toList.map Array.toList) = true) : a = b := by
  rw [beq_iff_eq] at h
  exact Array.toList_inj.mp ((List.map_injective_iff.mpr fun x y e => Array.toList_inj.mp e) h)

theorem certEqB_eq (c d : NatCert) (h : certEqB c d = true) : c = d := by
  obtain ⟨p, e, q, l⟩ := c
  obtain ⟨p', e', q', l'⟩ := d
  unfold certEqB at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.toList_inj] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [h1, h3, h4, arrEq e e' (beq_iff_eq.mpr h2)]

theorem orbsEqB_eq (a b : List (ℕ × NatCert)) (h : orbsEqB a b = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => simp [orbsEqB] at h
  | cons x xs ih =>
    cases b with
    | nil => simp [orbsEqB] at h
    | cons y ys =>
      simp only [orbsEqB, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [ih ys h3, Prod.ext h1 (certEqB_eq _ _ h2)]

theorem repOKL_of (c : NatCert) (hp : Array (Array ℕ)) (r : ℕ) (w : List ℕ) (rp : Array ℕ)
    (c₃ : NatCert) (hw : pathWord c 280 r = w) (hrp : permArr c w = rp)
    (hc : natBfsL (repAct hp rp) 4 0 280 = c₃) (h : repLitOK c hp r w rp c₃ = true) :
    repOKL c hp r = true := by
  unfold repOKL
  unfold repLitOK at h
  simp only [hw, hrp, hc]
  exact h

end CFSG.KC.J2Max76
