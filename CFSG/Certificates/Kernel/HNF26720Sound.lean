module

public import Certificates.Data.Kernel.HNF26720K
public import CFSG.Certificates.Kernel.HNLocalSound

public section

namespace CFSG.KS.HNF26720

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNF26720 CFSG.KS.HNLocal Matrix

variable {L H CM RM ONE LV HV : Nat}

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem ltr_cases (A B Bi : Nat) (l : Int) : ltr A B Bi l = A ∨ ltr A B Bi l = B ∨ ltr A B Bi l = Bi := by
  rcases l with n | n
  · have e : ltr A B Bi (Int.ofNat n) = Bool.rec (motive := fun _ => Nat) B A (Nat.beq n 1) := rfl
    rw [e]
    cases Nat.beq n 1
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · have e : ltr A B Bi (Int.negSucc n) = Bool.rec (motive := fun _ => Nat) Bi A (Nat.beq n 0) :=
      rfl
    rw [e]
    cases Nat.beq n 0
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

theorem ltr_one (A B Bi : Nat) : ltr A B Bi 1 = A := rfl

theorem ltr_two (A B Bi : Nat) : ltr A B Bi 2 = B := rfl

theorem ltr_neg_one (A B Bi : Nat) : ltr A B Bi (-1) = A := rfl

theorem ltr_neg_two (A B Bi : Nat) : ltr A B Bi (-2) = Bi := rfl

section Sound

variable (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
include hc

theorem mul_sound {X Y : Nat} (hX : Canon 5 133 13 X) (hY : Canon 5 133 13 Y) :
    Canon 5 133 13 (mulR 5 13 1729 133 9 L H CM RM X Y) ∧
      OM (mulR 5 13 1729 133 9 L H CM RM X Y) = OM X * OM Y :=
  mulR_sound hc hX hY

theorem wgo_sound {A B Bi : Nat} (hA : Canon 5 133 13 A) (hB : Canon 5 133 13 B)
    (hBi : Canon 5 133 13 Bi) :
    ∀ (w : List Int) (acc : Nat), Canon 5 133 13 acc →
      Canon 5 133 13 (wgo (mulR 5 13 1729 133 9 L H CM RM) A B Bi w acc) ∧
        OM (wgo (mulR 5 13 1729 133 9 L H CM RM) A B Bi w acc) =
          OM acc * (w.map fun l => OM (ltr A B Bi l)).prod
  | [], acc, h => ⟨h, by rw [List.map_nil, List.prod_nil, mul_one]; rfl⟩
  | l :: w, acc, h => by
    have hl : Canon 5 133 13 (ltr A B Bi l) := by
      rcases ltr_cases A B Bi l with e | e | e <;> rw [e] <;> assumption
    obtain ⟨h1, h2⟩ := mul_sound hc h hl
    have e : wgo (mulR 5 13 1729 133 9 L H CM RM) A B Bi (l :: w) acc =
        wgo (mulR 5 13 1729 133 9 L H CM RM) A B Bi w (mulR 5 13 1729 133 9 L H CM RM acc
          (ltr A B Bi l)) :=
      strictN_eq _ _
    obtain ⟨h3, h4⟩ := wgo_sound hA hB hBi w _ h1
    rw [e]
    exact ⟨h3, by rw [h4, h2, List.map_cons, List.prod_cons, mul_assoc]⟩

theorem wprod_sound {A B Bi : Nat} (hA : Canon 5 133 13 A) (hB : Canon 5 133 13 B)
    (hBi : Canon 5 133 13 Bi) (w : List Int) :
    Canon 5 133 13 (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w) ∧
      OM (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w) =
        (w.map fun l => OM (ltr A B Bi l)).prod := by
  obtain ⟨h1, h2⟩ := one_sound hc
  obtain ⟨h3, h4⟩ := wgo_sound hc hA hB hBi w ONE h1
  refine ⟨h3, ?_⟩
  unfold wprod
  rw [h4]
  change ordMat 5 133 13 1729 ONE * _ = _
  rw [h2, one_mul]

theorem diagR_sound {r : Nat} :
    OM (diagR ONE r) = diagonal fun i : Fin 133 => if i.val < r then (1 : ZMod 5) else 0 := by
  obtain ⟨h1, h2⟩ := one_sound hc
  have hr := (rows_sound (m := 0) (n := r) h1).2
  funext i j
  unfold diagR
  rw [hr i j, diagonal_apply]
  by_cases hi : i.val < r
  · rw [dif_pos ⟨hi, by omega⟩, if_pos hi]
    change ordMat 5 133 13 1729 ONE _ j = _
    rw [h2, one_apply]
    have e : (⟨0 + i.val, by omega⟩ : Fin 133) = i := Fin.ext (by simp)
    rw [e]
  · rw [dif_neg (fun h => hi h.1), if_neg hi]
    simp

theorem rank_diagR {r : Nat} (hr : r ≤ 133) : (OM (diagR ONE r)).rank = r := by
  rw [diagR_sound hc, rank_diagonal]
  have e : Fintype.card {i : Fin 133 // (if i.val < r then (1 : ZMod 5) else 0) ≠ 0} =
      Fintype.card {i : Fin 133 // i.val < r} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      by_cases h : i.val < r
      · simp [h]
      · simp [h])
  rw [e, Fintype.card_fin_lt_of_le hr]

theorem rk_sound {M P Q U V r : Nat} (hM : Canon 5 133 13 M)
    (h : rkOK (mulR 5 13 1729 133 9 L H CM RM) (validM 5 229957 L H) ONE M P Q U V r = true) :
    (OM M).rank = r := by
  unfold rkOK at h
  obtain ⟨hr, h⟩ := andB_true h
  obtain ⟨hP, h⟩ := andB_true h
  obtain ⟨hQ, h⟩ := andB_true h
  obtain ⟨hU, h⟩ := andB_true h
  obtain ⟨hV, h⟩ := andB_true h
  obtain ⟨h1, h2⟩ := andB_true h
  have hr' : r ≤ 133 := Nat.le_of_ble_eq_true hr
  have cP : Canon 5 133 13 P := validM_canon (d := 133) (S := 1729) hc hP
  have cQ : Canon 5 133 13 Q := validM_canon (d := 133) (S := 1729) hc hQ
  have cU : Canon 5 133 13 U := validM_canon (d := 133) (S := 1729) hc hU
  have cV : Canon 5 133 13 V := validM_canon (d := 133) (S := 1729) hc hV
  have cD : Canon 5 133 13 (diagR ONE r) := (rows_sound (m := 0) (n := r) (one_sound hc).1).1
  obtain ⟨cPM, ePM⟩ := mul_sound hc cP hM
  obtain ⟨-, ePMQ⟩ := mul_sound hc cPM cQ
  obtain ⟨cUD, eUD⟩ := mul_sound hc cU cD
  obtain ⟨-, eUDV⟩ := mul_sound hc cUD cV
  have hD := rank_diagR hc hr'
  apply le_antisymm
  · have e : OM M = OM U * OM (diagR ONE r) * OM V := by
      rw [← eUD, ← eUDV, Nat.eq_of_beq_eq_true h2]
    have h3 := rank_mul_le_left (OM U * OM (diagR ONE r)) (OM V)
    have h4 := rank_mul_le_right (OM U) (OM (diagR ONE r))
    rw [e]
    omega
  · have e : OM (diagR ONE r) = OM P * OM M * OM Q := by
      rw [← ePM, ← ePMQ, Nat.eq_of_beq_eq_true h1]
    rw [e] at hD
    have h3 := rank_mul_le_left (OM P * OM M) (OM Q)
    have h4 := rank_mul_le_right (OM P) (OM M)
    omega

theorem pair_sound {A B Bi : Nat} {PS QS US VS KS : Nat → Nat} {w : List Int} {k : Nat}
    (hA : Canon 5 133 13 A) (hB : Canon 5 133 13 B) (hBi : Canon 5 133 13 Bi)
    (h : pairOK (mulR 5 13 1729 133 9 L H CM RM) (validM 5 229957 L H) L H ONE A B Bi
      PS QS US VS KS w k = true) :
    (OM (xw (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w) - 1).rank = KS k ∧
      (OM (xw (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w) ^ 2 - 1).rank = KS (k + 1) := by
  have cX : Canon 5 133 13 (xw (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w) :=
    (wprod_sound hc hA hB hBi ((1 :: w) ++ (1 :: invW w))).1
  unfold pairOK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  rw [strictB_eq] at h2
  generalize xw (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w = X at cX h1 h2 ⊢
  obtain ⟨cS, eS⟩ := subOne_sound (X := X) hc cX
  obtain ⟨cXX, eXX⟩ := mul_sound hc cX cX
  obtain ⟨cS2, eS2⟩ := subOne_sound (X := mulR 5 13 1729 133 9 L H CM RM X X) hc cXX
  refine ⟨?_, ?_⟩
  · rw [← eS]
    exact rk_sound hc cS h1
  · rw [sq, ← eXX, ← eS2]
    exact rk_sound hc cS2 h2

theorem comm_sound {A B Bi : Nat} {w : List Int} (hA : Canon 5 133 13 A) (hB : Canon 5 133 13 B)
    (hBi : Canon 5 133 13 Bi)
    (h : commOK (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w = true) :
    ((1 :: w).map fun l => OM (ltr A B Bi l)).prod = ((w ++ [1]).map fun l => OM (ltr A B Bi l)).prod := by
  rw [← (wprod_sound hc hA hB hBi _).2, ← (wprod_sound hc hA hB hBi _).2]
  exact congrArg OM (Nat.eq_of_beq_eq_true h)

end Sound

end CFSG.KS.HNF26720

end
