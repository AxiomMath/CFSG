module

public import Certificates.Data.Kernel.Hering2119K
public import CFSG.RankThree.PartTwo.Sec21.Hering2119KItems
public import CFSG.RankThree.PartTwo.Sec21.Hering2119KNormS
import all CFSG.RankThree.PartTwo.Sec21.Hering2119SShareK

public section

namespace CFSG.KC.H2119

open CFSG.RankThree.PartTwo.Sec21.Hering2119S Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mulK_eq (A B : M4C) : mulK A B = A.mul B := rfl

theorem mvK_eq (A : M4C) (v : V4C) : mvK A v = A.mv v := rfl

theorem omK_eq (x y : V4C) : omK x y = x.om y := rfl

theorem addK_eq (x y : V4C) : addK x y = x.add y := rfl

theorem smulK_eq (k : Nat) (x : V4C) : smulK k x = x.smul k := rfl

theorem oneK_eq : oneK = M4C.one := rfl

theorem nat_beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b := Nat.beq_eq_true_eq a b ▸ Iff.rfl

theorem eqM_iff {A B : M4C} : eqM A B = true ↔ A = B := by
  cases A
  cases B
  simp only [eqM, Bool.and_eq_true, nat_beq_iff, M4C.mk.injEq, and_assoc]

theorem eqV_iff {x y : V4C} : eqV x y = true ↔ x = y := by
  cases x
  cases y
  simp only [eqV, Bool.and_eq_true, nat_beq_iff, V4C.mk.injEq, and_assoc]

theorem eqP_iff {p q : M4C × M4C} : eqP p q = true ↔ p = q := by
  rw [eqP, Bool.and_eq_true, eqM_iff, eqM_iff, Prod.ext_iff]

theorem lineK_eq : ∀ j : Nat, lineK j = lineC j
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

theorem lineK_toV (j : Fin 4) : (lineK j.val).toV = lineVec j := by
  rw [lineK_eq, lineC_toV]

theorem blkXK_toM (c0 c1 c2 : F3) : (blkXK c0.val c1.val c2.val).toM = blkX c0 c1 c2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkXK, blkX, M4C.toM]

theorem F3.two_eq_neg_one : ((2 : Nat) : F3) = -1 := by decide

theorem blkTK_toM (d0 d1 d2 : F3) : (blkTK d0.val d1.val d2.val).toM = blkT d0 d1 d2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkTK, blkT, M4C.toM] <;> decide

theorem F3.neg_val : ∀ s : F3, ((Nat.mod (Nat.sub 3 s.val) 3 : Nat) : F3) = -s := by decide

theorem uP_toM (s0 s1 s2 : F3) :
    (uP s0.val s1.val s2.val).1.toM = umat s0 s1 s2 ∧
      (uP s0.val s1.val s2.val).2.toM = umat (-s0) (-s1) (-s2) := by
  refine ⟨?_, ?_⟩
  · rw [uP, uC_toM, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · change (uC (Nat.mod (Nat.sub 3 s0.val) 3) (Nat.mod (Nat.sub 3 s1.val) 3)
      (Nat.mod (Nat.sub 3 s2.val) 3)).toM = _
    rw [uC_toM]
    rw [F3.neg_val, F3.neg_val, F3.neg_val]

theorem conjP_toM (u n : M4C × M4C) :
    (conjP u n).1.toM = u.1.toM * n.1.toM * u.2.toM ∧
      (conjP u n).2.toM = u.1.toM * n.2.toM * u.2.toM := by
  simp only [conjP, mulK_eq, M4C.toM_mul, mul_assoc, and_self]

theorem conjP_valid (u n : M4C × M4C) : (conjP u n).1.Valid := by
  simp only [conjP, mulK_eq]
  exact M4C.valid_mul _ _

theorem all3_true {f : Nat → Bool} (h : all3 f = true) : ∀ n < 3, f n = true := by
  simp only [all3, Bool.and_eq_true] at h
  intro n hn
  interval_cases n
  · exact h.1.1
  · exact h.1.2
  · exact h.2

theorem allL_true {α : Type} {L : List α} {f : α → Bool} (h : allL L f = true) :
    ∀ x ∈ L, f x = true := by
  induction L with
  | nil => intro x hx; cases hx
  | cons y L ih =>
    have h' : (f y && allL L f) = true := h
    rw [Bool.and_eq_true] at h'
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h'.1
    · exact ih h'.2 x hx

theorem memM_true {X : M4C} {S : List M4C} (h : memM X S = true) : X ∈ S := by
  induction S with
  | nil => exact absurd h Bool.false_ne_true
  | cons Y S ih =>
    have h' : (eqM X Y || memM X S) = true := h
    rcases Bool.or_eq_true_iff.mp h' with h1 | h1
    · rw [eqM_iff.mp h1]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h1)

theorem memP_true {p : M4C × M4C} {N : List (M4C × M4C)} (h : memP p N = true) : p ∈ N := by
  induction N with
  | nil => exact absurd h Bool.false_ne_true
  | cons q N ih =>
    have h' : (eqP p q || memP p N) = true := h
    rcases Bool.or_eq_true_iff.mp h' with h1 | h1
    · rw [eqP_iff.mp h1]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h1)

theorem allNorm_true {a : V4C} {f : M4C × M4C → Bool} (h : allNorm a f = true)
    {c0 c1 c2 d0 d1 d2 : Nat} (hc0 : c0 < 3) (hc1 : c1 < 3) (hc2 : c2 < 3) (hd0 : d0 < 3)
    (hd1 : d1 < 3) (hd2 : d2 < 3) (hc : condK a c0 c1 c2 d0 d1 d2 = true) :
    f (blkXK c0 c1 c2, blkTK d0 d1 d2) = true := by
  have h6 := all3_true (all3_true (all3_true (all3_true (all3_true (all3_true h c0 hc0) c1 hc1)
    c2 hc2) d0 hd0) d1 hd1) d2 hd2
  simp only [hc, Bool.not_true, Bool.false_or] at h6
  exact h6

theorem F3.three_eq_zero : (3 : F3) = 0 := by decide

theorem quad_zero_of_item {a : V4} (ha : inA a) {c0 c1 c2 : F3} {T : M4}
    (hI : IsItem a (blkX c0 c1 c2) T) :
    c0 * a 0 * a 0 + 2 * c1 * a 0 * a 1 + c2 * a 1 * a 1 = 0 := by
  have ha0 : InF a (blkX c0 c1 c2) a := ⟨1, 0, by simp, by simp [omega4], by simp⟩
  obtain ⟨c, h, -, hh2, hh3⟩ := hI.presF a ha0
  have e2 := congrFun hh3 2
  have e3 := congrFun hh3 3
  simp [blkX, Matrix.mulVec, dotProduct, Fin.sum_univ_four, ha.1, ha.2] at e2 e3
  simp only [omega4, ha.1, ha.2] at hh2
  linear_combination hh2 + a 0 * e2 + a 1 * e3

theorem beq_mod_zero (n : Nat) : Nat.beq (Nat.mod n 3) 0 = true ↔ (n : F3) = 0 := by
  rw [nat_beq_iff, ← ZMod.natCast_mod n 3]
  have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  change n % 3 = 0 ↔ _
  generalize n % 3 = r at this ⊢
  interval_cases r <;> decide

theorem condK_true {a : V4C} {c0 c1 c2 d0 d1 d2 : F3} (hdet : c0 * c2 - c1 * c1 ≠ 0)
    (hq : c0 * (a.a : F3) * a.a + 2 * c1 * a.a * a.b + c2 * a.b * a.b = 0)
    (hd0 : d0 * (a.a : F3) + d1 * a.b = 0) (hd1 : d1 * (a.a : F3) + d2 * a.b = 0) :
    condK a c0.val c1.val c2.val d0.val d1.val d2.val = true := by
  simp only [condK, Bool.and_eq_true, Bool.not_eq_true', beq_mod_zero, Bool.eq_false_iff, ne_eq]
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  simp only [ZMod.natCast_zmod_val]
  refine ⟨⟨⟨fun h => hdet ?_, ?_⟩, ?_⟩, ?_⟩
  · linear_combination h - c1 * c1 * F3.three_eq_zero
  · linear_combination hq
  · linear_combination hd0
  · linear_combination hd1

theorem condK_of_item (j : Fin 4) {c0 c1 c2 d0 d1 d2 : F3}
    (hI : IsItem (lineVec j) (blkX c0 c1 c2) (blkT d0 d1 d2)) (hdet : c0 * c2 - c1 * c1 ≠ 0)
    (hd0 : d0 * lineVec j 0 + d1 * lineVec j 1 = 0)
    (hd1 : d1 * lineVec j 0 + d2 * lineVec j 1 = 0) :
    condK (lineK j.val) c0.val c1.val c2.val d0.val d1.val d2.val = true := by
  have hq := quad_zero_of_item (inA_lineVec j) hI
  have hv := lineK_toV j
  have e0 : lineVec j 0 = ((lineK j.val).a : F3) := by rw [← hv]; rfl
  have e1 : lineVec j 1 = ((lineK j.val).b : F3) := by rw [← hv]; rfl
  rw [e0, e1] at hq hd0 hd1
  exact condK_true hdet hq hd0 hd1

theorem mem_of_nOK {j : Fin 4} {N : List (M4C × M4C)} (hn : nOK (lineK j.val) N = true)
    {c0 c1 c2 d0 d1 d2 : F3} (hI : IsItem (lineVec j) (blkX c0 c1 c2) (blkT d0 d1 d2))
    (hdet : c0 * c2 - c1 * c1 ≠ 0) (hd0 : d0 * lineVec j 0 + d1 * lineVec j 1 = 0)
    (hd1 : d1 * lineVec j 0 + d2 * lineVec j 1 = 0) :
    (blkXK c0.val c1.val c2.val, blkTK d0.val d1.val d2.val) ∈ N :=
  memP_true (allNorm_true hn (ZMod.val_lt c0) (ZMod.val_lt c1) (ZMod.val_lt c2) (ZMod.val_lt d0)
    (ZMod.val_lt d1) (ZMod.val_lt d2) (condK_of_item j hI hdet hd0 hd1))

def Covers (F : (List (M4C × M4C) → Bool) → List (M4C × M4C) → Bool)
    (P : M4C × M4C → Prop) : Prop :=
  ∀ k L, F k L = true → (∀ x, P x → x ∈ L) ∧ ∃ L', L' ⊆ L ∧ k L' = true

theorem innerL_covers (u : M4C × M4C) (N : List (M4C × M4C)) :
    Covers (innerL u N) (fun x => ∃ n ∈ N, x = conjP u n) := by
  induction N with
  | nil =>
    intro k L h
    exact ⟨fun x ⟨n, hn, _⟩ => absurd hn List.not_mem_nil, L, List.Subset.refl _, h⟩
  | cons n N ih =>
    intro k L h
    cases L with
    | nil => exact absurd h Bool.false_ne_true
    | cons s L' =>
      have h' : (eqP s (conjP u n) && innerL u N k L') = true := h
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h'
      have hs := eqP_iff.mp h1
      obtain ⟨hP, L'', hsub, hk⟩ := ih k L' h2
      refine ⟨?_, L'', fun x hx => List.mem_cons_of_mem _ (hsub hx), hk⟩
      rintro x ⟨m, hm, rfl⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [← hs]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hP _ ⟨m, hm, rfl⟩)

theorem covers_comp {F G : (List (M4C × M4C) → Bool) → List (M4C × M4C) → Bool}
    {P Q : M4C × M4C → Prop} (hF : Covers F P) (hG : Covers G Q) :
    Covers (fun k => F (G k)) (fun x => P x ∨ Q x) := by
  intro k L h
  obtain ⟨hP, L', hsub, hk⟩ := hF (G k) L h
  obtain ⟨hQ, L'', hsub', hk'⟩ := hG k L' hk
  refine ⟨?_, L'', fun x hx => hsub (hsub' hx), hk'⟩
  rintro x (hx | hx)
  · exact hP x hx
  · exact hsub (hQ x hx)

theorem covers_seq3 {f : Nat → (List (M4C × M4C) → Bool) → List (M4C × M4C) → Bool}
    (P : Nat → M4C × M4C → Prop) (hf : ∀ i < 3, Covers (f i) (P i)) :
    Covers (seq3 f) (fun x => ∃ i < 3, P i x) := by
  intro k L h
  obtain ⟨hP, hk⟩ := covers_comp (hf 0 (by norm_num))
    (covers_comp (hf 1 (by norm_num)) (hf 2 (by norm_num))) k L h
  refine ⟨?_, hk⟩
  rintro x ⟨i, hi, hx⟩
  interval_cases i
  · exact hP x (Or.inl hx)
  · exact hP x (Or.inr (Or.inl hx))
  · exact hP x (Or.inr (Or.inr hx))

theorem mem_of_chkL {N L : List (M4C × M4C)} (h : chkL N L = true) :
    ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ n ∈ N, conjP (uP a b c) n ∈ L := by
  have hc := covers_seq3 (fun a x => ∃ b < 3, ∃ c < 3, ∃ n ∈ N, x = conjP (uP a b c) n)
    (fun a _ => covers_seq3 (fun b x => ∃ c < 3, ∃ n ∈ N, x = conjP (uP a b c) n)
      (fun b _ => covers_seq3 (fun c x => ∃ n ∈ N, x = conjP (uP a b c) n)
        (fun c _ => innerL_covers _ _)))
  intro a ha b hb c hc' n hn
  exact (hc isNilK L h).1 _ ⟨a, ha, b, hb, c, hc', n, hn, rfl⟩

theorem item_mem_L {j : Fin 4} {N L : List (M4C × M4C)} (hn : nOK (lineK j.val) N = true)
    (hl : chkL N L = true) {X T : M4} (hI : IsItem (lineVec j) X T) :
    ∃ s ∈ L, s.1.toM = X ∧ s.2.toM = T ∧ s.1.Valid := by
  obtain ⟨s0, s1, s2, c0, c1, c2, d0, d1, d2, hX, hT, hI', hdet, hd0, hd1⟩ :=
    item_normal_conj (inA_lineVec j) hI
  have hl' := mem_of_chkL hl _ (ZMod.val_lt s0) _ (ZMod.val_lt s1) _ (ZMod.val_lt s2) _
    (mem_of_nOK hn hI' hdet hd0 hd1)
  obtain ⟨u1, u2⟩ := uP_toM s0 s1 s2
  obtain ⟨p1, p2⟩ := conjP_toM (uP s0.val s1.val s2.val)
    (blkXK c0.val c1.val c2.val, blkTK d0.val d1.val d2.val)
  refine ⟨_, hl', ?_, ?_, conjP_valid _ _⟩
  · rw [p1, u1, u2, hX, blkXK_toM]
  · rw [p2, u1, u2, hT, blkTK_toM]

theorem perm_of_permOK {s1 s2 s3 : Nat} (h : permOK s1 s2 s3 = true) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = 0 ∧ (σ 1).val = s1 ∧ (σ 2).val = s2 ∧ (σ 3).val = s3 := by
  simp only [permOK, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    nat_beq_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, b1⟩, a2⟩, b2⟩, a3⟩, b3⟩, n12⟩, n13⟩, n23⟩ := h
  let f : Fin 4 → Fin 4 := ![0, ⟨s1, b1⟩, ⟨s2, b2⟩, ⟨s3, b3⟩]
  have hf : Function.Injective f := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp [f, Fin.ext_iff] at hxy ⊢ <;> omega
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), rfl, rfl, rfl, rfl⟩

theorem lineImg_sound {h : M4C} (i t : Fin 4) (hl : lineImg h i.val t.val = true) :
    ∃ ε : F3, ε * ε = 1 ∧ h.toM.mulVec (lineVec i) = ε • lineVec t := by
  simp only [lineImg, Bool.or_eq_true, eqV_iff, mvK_eq, smulK_eq] at hl
  rw [← lineK_toV i, ← M4C.toV_mv]
  rcases hl with hl | hl
  · exact ⟨1, by decide, by rw [hl, lineK_toV, one_smul]⟩
  · refine ⟨-1, by decide, ?_⟩
    rw [hl, V4C.toV_smul, lineK_toV, F3.two_eq_neg_one]

theorem symp_of_cols {Y : M4} {μ : F3}
    (h02 : omega4 (fun r => Y r 0) (fun r => Y r 2) = μ)
    (h13 : omega4 (fun r => Y r 1) (fun r => Y r 3) = μ)
    (h01 : omega4 (fun r => Y r 0) (fun r => Y r 1) = 0)
    (h03 : omega4 (fun r => Y r 0) (fun r => Y r 3) = 0)
    (h12 : omega4 (fun r => Y r 1) (fun r => Y r 2) = 0)
    (h23 : omega4 (fun r => Y r 2) (fun r => Y r 3) = 0) (x y : V4) :
    omega4 (Y *ᵥ x) (Y *ᵥ y) = μ * omega4 x y := by
  simp only [omega4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at *
  linear_combination (x 0 * y 2 - x 2 * y 0) * h02 + (x 1 * y 3 - x 3 * y 1) * h13 +
    (x 0 * y 1 - x 1 * y 0) * h01 + (x 0 * y 3 - x 3 * y 0) * h03 +
    (x 1 * y 2 - x 2 * y 1) * h12 + (x 2 * y 3 - x 3 * y 2) * h23

theorem colK_toV (h : M4C) (i : Fin 4) : (colK h i.val).toV = fun r => h.toM r i := by
  rw [← mulVec_ev, colK, mvK_eq, M4C.toV_mv]
  congr 1
  fin_cases i <;> (ext r; fin_cases r <;> first | decide | simp [V4C.toV, ev])

theorem simK_sound {h : M4C} {m : Nat} (hs : simK h m = true) (x y : V4) :
    omega4 (h.toM *ᵥ x) (h.toM *ᵥ y) = (m : F3) * omega4 x y := by
  simp only [simK, Bool.and_eq_true, nat_beq_iff] at hs
  obtain ⟨⟨⟨⟨⟨h02, h13⟩, h01⟩, h03⟩, h12⟩, h23⟩ := hs
  have f : ∀ i j : Fin 4, ∀ k : Nat, omK (colK h i.val) (colK h j.val) = k →
      omega4 (fun r => h.toM r i) (fun r => h.toM r j) = (k : F3) := by
    intro i j k hk
    rw [← colK_toV, ← colK_toV, ← V4C.om_spec, ← omK_eq, hk]
  have g01 := f 0 1 0 h01
  have g03 := f 0 3 0 h03
  have g12 := f 1 2 0 h12
  have g23 := f 2 3 0 h23
  rw [Nat.cast_zero] at g01 g03 g12 g23
  exact symp_of_cols (f 0 2 m h02) (f 1 3 m h13) g01 g03 g12 g23 x y

theorem conjOK_sound {R0 R1 : M4C × M4C} {e : ConjK} (h : conjOK R0 R1 e = true) :
    (∃ σ : Equiv.Perm (Fin 4), σ 0 = 0 ∧ NormElS e.h.toM e.h'.toM (e.m : F3) σ) ∧
      (conjP (e.h, e.h') (e.X, e.T) = R0 ∨ conjP (e.h, e.h') (e.X, e.T) = R1) := by
  simp only [conjOK, Bool.and_eq_true, Bool.or_eq_true, eqM_iff, nat_beq_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hmi, him⟩, hm⟩, hs⟩, hp⟩, l0⟩, l1⟩, l2⟩, l3⟩, hR⟩ := h
  obtain ⟨σ, hσ0, hσ1, hσ2, hσ3⟩ := perm_of_permOK hp
  refine ⟨⟨σ, hσ0, ?_, ?_, ?_, simK_sound hs, ?_⟩, ?_⟩
  · rw [← M4C.toM_mul, ← mulK_eq, hmi, oneK_eq, M4C.toM_one]
  · rw [← M4C.toM_mul, ← mulK_eq, him, oneK_eq, M4C.toM_one]
  · rcases hm with hm | hm <;> rw [hm] <;> decide
  · intro i
    fin_cases i
    · exact lineImg_sound 0 (σ 0) (by rw [hσ0]; exact l0)
    · exact lineImg_sound 1 (σ 1) (by rw [hσ1]; exact l1)
    · exact lineImg_sound 2 (σ 2) (by rw [hσ2]; exact l2)
    · exact lineImg_sound 3 (σ 3) (by rw [hσ3]; exact l3)
  · cases hb : Nat.beq e.r 0
    · rw [hb, eqP_iff] at hR
      exact Or.inr hR
    · rw [hb, eqP_iff] at hR
      exact Or.inl hR

theorem find_rec {p : M4C × M4C} {C : List ConjK}
    (h : List.rec (motive := fun _ => Bool) false (fun e _ ih => eqP p (e.X, e.T) || ih) C = true) :
    ∃ e ∈ C, p = (e.X, e.T) := by
  induction C with
  | nil => exact absurd h Bool.false_ne_true
  | cons e C ih =>
    rcases Bool.or_eq_true_iff.mp h with h1 | h1
    · exact ⟨e, List.mem_cons_self .., eqP_iff.mp h1⟩
    · obtain ⟨e', he', hp⟩ := ih h1
      exact ⟨e', List.mem_cons_of_mem _ he', hp⟩

theorem conj_cancel (h u' u B h' : M4) (hu : u' * u = 1) :
    h * u' * (u * B * u') * (u * h') = h * B * h' := by
  calc h * u' * (u * B * u') * (u * h') = h * (u' * u) * B * (u' * u) * h' := by
        simp only [mul_assoc]
    _ = h * B * h' := by rw [hu, mul_one, mul_one]

theorem exists_rep {R0 R1 : M4C × M4C} {C : List ConjK} (hc : conjsOK R0 R1 C = true)
    {X T : M4} (hI : IsItem (lineVec 0) X T) :
    ∃ g g' : M4, ∃ m : F3, ∃ σ : Equiv.Perm (Fin 4), σ 0 = 0 ∧ NormElS g g' m σ ∧
      ((g * X * g' = R0.1.toM ∧ g * T * g' = R0.2.toM ∧ R0.1.Valid) ∨
        (g * X * g' = R1.1.toM ∧ g * T * g' = R1.2.toM ∧ R1.1.Valid)) := by
  obtain ⟨s0, s1, s2, c0, c1, c2, d0, d1, d2, hX, hT, hI', hdet, hd0, hd1⟩ :=
    item_normal_conj (inA_lineVec 0) hI
  simp only [conjsOK, Bool.and_eq_true] at hc
  obtain ⟨hall, hnorm⟩ := hc
  have hmem := allNorm_true hnorm (ZMod.val_lt c0) (ZMod.val_lt c1) (ZMod.val_lt c2)
    (ZMod.val_lt d0) (ZMod.val_lt d1) (ZMod.val_lt d2) (condK_of_item 0 hI' hdet hd0 hd1)
  obtain ⟨e, he, hpe⟩ := find_rec hmem
  obtain ⟨⟨σ, hσ0, hN⟩, hR⟩ := conjOK_sound (allL_true hall e he)
  have hU := NormElS.ofNormEl (umat_normEl s0 s1 s2)
  refine ⟨_, _, _, _, ?_, hU.comp hN, ?_⟩
  · rw [Equiv.trans_apply, Equiv.Perm.one_apply, hσ0]
  obtain ⟨hpX, hpT⟩ := Prod.ext_iff.mp hpe
  dsimp only at hpX hpT
  obtain ⟨c1', c2'⟩ := conjP_toM (e.h, e.h') (e.X, e.T)
  have kX : e.h.toM * umat (-s0) (-s1) (-s2) * X * (umat s0 s1 s2 * e.h'.toM) =
      (conjP (e.h, e.h') (e.X, e.T)).1.toM := by
    rw [c1', hX, conj_cancel _ _ _ _ _ (umat_neg_mul s0 s1 s2)]
    dsimp only
    rw [← hpX, blkXK_toM]
  have kT : e.h.toM * umat (-s0) (-s1) (-s2) * T * (umat s0 s1 s2 * e.h'.toM) =
      (conjP (e.h, e.h') (e.X, e.T)).2.toM := by
    rw [c2', hT, conj_cancel _ _ _ _ _ (umat_neg_mul s0 s1 s2)]
    dsimp only
    rw [← hpT, blkTK_toM]
  have hv := conjP_valid (e.h, e.h') (e.X, e.T)
  rcases hR with hR | hR
  · rw [hR] at kX kT hv
    exact Or.inl ⟨kX, kT, hv⟩
  · rw [hR] at kX kT hv
    exact Or.inr ⟨kX, kT, hv⟩

theorem rowsK_true {X0 T0 : M4C} {a : V4C} {S : List M4C} {L : List (M4C × M4C)}
    {W : List RowK} (h : rowsK X0 T0 a S L W = true) :
    ∀ s ∈ L, ∃ r : RowK, rowK X0 T0 a S s r = true := by
  induction L generalizing W with
  | nil => intro s hs; cases hs
  | cons t L ih =>
    cases W with
    | nil => exact absurd h Bool.false_ne_true
    | cons r W' =>
      have h' : (rowK X0 T0 a S t r && rowsK X0 T0 a S L W') = true := h
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h'
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨r, h1⟩
      · exact ih h2 s hs

theorem wordK_valid (X0 T0 X T : M4C) : ∀ w : List Nat, (wordK X0 T0 X T w).Valid
  | [] => M4C.valid_one
  | _ :: _ => M4C.valid_mul _ _

theorem selK_cases (X0 T0 X T : M4C) (l : Nat) :
    selK X0 T0 X T l = X0 ∨ selK X0 T0 X T l = T0 ∨ selK X0 T0 X T l = X ∨
      selK X0 T0 X T l = T := by
  unfold selK
  cases Nat.beq l 0 <;> cases Nat.beq l 1 <;> cases Nat.beq l 2 <;> simp

theorem wordK_mem {Sg : Set M4} {X0 T0 X T : M4C} (h1 : X0.toM ∈ Submonoid.closure Sg)
    (h2 : T0.toM ∈ Submonoid.closure Sg) (h3 : X.toM ∈ Submonoid.closure Sg)
    (h4 : T.toM ∈ Submonoid.closure Sg) :
    ∀ w : List Nat, (wordK X0 T0 X T w).toM ∈ Submonoid.closure Sg
  | [] => by
    change oneK.toM ∈ _
    rw [oneK_eq, M4C.toM_one]
    exact Submonoid.one_mem _
  | l :: w => by
    change (mulK (selK X0 T0 X T l) (wordK X0 T0 X T w)).toM ∈ _
    rw [mulK_eq, M4C.toM_mul]
    refine Submonoid.mul_mem _ ?_ (wordK_mem h1 h2 h3 h4 w)
    rcases selK_cases X0 T0 X T l with e | e | e | e <;> rw [e] <;> assumption

theorem anzK_sound {v : V4C} (hv : v.Valid) (h : anzK v = true) : inA v.toV ∧ v.toV ≠ 0 := by
  simp only [anzK, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, nat_beq_iff,
    Bool.eq_false_iff, ne_eq] at h
  obtain ⟨⟨hc, hd⟩, hab⟩ := h
  refine ⟨⟨by simp [V4C.toV, hc], by simp [V4C.toV, hd]⟩, fun h0 => ?_⟩
  have h0a : (v.a : F3) = ((0 : Nat) : F3) := by simpa [V4C.toV] using congrFun h0 0
  have h0b : (v.b : F3) = ((0 : Nat) : F3) := by simpa [V4C.toV] using congrFun h0 1
  exact hab ⟨nat_eq_of_cast_eq hv.1 (by norm_num) h0a, nat_eq_of_cast_eq hv.2.1 (by norm_num) h0b⟩

theorem inFHK_sound {a : V4C} {X : M4C} {v : V4C} (hv : v.Valid) {c : Nat}
    (h : inFHK a X v (addK v (smulK (Nat.mul 2 c) a)) = true) :
    InF a.toV X.toM v.toV ∧ ¬ InH a.toV X.toM v.toV := by
  simp only [inFHK, Bool.and_eq_true, Bool.not_eq_true', nat_beq_iff] at h
  obtain ⟨⟨hf, ho⟩, hn⟩ := h
  have hhv : (addK v (smulK (Nat.mul 2 c) a)).Valid := V4C.valid_add _ _
  have hfix := (mv_eq_iff hhv).mp (by rw [← mvK_eq]; exact eqV_iff.mp hf)
  have hom := (om_eq_iff a _ (k := 0) (by norm_num)).mp (by rw [← omK_eq]; exact ho)
  refine ⟨⟨(c : F3), _, hfix, by simpa using hom, ?_⟩, ?_⟩
  · rw [addK_eq, smulK_eq, V4C.toV_add, V4C.toV_smul]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.mul_eq]
    push_cast
    linear_combination (-(c : F3) * a.toV i) * F3.three_eq_zero
  · rintro ⟨h1, h2⟩
    have e1 : fixK X v = true := eqV_iff.mpr (by rw [mvK_eq]; exact (mv_eq_iff hv).mpr h1)
    have e2 : Nat.beq (omK a v) 0 = true :=
      nat_beq_iff.mpr ((om_eq_iff a v (by norm_num)).mpr (by simpa using h2))
    rw [e1, e2] at hn
    exact absurd hn (by decide)

theorem mem_of_rowK {Y T : Fin 4 → M4} (hC : Compat Y T) {X0 T0 : M4C} (h0 : X0.toM = Y 0)
    (h0' : T0.toM = T 0) {j : Fin 4} {S : List M4C} {s : M4C × M4C} (hs : s.1.toM = Y j)
    (hs' : s.2.toM = T j) {r : RowK} (h : rowK X0 T0 (lineK j.val) S s r = true) : s.1 ∈ S := by
  unfold rowK at h
  cases ht : Nat.beq r.tag 3
  · rw [ht] at h
    exfalso
    have h' : violK X0 (lineK j.val) s.1 (wordK X0 T0 s.1 s.2 r.w) r = true := h
    simp only [violK, Bool.and_eq_true, Bool.not_eq_true'] at h'
    obtain ⟨⟨⟨hne, hcube⟩, hfix⟩, hbad⟩ := h'
    set k := wordK X0 T0 s.1 s.2 r.w with hk
    have hkv : k.Valid := wordK_valid _ _ _ _ _
    have hmem : ∀ l, Y l ∈ Submonoid.closure (Set.range Y ∪ Set.range T) ∧
        T l ∈ Submonoid.closure (Set.range Y ∪ Set.range T) := fun l =>
      ⟨Submonoid.subset_closure (Or.inl ⟨l, rfl⟩), Submonoid.subset_closure (Or.inr ⟨l, rfl⟩)⟩
    have hkc : k.toM ∈ Submonoid.closure (Set.range Y ∪ Set.range T) := by
      rw [hk]
      refine wordK_mem ?_ ?_ ?_ ?_ r.w
      · rw [h0]; exact (hmem 0).1
      · rw [h0']; exact (hmem 0).2
      · rw [hs]; exact (hmem j).1
      · rw [hs']; exact (hmem j).2
    have hk1 : k.toM ≠ 1 := by
      intro h1
      have := (toM_eq_one_iff hkv).mp h1
      rw [this, ← oneK_eq, (eqM_iff (A := oneK)).mpr rfl] at hne
      exact absurd hne (by decide)
    have hk3 : k.toM * k.toM * k.toM = 1 := by
      have := congrArg M4C.toM (eqM_iff.mp hcube)
      rw [mulK_eq, mulK_eq, M4C.toM_mul, M4C.toM_mul, oneK_eq, M4C.toM_one, ← mul_assoc] at this
      exact this
    have hfv := eqV_iff.mp hfix
    have hvv : r.v.Valid := by rw [← hfv, mvK_eq]; exact M4C.valid_mv _ _
    have hkf : k.toM *ᵥ r.v.toV = r.v.toV := (mv_eq_iff hvv).mp (by rw [← mvK_eq]; exact hfv)
    have hC' := hC k.toM hkc hk1 hk3
    cases h0t : Nat.beq r.tag 0
    · rw [h0t] at hbad
      cases h1t : Nat.beq r.tag 1
      · rw [h1t] at hbad
        obtain ⟨hF, hH⟩ := inFHK_sound hvv hbad
        rw [lineK_toV, hs] at hF hH
        exact hC' j _ (Or.inr ⟨hF, hH⟩) hkf
      · rw [h1t] at hbad
        obtain ⟨hF, hH⟩ := inFHK_sound hvv hbad
        have e0 : (⟨1, 0, 0, 0⟩ : V4C).toV = lineVec 0 := lineK_toV 0
        rw [e0, h0] at hF hH
        exact hC' 0 _ (Or.inr ⟨hF, hH⟩) hkf
    · rw [h0t] at hbad
      obtain ⟨hA, hne0⟩ := anzK_sound hvv hbad
      exact hC' 0 _ (Or.inl ⟨hA, hne0⟩) hkf
  · rw [ht] at h
    exact memM_true h

theorem eqM_eq (A B : M4C) : eqM A B = (A == B) := by
  rw [Bool.eq_iff_iff, eqM_iff, beq_iff_eq]

theorem fixK_eq (X : M4C) (v : V4C) : fixK X v = (X.mv v == v) := by
  rw [Bool.eq_iff_iff, fixK, eqV_iff, mvK_eq, beq_iff_eq]

theorem bEq_eq (x y : Bool) : bEq x y = (x == y) := by
  cases x <;> cases y <;> rfl

theorem sameCycK_eq (A B : M4C) : sameCycK A B = sameCyc A B := by
  rw [sameCycK, sameCyc, eqM_eq, eqM_eq, mulK_eq]

theorem all3_of {f : Nat → Bool} (h : ∀ n < 3, f n = true) : all3 f = true := by
  simp only [all3, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), Bool.and_self]

theorem allV_eq (f : V4C → Bool) : allV f = allVecs.all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true]
  constructor
  · intro h v hv
    obtain ⟨ha, hb, hc, hd⟩ := valid_of_mem_allVecs hv
    exact all3_true (all3_true (all3_true (all3_true h _ ha) _ hb) _ hc) _ hd
  · intro h
    exact all3_of fun a ha => all3_of fun b hb => all3_of fun c hc => all3_of fun d hd =>
      h _ (mem_allVecs_of_valid ⟨ha, hb, hc, hd⟩)

theorem conclR_eq (X0 X1 X2 X3 : M4C) : conclR X0 X1 X2 X3 = conclC X0 X1 X2 X3 := by
  simp only [conclR, conclC, allV_eq, fixK_eq, bEq_eq, sameCycK_eq]

theorem conclK_of_conclR {X : Fin 4 → M4} {A0 A1 A2 A3 : M4C} (h0 : A0.toM = X 0)
    (h1 : A1.toM = X 1) (h2 : A2.toM = X 2) (h3 : A3.toM = X 3) (hv0 : A0.Valid)
    (hv1 : A1.Valid) (hv2 : A2.Valid) (hv3 : A3.Valid) (h : conclR A0 A1 A2 A3 = true) :
    ConclK X := by
  have e : ∀ A : M4C, A.Valid → toCM A.toM = A := fun A hA =>
    M4C.toM_inj (valid_toCM _) hA (toM_toCM _)
  apply conclC_sound
  rw [← h0, ← h1, ← h2, ← h3, e A0 hv0, e A1 hv1, e A2 hv2, e A3 hv3, ← conclR_eq]
  exact h

theorem conclK_of_rep {N1 N2 N3 L1 L2 L3 : List (M4C × M4C)} {R : M4C × M4C}
    {W1 W2 W3 : List RowK} {S1 S2 S3 : List M4C}
    (hn1 : nOK (lineK 1) N1 = true) (hn2 : nOK (lineK 2) N2 = true)
    (hn3 : nOK (lineK 3) N3 = true) (hl1 : chkL N1 L1 = true) (hl2 : chkL N2 L2 = true)
    (hl3 : chkL N3 L3 = true) (hw1 : rowsK R.1 R.2 (lineK 1) S1 L1 W1 = true)
    (hw2 : rowsK R.1 R.2 (lineK 2) S2 L2 W2 = true) (hw3 : rowsK R.1 R.2 (lineK 3) S3 L3 W3 = true)
    (hk : conclAll R.1 S1 S2 S3 = true) {X T : Fin 4 → M4}
    (hI : ∀ i, IsItem (lineVec i) (X i) (T i)) (hC : Compat X T) (h0 : X 0 = R.1.toM)
    (h0' : T 0 = R.2.toM) (hR : R.1.Valid) : ConclK X := by
  obtain ⟨s1, hs1, e1, f1, v1⟩ := item_mem_L (j := 1) hn1 hl1 (hI 1)
  obtain ⟨s2, hs2, e2, f2, v2⟩ := item_mem_L (j := 2) hn2 hl2 (hI 2)
  obtain ⟨s3, hs3, e3, f3, v3⟩ := item_mem_L (j := 3) hn3 hl3 (hI 3)
  obtain ⟨r1, hr1⟩ := rowsK_true hw1 s1 hs1
  obtain ⟨r2, hr2⟩ := rowsK_true hw2 s2 hs2
  obtain ⟨r3, hr3⟩ := rowsK_true hw3 s3 hs3
  have m1 := mem_of_rowK hC h0.symm h0'.symm (j := 1) e1 f1 hr1
  have m2 := mem_of_rowK hC h0.symm h0'.symm (j := 2) e2 f2 hr2
  have m3 := mem_of_rowK hC h0.symm h0'.symm (j := 3) e3 f3 hr3
  exact conclK_of_conclR h0.symm e1 e2 e3 hR v1 v2 v3
    (allL_true (allL_true (allL_true hk _ m1) _ m2) _ m3)

theorem kfact_of_checks {N1 N2 N3 L1 L2 L3 : List (M4C × M4C)} {R0 R1 : M4C × M4C}
    {C : List ConjK} {W01 W02 W03 W11 W12 W13 : List RowK}
    {S01 S02 S03 S11 S12 S13 : List M4C}
    (hn1 : nOK (lineK 1) N1 = true) (hn2 : nOK (lineK 2) N2 = true)
    (hn3 : nOK (lineK 3) N3 = true) (hl1 : chkL N1 L1 = true) (hl2 : chkL N2 L2 = true)
    (hl3 : chkL N3 L3 = true) (hc : conjsOK R0 R1 C = true)
    (hw01 : rowsK R0.1 R0.2 (lineK 1) S01 L1 W01 = true)
    (hw02 : rowsK R0.1 R0.2 (lineK 2) S02 L2 W02 = true)
    (hw03 : rowsK R0.1 R0.2 (lineK 3) S03 L3 W03 = true)
    (hw11 : rowsK R1.1 R1.2 (lineK 1) S11 L1 W11 = true)
    (hw12 : rowsK R1.1 R1.2 (lineK 2) S12 L2 W12 = true)
    (hw13 : rowsK R1.1 R1.2 (lineK 3) S13 L3 W13 = true)
    (hk0 : conclAll R0.1 S01 S02 S03 = true) (hk1 : conclAll R1.1 S11 S12 S13 = true) :
    Item2119EndShareK := by
  intro X T hI hC
  obtain ⟨g, g', m, σ, hσ0, hN, hrep⟩ := exists_rep hc (hI 0)
  have hI' := hN.isItems hI
  have hC' := hN.compat hC
  have hs0 : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, hσ0]
  apply hN.conclK
  rcases hrep with ⟨hx, ht, hv⟩ | ⟨hx, ht, hv⟩
  · exact conclK_of_rep hn1 hn2 hn3 hl1 hl2 hl3 hw01 hw02 hw03 hk0 hI' hC'
      (by simp only [hs0]; exact hx) (by simp only [hs0]; exact ht) hv
  · exact conclK_of_rep hn1 hn2 hn3 hl1 hl2 hl3 hw11 hw12 hw13 hk1 hI' hC'
      (by simp only [hs0]; exact hx) (by simp only [hs0]; exact ht) hv

end CFSG.KC.H2119
