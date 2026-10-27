module

public import Certificates.Data.Kernel.AE6FWN
public import CFSG.Certificates.Kernel.AE6FSound
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.AE6FW

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.Sporadic.Schreier.Native CFSG.KS.PF

@[expose] def CommPt (x y i : Nat) : Prop :=
  pg 9 (mask 9) (x % 2 ^ (360 * 9)) (pg 9 (mask 9) (y % 2 ^ (360 * 9)) i) =
    pg 9 (mask 9) (y % 2 ^ (360 * 9)) (pg 9 (mask 9) (x % 2 ^ (360 * 9)) i)

theorem commAt_iff (m x y : Nat) : commAt m x y = true ↔ ∀ i < m, CommPt x y i := by
  unfold commAt CommPt
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.allN_iff]
  simp only [Nat.beq_eq]

set_option exponentiation.threshold 4096 in
theorem commN_iff (x y : Nat) : commN x y = true ↔ ∀ i < 360, CommPt x y i := by
  unfold commN CommPt
  rw [eqN, Nat.beq_eq, ← tabN_inj_iff (n := 360) (by decide) (by decide)]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [ap_tabN (by decide), ap_tabN (by decide), pg_mod hi, pg_mod hi, pmN, pmN,
    pg_pcomp (by decide) hi, pg_pcomp (by decide) hi, ← pg_mod (w := 9) (x := y) hi,
    ← pg_mod (w := 9) (x := x) hi]

theorem commF_eq (x y : Nat) : commF x y = commN x y := by
  unfold commF
  cases h : commN x y with
  | false => exact Bool.and_false _
  | true =>
    rw [Bool.and_true]
    exact (commAt_iff 8 x y).2 fun i hi => (commN_iff x y).1 h i (by omega)

theorem commT_tabN (x y : Nat) : commT 360 (tabN 360 9 x) (tabN 360 9 y) = commF x y := by
  unfold commT
  rw [commF_eq, compT_tabN' dims, compT_tabN' dims, tblEq_tabN' dims]
  rfl

section Frames

variable {α β γ : Type}

theorem all_congr' {l : List γ} {f g : γ → Bool} (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem all_and2 (l : List γ) (p q : γ → Bool) :
    (l.all fun x => p x && q x) = (l.all p && l.all q) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, List.all_cons, ih]
    cases p a <;> cases q a <;> simp

theorem framesG_mapS (f : γ → β) (ST : List γ) (K0 K1 K2 K3 : List α)
    (c0 c1 c2 c3 : β → α → Bool) (w0 w1 w2 w3 : α → Bool) :
    framesG (ST.map f) K0 K1 K2 K3 c0 c1 c2 c3 w0 w1 w2 w3 =
      framesG ST K0 K1 K2 K3 (fun T X => c0 (f T) X) (fun T X => c1 (f T) X)
        (fun T X => c2 (f T) X) (fun T X => c3 (f T) X) w0 w1 w2 w3 := by
  unfold framesG
  simp only [List.filter_map, List.length_map, Function.comp_def]

theorem framesG_mapK (g : γ → α) (ST : List β) (K0 K1 K2 K3 : List γ)
    (c0 c1 c2 c3 : β → α → Bool) (w0 w1 w2 w3 : α → Bool) :
    framesG ST (K0.map g) (K1.map g) (K2.map g) (K3.map g) c0 c1 c2 c3 w0 w1 w2 w3 =
      framesG ST K0 K1 K2 K3 (fun T i => c0 T (g i)) (fun T i => c1 T (g i))
        (fun T i => c2 T (g i)) (fun T i => c3 T (g i)) (fun i => w0 (g i)) (fun i => w1 (g i))
        (fun i => w2 (g i)) (fun i => w3 (g i)) := by
  unfold framesG
  simp only [List.all_map, Function.comp_def]

theorem framesG_congr {ST : List β} {K0 K1 K2 K3 : List α}
    {c0 c1 c2 c3 c0' c1' c2' c3' : β → α → Bool} {w0 w1 w2 w3 w0' w1' w2' w3' : α → Bool}
    (h0 : ∀ X ∈ K0, (fun T => c0 T X) = (fun T => c0' T X) ∧ w0 X = w0' X)
    (h1 : ∀ X ∈ K1, (fun T => c1 T X) = (fun T => c1' T X) ∧ w1 X = w1' X)
    (h2 : ∀ X ∈ K2, (fun T => c2 T X) = (fun T => c2' T X) ∧ w2 X = w2' X)
    (h3 : ∀ X ∈ K3, (fun T => c3 T X) = (fun T => c3' T X) ∧ w3 X = w3' X) :
    framesG ST K0 K1 K2 K3 c0 c1 c2 c3 w0 w1 w2 w3 =
      framesG ST K0 K1 K2 K3 c0' c1' c2' c3' w0' w1' w2' w3' := by
  unfold framesG
  refine all_congr' fun X0 m0 => ?_
  rw [(h0 X0 m0).1, (h0 X0 m0).2]
  refine all_congr' fun X1 m1 => ?_
  rw [(h1 X1 m1).1, (h1 X1 m1).2]
  refine all_congr' fun X2 m2 => ?_
  rw [(h2 X2 m2).1, (h2 X2 m2).2]
  refine all_congr' fun X3 m3 => ?_
  rw [(h3 X3 m3).1, (h3 X3 m3).2]

theorem testBit_bitsOf : ∀ (L : List Bool) (i : Nat), (bitsOf L).testBit i = L.getD i false
  | [], i => by simp [bitsOf]
  | b :: L, 0 => by
    rw [bitsOf, List.foldr_cons, Nat.testBit_bit_zero, List.getD_cons_zero]
  | b :: L, i + 1 => by
    rw [bitsOf, List.foldr_cons, Nat.testBit_bit_succ, List.getD_cons_succ, ← testBit_bitsOf L i]
    rfl

theorem getD_map_lt {L : List Nat} {i : Nat} (f : Nat → Bool) (hi : i < L.length) :
    (L.map f).getD i false = f (L.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

theorem range'_getD (A B C : List Nat) :
    (List.range' A.length B.length).map (fun i => (A ++ (B ++ C)).getD i 0) = B := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_map, List.getElem_range', List.getD_eq_getElem _ _ (by simp at h1 ⊢; omega),
    List.getElem_append_right (by omega), List.getElem_append_left (by simp at h1 ⊢; omega)]
  congr 1
  omega

theorem lt_of_mem_range' {s n i : Nat} (L : List Nat) (hL : s + n ≤ L.length)
    (h : i ∈ List.range' s n) : i < L.length := by
  rw [List.mem_range'_1] at h
  omega

end Frames

end CFSG.KC.AE6FW

end
