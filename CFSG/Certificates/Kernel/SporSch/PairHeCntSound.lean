module

public import Certificates.Data.Kernel.SporSch.PairHeCnt
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative

variable {n : Nat}

theorem listNot_iff (e : Nat → Bool) (ds : List Nat) :
    List.rec (motive := fun _ => Bool) true
      (fun d _ ih => Bool.rec (motive := fun _ => Bool) false ih
        (Bool.rec (motive := fun _ => Bool) true false (e d))) ds = true ↔
      ∀ d ∈ ds, e d ≠ true := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    change Bool.rec (motive := fun _ => Bool) false _ _ = true ↔ _
    rw [bAnd_iff, bNot_iff, ih, List.forall_mem_cons]

variable {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}

theorem ordDL_iff (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {f : Nat → Nat}
    {u : Equiv.Perm (Fin n)} (hf : RepF n f u) (hu : u ∈ H) {m : Nat} {ds : List Nat}
    (hm : 0 < m) (hds : ∀ q, q.Prime → q ∣ m → m / q ∈ ds) (hlt : ∀ d ∈ ds, 0 < d ∧ d < m) :
    ordDL bs f m ds = true ↔ orderOf u = m := by
  unfold ordDL
  rw [bAnd_iff, fixL_iff hH hbs (hf.powF m) (H.pow_mem hu m), listNot_iff]
  have hd : ∀ d ∈ ds, (eqOnL bs (powF f d) (fun x => x) ≠ true ↔ u ^ d ≠ 1) := fun d _ => by
    rw [Ne, fixL_iff hH hbs (hf.powF d) (H.pow_mem hu d)]
  constructor
  · rintro ⟨h1, h2⟩
    refine orderOf_eq_of_pow_and_pow_div_prime hm h1 fun q hq hqm => ?_
    have hq' := hds q hq hqm
    exact (hd _ hq').1 (h2 _ hq')
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one u, fun d hdm => (hd d hdm).2 ?_⟩
    exact pow_ne_one_of_lt_orderOf (hlt d hdm).1.ne' (h ▸ (hlt d hdm).2)

theorem ds6 : ∀ q, q.Prime → q ∣ 6 → 6 / q ∈ [3, 2] := by
  intro q hq hd
  have := Nat.le_of_dvd (by norm_num) hd
  interval_cases q <;> revert hq hd <;> decide

theorem ds12 : ∀ q, q.Prime → q ∣ 12 → 12 / q ∈ [6, 4] := by
  intro q hq hd
  have := Nat.le_of_dvd (by norm_num) hd
  interval_cases q <;> revert hq hd <;> decide

theorem ds15 : ∀ q, q.Prime → q ∣ 15 → 15 / q ∈ [5, 3] := by
  intro q hq hd
  have := Nat.le_of_dvd (by norm_num) hd
  interval_cases q <;> revert hq hd <;> decide

theorem nIf_and4 (a b c d : Bool) :
    Bool.rec (motive := fun _ => Nat) 0 1 (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false d c) b)
      a) = if a = true ∧ b = true ∧ c = true ∧ d = true then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

section Checks

variable {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}
  (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base bs)
include hT

noncomputable abbrev elt5 (S : Array (Array Nat)) (base : Array Nat) (F : Nat) :
    Equiv.Perm (Fin n) :=
  nfElt n S base (nfArr 5 F)

theorem nfPtT5 {F : Nat} (hF : nfValidK 5 LR F = true) :
    nfOK (rawLevels n S base) (nfArr 5 F) = true ∧
      RepF n (fun x => nfPtT w NR NL LT PT (nat_lit 5) F x) (elt5 S base F) :=
  nfPtT_sound hT hF

theorem scanHeAt_eq (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {X Z ZI : Nat → Nat}
    {z : Equiv.Perm (Fin n)} (hZ : RepF n Z z) (hZI : RepF n ZI z⁻¹) (hz : z ∈ H) {c i : Nat}
    (hV : i < c → nfValidK 5 LR (nfX 5 (X i)) = true)
    (hE : i < c → elt5 S base (nfX 5 (X i)) ∈ H) :
    scanHeAt w NR NL LT PT bs c X Z ZI i = if i < c ∧
      orderOf (elt5 S base (nfX 5 (X i)) * z) = 7 ∧
      orderOf (z * elt5 S base (nfX 5 (X i)) * z⁻¹ * elt5 S base (nfX 5 (X i))) = 6 ∧
      orderOf (z * elt5 S base (nfX 5 (X i)) * z) = 12 ∧
      orderOf (z * z * elt5 S base (nfX 5 (X i)) * z) = 15 then 1 else 0 := by
  unfold scanHeAt
  by_cases hi : i < c
  · rw [blt_true hi]
    change strictN (nfX 5 (X i)) _ = _
    rw [strictN_val]
    have hR := (nfPtT5 hT (hV hi)).2
    have hx := hE hi
    set x := elt5 (n := n) S base (nfX 5 (X i))
    have h1 : RepF n (fun b => nfPtT w NR NL LT PT (nat_lit 5) (nfX 5 (X i)) (Z b)) (x * z) :=
      hR.comp hZ
    have h2 : RepF n (fun b => Z (nfPtT w NR NL LT PT (nat_lit 5) (nfX 5 (X i))
        (ZI (nfPtT w NR NL LT PT (nat_lit 5) (nfX 5 (X i)) b)))) (z * x * z⁻¹ * x) :=
      (hZ.comp (hR.comp (hZI.comp hR))).congr (by simp only [mul_assoc])
    have h3 : RepF n (fun b => Z (nfPtT w NR NL LT PT (nat_lit 5) (nfX 5 (X i)) (Z b)))
        (z * x * z) := (hZ.comp (hR.comp hZ)).congr (by simp only [mul_assoc])
    have h4 : RepF n (fun b => Z (Z (nfPtT w NR NL LT PT (nat_lit 5) (nfX 5 (X i)) (Z b))))
        (z * z * x * z) := (hZ.comp (hZ.comp (hR.comp hZ))).congr (by simp only [mul_assoc])
    have hA := ordPL_iff hH hbs h1 (H.mul_mem hx hz) (by norm_num : Nat.Prime 7)
    have hB := ordDL_iff hH hbs h2
      (H.mul_mem (H.mul_mem (H.mul_mem hz hx) (H.inv_mem hz)) hx) (by norm_num) ds6
      (by simp)
    have hC := ordDL_iff hH hbs h3 (H.mul_mem (H.mul_mem hz hx) hz) (by norm_num) ds12
      (by simp)
    have hD := ordDL_iff hH hbs h4 (H.mul_mem (H.mul_mem (H.mul_mem hz hz) hx) hz)
      (by norm_num) ds15 (by simp)
    rw [nIf_and4]
    simp only [hA, hB, hC, hD, hi, true_and]
  · rw [blt_false hi]
    simp only [hi, false_and, ite_false]

theorem bind5_spec {F P : Nat} (hF : nfValidK 5 LR F = true)
    (h : ∀ x < n, bind5At n w NR NL LT PT F P x = true) :
    RepF n (pg w (mask w) P) (elt5 S base F) := by
  intro x hx
  have h1 := h x hx
  unfold bind5At at h1
  rw [blt_true hx] at h1
  rw [Nat.eq_of_beq_eq_true h1]
  exact (nfPtT5 hT hF).2 x hx

end Checks

end CFSG.KS.SporSch

end
