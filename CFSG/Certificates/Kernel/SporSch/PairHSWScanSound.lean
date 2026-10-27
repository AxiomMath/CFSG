module

public import Certificates.Data.Kernel.SporSch.PairHSWScan
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier

variable {n : Nat} {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}

theorem ord10L_iff (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {f : Nat → Nat}
    {u : Equiv.Perm (Fin n)} (hf : RepF n f u) (hu : u ∈ H) :
    ord10L bs f = true ↔ orderOf u = 10 := by
  unfold ord10L
  rw [bAnd_iff, bAnd_iff, fixL_iff hH hbs (hf.powF 10) (H.pow_mem hu 10), bNot_iff, bNot_iff, Ne,
    Ne, fixL_iff hH hbs (hf.powF 5) (H.pow_mem hu 5), fixL_iff hH hbs (hf.powF 2) (H.pow_mem hu 2)]
  constructor
  · rintro ⟨h10, h5, h2⟩
    have hm : orderOf u ∈ Nat.divisors 10 :=
      Nat.mem_divisors.2 ⟨orderOf_dvd_of_pow_eq_one h10, by norm_num⟩
    have e : Nat.divisors 10 = {1, 2, 5, 10} := by decide
    rw [e] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [h]; norm_num)) h2
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [h])) h2
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [h])) h5
    · exact h
  · intro h
    exact ⟨h ▸ pow_orderOf_eq_one u, pow_ne_one_of_lt_orderOf (by norm_num) (by omega),
      pow_ne_one_of_lt_orderOf (by norm_num) (by omega)⟩

theorem nIf_and3 (a b c : Bool) :
    Bool.rec (motive := fun _ => Nat) 0 1 (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false c b) a) =
      if a = true ∧ b = true ∧ c = true then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> rfl

section Checks

variable {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}
  (hT : TabChain n w kS 4 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base bs)
include hT

theorem scanWAt_eq (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {X Z ZI : Nat → Nat}
    {z : Equiv.Perm (Fin n)} (hZ : RepF n Z z) (hZI : RepF n ZI z⁻¹) (hz : z ∈ H) {c i : Nat}
    (hV : i < c → nfValidK 4 LR (nfX 4 (X i)) = true)
    (hE : i < c → eltOf S base (nfX 4 (X i)) ∈ H) :
    scanWAt w NR NL LT PT bs c X Z ZI i = if i < c ∧
      orderOf (eltOf S base (nfX 4 (X i)) * z) = 5 ∧
      orderOf (z * eltOf S base (nfX 4 (X i)) * z⁻¹ * eltOf S base (nfX 4 (X i))) = 5 ∧
      orderOf (z * eltOf S base (nfX 4 (X i)) * z) = 10 then 1 else 0 := by
  unfold scanWAt
  by_cases hi : i < c
  · rw [blt_true hi]
    change strictN (nfX 4 (X i)) _ = _
    rw [strictN_val]
    have hR := (nfPtT4 hT (hV hi)).2
    have hEi := hE hi
    have h1 : RepF n (fun b => nfPtT w NR NL LT PT (nat_lit 4) (nfX 4 (X i)) (Z b))
        (eltOf S base (nfX 4 (X i)) * z) := hR.comp hZ
    have h2 : RepF n (fun b => Z (nfPtT w NR NL LT PT (nat_lit 4) (nfX 4 (X i))
        (ZI (nfPtT w NR NL LT PT (nat_lit 4) (nfX 4 (X i)) b))))
        (z * eltOf S base (nfX 4 (X i)) * z⁻¹ * eltOf S base (nfX 4 (X i))) :=
      (hZ.comp (hR.comp (hZI.comp hR))).congr (by simp only [mul_assoc])
    have h3 : RepF n (fun b => Z (nfPtT w NR NL LT PT (nat_lit 4) (nfX 4 (X i)) (Z b)))
        (z * eltOf S base (nfX 4 (X i)) * z) :=
      (hZ.comp h1).congr (by simp only [mul_assoc])
    have hp5 : Nat.Prime 5 := by norm_num
    have hA := ordPL_iff hH hbs h1 (H.mul_mem hEi hz) hp5
    have hB := ordPL_iff hH hbs h2
      (H.mul_mem (H.mul_mem (H.mul_mem hz hEi) (H.inv_mem hz)) hEi) hp5
    have hC := ord10L_iff hH hbs h3 (H.mul_mem (H.mul_mem hz hEi) hz)
    rw [nIf_and3]
    simp only [hA, hB, hC, hi, true_and]
  · rw [blt_false hi]
    simp only [hi, false_and, ite_false]

end Checks

end CFSG.KS.SporSch

end
