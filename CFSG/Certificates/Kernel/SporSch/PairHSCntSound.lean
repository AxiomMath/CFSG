module

public import Certificates.Data.Kernel.SporSch.PairHSCnt
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative

variable {n : Nat}

section Checks

variable {bs : List Nat} {H : Subgroup (Equiv.Perm (Fin n))}
  {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}
  (hT : TabChain n w kS 4 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base bs)
include hT

theorem scanHSAt_eq (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {X Z ZI : Nat → Nat}
    {z : Equiv.Perm (Fin n)} (hZ : RepF n Z z) (hZI : RepF n ZI z⁻¹) (hz : z ∈ H) {c i : Nat}
    (hV : i < c → nfValidK 4 LR (nfX 4 (X i)) = true)
    (hE : i < c → eltOf S base (nfX 4 (X i)) ∈ H) :
    scanHSAt w NR NL LT PT bs c X Z ZI i = if i < c ∧
      orderOf (eltOf S base (nfX 4 (X i)) * z) = 5 ∧
      orderOf (z * eltOf S base (nfX 4 (X i)) * z⁻¹ * eltOf S base (nfX 4 (X i))) = 5
      then 1 else 0 := by
  unfold scanHSAt
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
    have hp5 : Nat.Prime 5 := by norm_num
    have hA := ordPL_iff hH hbs h1 (H.mul_mem hEi hz) hp5
    have hB := ordPL_iff hH hbs h2
      (H.mul_mem (H.mul_mem (H.mul_mem hz hEi) (H.inv_mem hz)) hEi) hp5
    rw [nIf_and]
    simp only [hA, hB, hi, true_and]
  · rw [blt_false hi]
    simp only [hi, false_and, ite_false]

end Checks

end CFSG.KS.SporSch

end
