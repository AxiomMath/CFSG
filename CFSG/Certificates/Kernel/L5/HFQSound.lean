module

public import Certificates.Data.Kernel.L5.HFQ
public import CFSG.Certificates.Kernel.L5.HFCSound
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Certificates.Kernel.L5Q

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.KC.Enum CFSG.KS CFSG.KS.PF
  CFSG.Certificates.Kernel.L5H CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF

private theorem strictB_q (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem linV_eq (a b c d i : Fin 16) :
    linV a.val b.val c.val d.val i.val = (linFun (a, b, c, d) i).val := by
  fin_cases i <;> rfl

theorem orF_eq (a b c d : Fin 16) : orF (linV a.val b.val c.val d.val) 16 =
    (List.finRange 16).foldl (fun acc i => acc ||| 2 ^ (linFun (a, b, c, d) i).val) 0 := by
  apply Nat.eq_of_testBit_eq
  intro e
  rw [testBit_permFold, Bool.eq_iff_iff, testBit_orF, List.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨⟨i, hi⟩, List.mem_finRange _, ?_⟩
    rw [decide_eq_true_iff, ← linV_eq]
    exact h
  · rintro ⟨i, -, h⟩
    rw [decide_eq_true_iff, ← linV_eq] at h
    exact ⟨i.val, i.isLt, h⟩

theorem permV_eq (a b c d : Fin 16) : permV a.val b.val c.val d.val = permN (linFun (a, b, c, d)) := by
  unfold permV permN
  rw [← orF_eq, Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

theorem mkPerm_apply {f : Fin 16 → Fin 16} (h : isPermChk f = true) (i : Fin 16) :
    mkPerm f i = f i := by
  unfold mkPerm
  rw [dif_pos h]
  rfl

theorem cvV_eq {a b c d : Fin 16} (h : permN (linFun (a, b, c, d)) = true) :
    cvV a.val b.val c.val d.val = cOf (mkPerm (linFun (a, b, c, d))) := by
  have hp : permV a.val b.val c.val d.val = true := by rw [permV_eq]; exact h
  have hc : isPermChk (linFun (a, b, c, d)) = true := by rw [isPermChk_eq]; exact h
  unfold cvV
  rw [dif_pos hp]
  apply Subtype.ext
  change pmk 16 5 (linV a.val b.val c.val d.val) =
    pmk 16 (wC 16) (fun i => if h : i < 16 then (mkPerm (linFun (a, b, c, d)) ⟨i, h⟩ : Nat) else 0)
  rw [wC16q]
  have hl : ∀ x < 16, linV a.val b.val c.val d.val x < 2 ^ 5 := fun x hx => by
    have := linV_eq a b c d ⟨x, hx⟩
    simp only at this
    rw [this]
    have := (linFun (a, b, c, d) ⟨x, hx⟩).isLt
    omega
  have hm : ∀ x < 16, (if h : x < 16 then (mkPerm (linFun (a, b, c, d)) ⟨x, h⟩ : Nat) else 0) <
      2 ^ 5 := fun x hx => by
    rw [dif_pos hx]
    have := (mkPerm (linFun (a, b, c, d)) ⟨x, hx⟩).isLt
    omega
  refine eq_of_fld (by norm_num) (fld_pmk (by norm_num) hl) (fld_congr (fld_pmk (by norm_num) hm) ?_)
  intro i
  by_cases hi : i < 16
  · rw [if_pos hi, if_pos hi, dif_pos hi, mkPerm_apply hc]
    exact (linV_eq a b c d ⟨i, hi⟩).symm
  · rw [if_neg hi, if_neg hi]

theorem rowQ_sound {g : Fin 16 → Fin 16 → Bool} {c : CV 16 → Bool} {k : Nat}
    (h : rowQ g c k = true) : allQ2RowC g c k = true := by
  unfold allQ2RowC
  rw [List.all_eq_true]
  intro a _
  rw [Bool.or_eq_true]
  by_cases hak : a.val / 4 = k
  · right
    unfold rowQ at h
    have h1 := CFSG.KS.PK.allN_iff.1 h (a.val % 4) (Nat.mod_lt _ (by decide))
    have ea : Nat.add (Nat.mul 4 k) (a.val % 4) = a.val := by
      change 4 * k + a.val % 4 = a.val
      omega
    rw [ea, strictB_q] at h1
    rw [List.all_eq_true]
    intro b _
    rw [Bool.or_eq_true]
    have h2 := CFSG.KS.PK.allN_iff.1 h1 b.val b.isLt
    have fa : f16 a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
    have fb : f16 b.val = b := Fin.ext (Nat.mod_eq_of_lt b.isLt)
    rw [fa, fb] at h2
    cases hg : g a b
    · left
      rfl
    · right
      rw [hg] at h2
      change allN 16 (fun c' => allN 16 fun d =>
        bIf(permV a.val b.val c' d, c (cvV a.val b.val c' d), true)) = true at h2
      rw [List.all_eq_true]
      intro c' _
      rw [List.all_eq_true]
      intro d _
      have h3 := CFSG.KS.PK.allN_iff.1 (CFSG.KS.PK.allN_iff.1 h2 c'.val c'.isLt) d.val d.isLt
      rw [Bool.or_eq_true]
      cases hpn : permN (linFun (a, b, c', d))
      · left
        rfl
      · right
        have hp : permV a.val b.val c'.val d.val = true := by rw [permV_eq]; exact hpn
        rw [hp] at h3
        rw [← cvV_eq hpn]
        exact h3
  · left
    simp [hak]

end CFSG.Certificates.Kernel.L5Q

end
