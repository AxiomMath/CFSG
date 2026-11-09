module

public import Certificates.Data.Kernel.LocalQT.MulF3
public import CFSG.Certificates.Kernel.LocalQT.StepsF3Sound
import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KC.LQT.F3S

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KS.Ord CFSG.F3.Native CFSG.KS.F3L
open CFSG.KS.SporSch.LyM (andB_true' cfacts)
open CFSG.KC.LocalComp.Ops3Snd (mat3 mat3_mul)

theorem beq_of_mulF3 {c : Lay} (hc : c.ok = true) {K X A B : Nat}
    (h : mulF3 c K X A B = true) : Nat.beq X (c.mul A B) = true := by
  unfold mulF3 at h
  obtain ⟨hp, h⟩ := andB_true' h
  obtain ⟨hK, h⟩ := andB_true' h
  obtain ⟨hd, h⟩ := andB_true' h
  obtain ⟨hva, h⟩ := andB_true' h
  obtain ⟨hvb, h⟩ := andB_true' h
  obtain ⟨hvn, heq⟩ := andB_true' h
  have hp : c.p = 3 := Nat.eq_of_beq_eq_true hp
  have hK : c.d * c.d ≤ 2 ^ K := by
    have h' := Nat.le_of_ble_eq_true hK
    rw [sl_one] at h'
    exact h'
  have hd : 0 < c.d := Nat.le_of_ble_eq_true hd
  obtain ⟨-, hS, -, hpw⟩ := cfacts hc
  have hw : 2 ≤ c.w := by
    rw [hp] at hpw
    rcases Nat.lt_or_ge c.w 2 with h2 | h2
    · interval_cases hcw : c.w <;> simp at hpw
    · exact h2
  have hA : Canon c.p c.d c.w A := validM_canon hc hva
  have hB : Canon c.p c.d c.w B := validM_canon hc hvb
  have hN : Canon c.p c.d c.w X := validM_canon hc hvn
  unfold eqV at heq
  obtain ⟨h1, h2⟩ := andB_true' heq
  have hG := CFSG.KS.F3L.V.ext' (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)
  have hmul := mat3_mul c hc hp hA hB
  unfold mat3 at hmul
  rw [hS] at hmul
  rw [hp] at hA hB hN
  have m1 := toMat_gath hw hK hN
  rw [hG, ← mul_unlane hd, toMat_mul (unlane_size _ _) (rowsWF_gath hw hA) (rowsWF_gath hw hB),
    toMat_gath hw hK hA, toMat_gath hw hK hB, ← hmul.2] at m1
  have hc3 := hmul.1
  rw [hp] at hc3
  rw [canon_inj hN hc3 m1.symm, Nat.beq_refl]

end CFSG.KC.LQT.F3S

end
