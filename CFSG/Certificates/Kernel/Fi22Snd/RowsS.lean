module

public import Certificates.Data.Kernel.Fi22Nbr3153S
public import CFSG.Certificates.Kernel.Fi22Snd.RowsW

public section

namespace CFSG.KC.Fi22Snd

open CFSG.KC.Enum CFSG.KC.N3153

theorem maskFold_start (h : Nat → Nat) {f : Nat → Nat → Nat}
    (hf : ∀ i a, f i a = (a ||| 2 ^ (64 + h i)) + 1) {m c : Nat} (hc : c + m < 2 ^ 64) :
    foldN m f c >>> 64 = foldN m f 0 >>> 64 := by
  obtain ⟨B1, h1, h1'⟩ := maskFold_aux h hf m 0 c hc
  obtain ⟨B2, h2, h2'⟩ := maskFold_aux h hf m 0 0 (by omega)
  simp only [Nat.mul_zero, Nat.zero_add] at h1 h2
  rw [CFSG.KC.Pack.foldN_eq, CFSG.KC.Pack.foldN_eq, h1, h2, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.mul_add_div (by positivity), Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero, Nat.add_zero]
  apply Nat.eq_of_testBit_eq
  intro q
  rw [h1', h2']

theorem maskSK_eq {d c : Nat} (hc : c + d < 2 ^ 64) (r : Nat) :
    Nat.shiftRight (maskSK d r c) (nat_lit 64) = Nat.shiftRight (maskK d r) (nat_lit 64) :=
  maskFold_start (rg r) (f := fun i a => Nat.add (Nat.lor a
    (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (rg r i)))) (nat_lit 1))
    (fun i a => by
      change (a ||| 1 <<< (64 + rg r i)) + 1 = _
      rw [Nat.one_shiftLeft]) hc

theorem imgMaskSK_eq {d c : Nat} (hc : c + d < 2 ^ 64) (g r : Nat) :
    Nat.shiftRight (imgMaskSK d g r c) (nat_lit 64) =
      Nat.shiftRight (imgMaskK d g r) (nat_lit 64) :=
  maskFold_start (fun i => pg (nat_lit 12) (nat_lit 4095) g (rg r i))
    (f := fun i a => Nat.add (Nat.lor a (Nat.shiftLeft (nat_lit 1)
      (Nat.add (nat_lit 64) (pg (nat_lit 12) (nat_lit 4095) g (rg r i))))) (nat_lit 1))
    (fun i a => by
      change (a ||| 1 <<< (64 + pg 12 4095 g (rg r i))) + 1 = _
      rw [Nat.one_shiftLeft]) hc

theorem rowSalt_lt (x : Nat) : rowSalt x < 2 ^ 62 := by
  have : rowSalt x ≤ 4611686018427387903 := Nat.and_le_right
  omega

theorem rowOKW_of_S {n d x : Nat} {R M S D : Nat → Nat} (hd : d < 2 ^ 62)
    (h : rowOKS n d R M S D x = true) : rowOKW n d R M S D x = true := by
  have hc : rowSalt x + d < 2 ^ 64 := by
    have := rowSalt_lt x
    omega
  have e : rowOKS n d R M S D x = rowOKW n d R M S D x := by
    unfold rowOKS rowOKW
    simp only [maskSK_eq hc]
  rwa [e] at h

theorem imgOK_of_S {n d g x : Nat} {R M : Nat → Nat} (hd : d < 2 ^ 62)
    (h : imgOKS n d g R M x = true) : imgOK n d g R M x = true := by
  have hc : rowSalt x + d < 2 ^ 64 := by
    have := rowSalt_lt x
    omega
  have e : imgOKS n d g R M x = imgOK n d g R M x := by
    unfold imgOKS imgOK
    simp only [imgMaskSK_eq hc]
  rwa [e] at h

end CFSG.KC.Fi22Snd

end
