module

public import Certificates.Data.Kernel.Misc.PermM22
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.RankThree.Asc83Table.M22Data

public section

namespace CFSG.KC.Misc.M22

open Equiv CFSG.KC.Misc.Clos CFSG.KC.LQT CFSG.RankThree.Asc83Table.M22

theorem noBadK_sound {X Y : ℕ} {W : ℕ → ℕ} {Q : List ℕ} (hX : pcode x = X) (hY : pcode y = Y)
    (hW : ∀ k < 9, pcode (w k) = W k)
    (hQ : ∀ k < 9, ∀ l < 9, q8K Q k l = m22Q8.contains (k, l)) {g : Perm (Fin 22)}
    (h : noBadK X Y W Q (pcode g) = true) :
    ∀ k < 9, ∀ l < 9, g * x = w k * g → g * y = w l * g → m22Q8.contains (k, l) = true := by
  intro k hk l hl h1 h2
  have henc := pcode_enc (n := 22) (by norm_num)
  rw [noBadK, letB_eq, letB_eq] at h
  have hk' := impB_eq_true ((allN_iff _ _).1 h k hk) (by
    rw [← hX, ← hW k hk, ← henc.enc_mul, ← henc.enc_mul, h1]
    exact Nat.beq_refl _)
  have hl' := impB_eq_true ((allN_iff _ _).1 hk' l hl) (by
    rw [← hY, ← hW l hl, ← henc.enc_mul, ← henc.enc_mul, h2]
    exact Nat.beq_refl _)
  rwa [hQ k hk l hl] at hl'

end CFSG.KC.Misc.M22

end
