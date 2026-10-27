module

public import Certificates.Data.Kernel.D4K
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.KC.D4K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum

theorem siftOK_parts {n w nb BP G : Nat} {LR TRI : Nat → Nat}
    (h : siftOK n w LR TRI BP nb G = true) :
    Nat.beq (Nat.shiftRight G (n * w)) 0 = true ∧
      allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G = true := by
  unfold siftOK at h
  cases h1 : Nat.beq (Nat.shiftRight G (n * w)) 0 <;> rw [h1] at h
  · exact absurd (h : false = true) Bool.false_ne_true
  cases h2 : allN n (fun i => Nat.blt (pg w (mask w) G i) n) <;> rw [h2] at h
  · exact absurd (h : false = true) Bool.false_ne_true
  exact ⟨rfl, rfl, h⟩

theorem allBlk_true {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, allBlk b f len = true →
    ∀ l < len, f (b + l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
      at h
    cases h1 : f (Nat.add b len) <;> rw [h1] at h
    · exact absurd (h : false = true) Bool.false_ne_true
    rcases Nat.lt_or_ge l len with h2 | h2
    · exact allBlk_true h l h2
    · have e : l = len := by omega
      subst e
      exact h1

theorem forall_of_slices {L K : Nat} {f : Nat → Bool} (hL : 0 < L)
    (h : ∀ s < K, allBlk (Nat.mul L s) f L = true) : ∀ i < L * K, f i = true := by
  intro i hi
  have hs : i / L < K := (Nat.div_lt_iff_lt_mul hL).2 (by rwa [Nat.mul_comm] at hi)
  have := allBlk_true (h (i / L) hs) (i % L) (Nat.mod_lt _ hL)
  have e : Nat.mul L (i / L) + i % L = i := Nat.div_add_mod i L
  rwa [e] at this

theorem allN_of_slices {L K : Nat} {f : Nat → Bool} (hL : 0 < L)
    (h : ∀ s < K, allBlk (Nat.mul L s) f L = true) : allN (L * K) f = true :=
  Orb.allN_iff.2 (forall_of_slices hL h)

theorem permB_pts {n w ng N : Nat} {G T E S : Nat → Nat}
    (hk : CFSG.KC.BfsPin.bfsK n w ng G N T E S = true)
    (hp : ∀ k < ng, CFSG.KC.Misc.ArrEnum.permB n w (G k) = true) :
    ∀ i < N, CFSG.KC.Misc.ArrEnum.permB n w (T i) = true := fun i hi =>
  CFSG.KC.Misc.ArrEnum.permB_of_pp (CFSG.KC.BfsPin.PP_pts hk (fun k hk' => hp k hk') i hi)

theorem linesK_of {n w p N r : Nat} {T LX : Nat → Nat}
    (h1 : ∀ k < N, lineAt n w p r T LX k = true)
    (h2 : allN r (fun j => permB n w (LX j) && Nat.beq (pw n w (LX j) p) (pidn n w)) = true) :
    linesK n w p N r T LX = true := by
  unfold linesK
  rw [Bool.and_eq_true]
  exact ⟨Orb.allN_iff.2 h1, h2⟩

end CFSG.KC.D4K

end
