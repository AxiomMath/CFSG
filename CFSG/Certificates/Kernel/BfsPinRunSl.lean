module

public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

variable {n w : Nat}

theorem canonSl_of_runSl {ng N L K : Nat} {G T E C : Nat → Nat} (hN : N = L * K)
    (hsz : szOK n w = true) (hG : allN ng (fun k => canonK n w (mask w) (Nat.mul n w) (G k)) = true)
    (h0 : Nat.beq (T 0) (pidn n w) = true) (hC0 : C 0 = 1) (hCK : C K = N)
    (hr : ∀ s < K, runSl n w ng G T E L C s = true) : ∀ s < K, canonSl n w T L s = true := by
  intro s hs
  have hR : runF n w (mask w) ng G T E N 0 1 = N := by
    have h := runF_blocks L C K hr
    rw [hC0, hCK, ← hN] at h
    exact h
  have hLs : ∀ i < L, L * s + i < N := fun i hi => by
    have h1 : L * (s + 1) ≤ L * K := Nat.mul_le_mul_left L hs
    rw [Nat.mul_succ] at h1
    omega
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h
      have e1 : runF n w (mask w) ng G T E 0 0 1 = 1 := rfl
      rw [hN, Nat.zero_mul, e1] at hR
      exact absurd hR (by decide)
    · exact h
  have hN0 : N ≠ 0 := by
    have := hLs 0 hL
    omega
  have hc1 : ∀ j < 1, canonK n w (mask w) (n * w) (T j) = true := by
    intro j hj
    have e : j = 0 := by omega
    rw [e, Nat.eq_of_beq_eq_true h0]
    exact (PP.id hsz).1
  obtain ⟨-, hQN, -⟩ := runF_spec (fun y => canonK n w (mask w) (n * w) y = true)
    (fun y hy k hk => canonK_pcomp (allN_spec hG k hk) hy) N 0 1 N hR hN0 hc1
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  unfold canonSl
  exact allN_of_forall fun i hi => hQN _ (hLs i hi)

theorem bfsK_of_runSl {ng N L K : Nat} {G T E S C : Nat → Nat} (hN : N = L * K) (hL : 0 < L)
    (hsz : szOK n w = true)
    (hG : allN ng (fun k => canonK n w (mask w) (Nat.mul n w) (G k)) = true)
    (h0 : Nat.beq (T 0) (pidn n w) = true)
    (hD : distinctK N T S = true) (hC0 : C 0 = 1) (hCK : C K = N)
    (hr : ∀ s < K, runSl n w ng G T E L C s = true) :
    bfsK n w ng G N T E S = true :=
  bfsK_of_slices hN hL hsz hG (canonSl_of_runSl hN hsz hG h0 hC0 hCK hr) h0 hD hC0 hCK hr

end CFSG.KC.BfsPin

end
