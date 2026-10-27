module

public import Certificates.Data.Kernel.BfsPinSlice
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

@[expose] noncomputable def runRec (n w m ng : Nat) (G T E : Nat → Nat) (N r : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (nIf(Nat.blt (Nat.sub (Nat.sub N r) (nat_lit 1)) c,
      pointStep n w m ng G T E (Nat.sub (Nat.sub N r) (nat_lit 1)) c, nat_lit 0)) ih) r

theorem runRec_succ {n w m ng : Nat} {G T E : Nat → Nat} (N r c : Nat) :
    runRec n w m ng G T E N (r + 1) c =
      runRec n w m ng G T E N r (nIf(Nat.blt (Nat.sub (Nat.sub N r) (nat_lit 1)) c,
        pointStep n w m ng G T E (Nat.sub (Nat.sub N r) (nat_lit 1)) c, nat_lit 0)) :=
  strictN_app _ _

theorem runF_succ {n w m ng : Nat} {G T E : Nat → Nat} (len lo c : Nat) :
    runF n w m ng G T E (len + 1) lo c =
      runF n w m ng G T E len (Nat.succ lo) (nIf(Nat.blt lo c, pointStep n w m ng G T E lo c,
        nat_lit 0)) :=
  strictN_app _ _

theorem runK_rec {n w m ng : Nat} {G T E : Nat → Nat} (N : Nat) : ∀ r, r ≤ N → ∀ c,
    runRec n w m ng G T E N r c = runF n w m ng G T E r (N - r) c
  | 0, _, _ => rfl
  | r + 1, h, c => by
    have e1 : Nat.sub (Nat.sub N r) (nat_lit 1) = N - (r + 1) := by
      change N - r - 1 = N - (r + 1)
      omega
    have e2 : Nat.succ (N - (r + 1)) = N - r := by omega
    rw [runRec_succ, runF_succ, e1, e2, runK_rec N r (by omega)]

theorem runK_eq {n w m ng : Nat} {G T E : Nat → Nat} (N : Nat) :
    runK n w m ng G T E N = runF n w m ng G T E N 0 1 := by
  have h := runK_rec (n := n) (w := w) (m := m) (ng := ng) (G := G) (T := T) (E := E) N N
    (Nat.le_refl N) 1
  rw [Nat.sub_self] at h
  exact h

theorem runF_add {n w m ng : Nat} {G T E : Nat → Nat} : ∀ (a b lo c : Nat),
    runF n w m ng G T E (a + b) lo c = runF n w m ng G T E b (lo + a) (runF n w m ng G T E a lo c)
  | 0, b, lo, c => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | a + 1, b, lo, c => by
    have e : Nat.succ lo + a = lo + (a + 1) := by omega
    rw [Nat.add_right_comm, runF_succ, runF_succ, runF_add a b (Nat.succ lo), e]

theorem runF_blocks {n w ng : Nat} {G T E : Nat → Nat} (L : Nat) (C : Nat → Nat) : ∀ K,
    (∀ s < K, runSl n w ng G T E L C s = true) →
      runF n w (mask w) ng G T E (L * K) 0 (C 0) = C K
  | 0, _ => rfl
  | K + 1, h => by
    rw [Nat.mul_succ, runF_add, runF_blocks L C K (fun s hs => h s (by omega)), Nat.zero_add]
    exact Nat.eq_of_beq_eq_true (h K (by omega))

theorem bfsK_of_slices {n w ng N L K : Nat} {G T E S C : Nat → Nat} (hN : N = L * K) (hL : 0 < L)
    (hsz : szOK n w = true)
    (hG : allN ng (fun k => canonK n w (mask w) (Nat.mul n w) (G k)) = true)
    (hc : ∀ s < K, canonSl n w T L s = true) (h0 : Nat.beq (T 0) (pidn n w) = true)
    (hD : distinctK N T S = true) (hC0 : C 0 = 1) (hCK : C K = N)
    (hr : ∀ s < K, runSl n w ng G T E L C s = true) :
    bfsK n w ng G N T E S = true := by
  have hT : ∀ i < N, canonK n w (mask w) (Nat.mul n w) (T i) = true := by
    intro i hi
    rw [hN] at hi
    have hs : i / L < K := (Nat.div_lt_iff_lt_mul hL).2 (by rwa [Nat.mul_comm] at hi)
    have h1 := hc (i / L) hs
    unfold canonSl at h1
    have h2 := allN_spec h1 (i % L) (Nat.mod_lt _ hL)
    have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
    rwa [e] at h2
  have hR : runK n w (mask w) ng G T E N = N := by
    have h := runF_blocks L C K hr
    rw [hC0, hCK, ← hN] at h
    rw [runK_eq]
    exact h
  unfold bfsK
  rw [hsz, hG, allN_of_forall hT, h0, hD, hR, Nat.beq_refl]

end CFSG.KC.BfsPin

end
