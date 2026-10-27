module

public import CFSG.Certificates.Kernel.Spor.ChainFKGen

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS.CB CFSG.ONSchreier.Native

theorem memFull3_sound {n s : Nat} {S : Array (Array Nat)} {base g : Array Nat}
    {F FI : Nat → Nat → Nat} {B G LEN : Nat → Nat} {IDX : Nat → Nat → Nat} {Mr : Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat → Nat}
    (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hb : base.size = 3) (hB : ∀ k < 3, base[k]! = B k ∧ B k < n) (hg : ∀ y < n, g[y]! = G y)
    (hG : ∀ y < n, G y < n)
    (hidx : ∀ i < 3, idxOK F s B i (IDX i) (LEN i) = true)
    (hh : ∀ i < 3, cbHead n (Mr i) (B i) (PTS i) (PAR i) (LAB i) = true)
    (hp : ∀ i < 3, ∀ k < Mr i, cbPt n (Mr i) (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i))
      (PTS i) (POS i) (PAR i) (LAB i) k = true)
    (hz : ∀ i < 3, ∀ z < n, cbPos n (Mr i) (PTS i) (POS i) z = true)
    (hsift : siftFull3 n POS PAR LAB Mr (fun i => invX F FI (IDX i) (LEN i)) B G = true) :
    memFull n (cLevels n base (allSteps S (pinvs n S) base)) (allInvSteps S (pinvs n S) base) base
      g = true :=
  memFull3_gen hS hF hb hB hg hG hidx hh hp hz hsift

end CFSG.KS.CH

end
