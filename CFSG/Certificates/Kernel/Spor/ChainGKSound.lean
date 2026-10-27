module

public import Certificates.Data.Kernel.Spor.ChainGK
public import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.ChainGKS

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS.CB CFSG.ONSchreier.Native

theorem fullChainG_sound {n m s nb chunks : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {W : Array (List Int)} {F FI : Nat → Nat → Nat} {B LEN : Nat → Nat} {IDX : Nat → Nat → Nat}
    {Mr : Nat → Nat} {PTS POS PAR LAB : Nat → Nat → Nat}
    (hS : S.size = s) (hWs : W.size = s) (hm : m ≤ s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hW : ∀ j, m ≤ j → j < s → (∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < n, F j x = W[j]!.foldr (CFSG.KS.TW.GZ F FI) x)
    (hb : base.size = nb) (hB : ∀ k < nb, base[k]! = B k ∧ B k < n)
    (hidx : ∀ i < nb, idxOK F s B i (IDX i) (LEN i) = true)
    (hh : ∀ i < nb, cbHead n (Mr i) (B i) (PTS i) (PAR i) (LAB i) = true)
    (hp : ∀ i < nb, ∀ k < Mr i, cbPt n (Mr i) (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i))
      (PTS i) (POS i) (PAR i) (LAB i) k = true)
    (hz : ∀ i < nb, ∀ z < n, cbPos n (Mr i) (PTS i) (POS i) z = true)
    (hsch : ∀ i < nb, ∀ h < Mr i, ∀ j < Nat.mul 2 (LEN i),
      schG n nb (fun i => stepX F FI (IDX i) (LEN i)) (fun i => invX F FI (IDX i) (LEN i)) PTS POS
        PAR LAB Mr B i h j = true)
    (hterm : termG n s nb F B = true) :
    fullChainOK n m S base W chunks = true ∧ cOrbitSizes n S base = (List.range nb).map Mr := by
  exact GKS.fullChainG_of_checks hS hWs hm hF hW hb hB hidx hh hp hz hsch hterm

end CFSG.KS.CH

end
