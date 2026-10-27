module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Weyl

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem linearFrame (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (hn : 4 ≤ n) :
    ToralFrame K (longRootSet (K := K) (by omega : 2 ≤ n)) (signGroup K n) (coordSet K n) ∧
      sigmaSet K (longRootSet (K := K) (by omega : 2 ≤ n)) (signGroup K n) = coordSet K n ∧
      (coordSet K n).ncard = n.choose 2 ∧
      A2Dichotomy (signGroup K n) (coordSet K n) ∧
      NonCommConnected (coordSet K n) ∧
      FibreLE2 (coordSet K n) ∧
      Nonempty (weylGraph n ≃g commGraph (coordSet K n)) ∧
      Nonempty (swapGraph n ≃g commGraph (coordSet K n)) := by
  have h2 := two_ne_zero_of_odd_natCard hodd
  have hF := isPairFamily_Lc (K := K) (n := n) h2 (by omega)
  exact ⟨toralFrame hodd h5 hn, (coordSet_eq_sigmaSet h2 (by omega)).symm,
    ncard_coordSet hodd (by omega), a2Dichotomy_coordSet hodd h5 hn,
    nonCommConnected_coordSet hodd (by omega), fibreLE2_coordSet hodd (by omega),
    ⟨hF.iso⟩, ⟨(swapGraphIso n).trans hF.iso⟩⟩

end CFSG.ClassicalInvolution.Models
