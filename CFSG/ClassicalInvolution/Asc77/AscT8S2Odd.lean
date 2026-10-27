module

public import CFSG.ClassicalInvolution.Asc77.AscE184Quot
public import CFSG.ClassicalInvolution.Asc77.AscT8Min
import CFSG.ClassicalInvolution.Asc77.AscT8S2OddEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace T8S2

section Odd

variable {H : Type} [Group H] [Finite H] {p f : ℕ} [Fact p.Prime]

theorem omegaNbr_map_odd (hp : p ≠ 2) {Λ : Set (Subgroup H)} (hΛ : HypOmegaMod p f Λ)
    {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) {K J : Subgroup H}
    (hJ : J ∈ omegaNbr Λ K)
    (hne : J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N)) :
    J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Λ N) (K.map (QuotientGroup.mk' N)) := by
  exact omegaNbr_map_oddE (fun hL hR hRL => hΛ.isSylow2In_of_mem_RSet_of_le hp hL hR hRL) hN hJ
    hne

theorem map_ne_of_noTwins (hp : p ≠ 2) {Λ : Set (Subgroup H)} (hΛ : HypOmegaMod p f Λ)
    {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) {K J : Subgroup H} {z t : H}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hJ : J ∈ omegaNbr Λ K)
    (hnt : J ∈ twinSet Λ K → J = K) :
    J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) := by
  exact map_ne_of_noTwinsE hN hz ht hJ (T8.mul_comm_of_mem_omegaNbr hp hΛ hz hJ ht) hnt

end Odd

end T8S2

end CFSG.ClassicalInvolution.Asc77
