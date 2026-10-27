module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Standard
import CFSG.GroupTheory.OddOverlap

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem SolStd.inL {L : Subgroup H} (h : SolStd L) : InL L := by
  obtain ⟨-, t, ht2, hc⟩ := h
  have hne : zpowers t ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h1
    rw [h1, orderOf_one] at ht2
    omega
  refine ⟨zpowers t, hne, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; rfl), ?_⟩
  rwa [zpowers_eq_closure, centralizer_closure]

theorem StdBare.solStd_of_involution [Finite H] {L : Subgroup H} (hstd : StdBare L)
    (hq : CFSG.IsQuasisimple ↥L) {t : H} (ht2 : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set H)) : SolStd L := by
  have hle : L ≤ centralizer ({t} : Set H) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL x hx)
  have hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H) := fun _ hg =>
    CFSG.StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute hstd.2 htL ht2
      (mem_centralizer_singleton_iff.1 hg)
  exact ⟨hstd, t, ht2, isCompIn_of_normal hle hq
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hCt)⟩

theorem InL.solStd [Finite H] {L : Subgroup H} (hL : InL L) (hstd : StdBare L) : SolStd L := by
  obtain ⟨T, hT, hT2, hLc⟩ := hL
  have hev : 2 ∣ Nat.card T := two_dvd_card_of_isPGroup hT2 hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hev
  have htT : (t : H) ∈ T := t.2
  have ht2 : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htL : (t : H) ∈ centralizer (L : Set H) := mem_centralizer_iff.2 fun l hl =>
    (mem_centralizer_iff.1 (hLc.1 hl) t htT).symm
  exact hstd.solStd_of_involution hLc.isQuasisimple ht2 htL

end CFSG.EvenSporadicStandard.Induction
