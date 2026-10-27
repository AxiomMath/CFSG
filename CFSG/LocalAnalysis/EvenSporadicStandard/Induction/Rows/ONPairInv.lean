module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONPinned

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.ONSchreier Cover


theorem on_pair_of_involution (H : Type) [Group H] (L K : Subgroup H) (hcov : OddCover .ONan L)
    (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K)
    (hK : IsOddCentralExt ↥onL (↥K ⧸ CFSG.oddCore ↥K)) (t : ↥L) (ht2' : orderOf (t : H) = 2)
    (hKt : ∀ k ∈ K, k * (t : H) = (t : H) * k) : ONQ H L K (t : H) := by
  have : Finite ↥L := hcov.finite (by decide : TauCeti.SporadicName.ONan ≠ .M)
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hKL)
  have hqt : orderOf (q ↥L ⟨(t : H), t.2⟩) = 2 := hcov.orderOf_q_involution t.2 ht2'
  have hle : (K.subgroupOf L).map (q ↥L) ≤ centralizer ({q ↥L ⟨(t : H), t.2⟩} : Set _) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKt k (Subgroup.mem_subgroupOf.1 hk))
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [on_card_centralizer hcov.2.2 hqt] at hdvd
  obtain ⟨hKq', π, hπs, hπc, hπo⟩ := hK
  have hqcard : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 80640 * Nat.card π.ker := by
    rw [← card_onL, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have hcard : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 80640 :=
    card_map_q_eq hKL hcov.2.1 (a := 1) (by norm_num) hπo hqcard (by simpa using hdvd)
  exact ⟨t.2, ht2', hKL, hKt, hKq.1, hcard⟩

end CFSG.EvenSporadicStandard.Induction
