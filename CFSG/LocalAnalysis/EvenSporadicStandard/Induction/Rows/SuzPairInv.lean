module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzRowAtlas

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore Cover


theorem suz_pair_of_involution (H : Type) [Group H] (L K : Subgroup H) (hcov : OddCover .Suz L)
    (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K)
    (hK : IsOddCentralExt ↥suzD (↥K ⧸ CFSG.oddCore ↥K)) (t : ↥L) (ht2' : orderOf (t : H) = 2)
    (hKt : ∀ k ∈ K, k * (t : H) = (t : H) * k) : SuzQ H L K (t : H) := by
  have : Finite ↥L := hcov.finite (by decide : TauCeti.SporadicName.Suz ≠ .M)
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hKL)
  have hqt : orderOf (q ↥L ⟨(t : H), t.2⟩) = 2 := hcov.orderOf_q_involution t.2 ht2'
  have hle : (K.subgroupOf L).map (q ↥L) ≤ centralizer ({q ↥L ⟨(t : H), t.2⟩} : Set _) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKt k (Subgroup.mem_subgroupOf.1 hk))
  have hdvd := Subgroup.card_dvd_of_le hle
  obtain ⟨hKq', π, hπs, hπc, hπo⟩ := hK
  have hqcard : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 20160 * Nat.card π.ker := by
    rw [← card_suzD, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  obtain ⟨r, hr, hcard⟩ := exists_odd_card_map_q hKL hcov.2.1
  have h20160 : 20160 ∣ Nat.card (centralizer ({q ↥L ⟨(t : H), t.2⟩} : Set _)) := by
    refine Dvd.dvd.trans ?_ hdvd
    rw [hcard, hqcard, mul_assoc]
    exact dvd_mul_right _ _
  obtain ⟨f⟩ := suz_equiv_of_isSporadic hcov.2.2
  rw [suz_card_centralizer f hqt h20160] at hdvd
  have hcard' : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 20160 :=
    card_map_q_eq hKL hcov.2.1 (a := 3) (by norm_num) hπo hqcard (by simpa using hdvd)
  exact ⟨t.2, ht2', hKL, hKt, hKq.1, hcard'⟩

end CFSG.EvenSporadicStandard.Induction
