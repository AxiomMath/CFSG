module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Co2Schreier.InvolClasses
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Census
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co2

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier

theorem co2P_center_eq_bot :
    center ↥co2P = ⊥ := by
  have : IsSimpleGroup ↥co2P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co2.isSimpleGroup_Co2 co2PermEquiv.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥co2P) with h | h
  · exact h
  · exfalso
    let _ : CommGroup ↥co2P :=
      { (inferInstance : Group ↥co2P) with
        mul_comm := fun a b => mem_center_iff.mp (h ▸ mem_top b) a }
    have hp := IsSimpleGroup.prime_card (α := ↥co2P)
    rw [card_co2P] at hp
    exact absurd hp (by norm_num)

theorem co2AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Co2) ↥co2P (co2P.subgroupOf co2P) :=
  autModel_of_allInner co2PermEquiv.symm co2P_center_eq_bot CTUC_Co2_full_automorphisms_inner

theorem factorization_two_pow_mul (k m : ℕ) (hm : Odd m) : (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)), add_zero]

theorem card_centralizer_locZ :
    Nat.card ↥(co2P ⊓ centralizer {locZ}) = 743178240 := by
  rw [← locC_eq_centralizer, card_locC]

theorem card_centralizer_locT :
    Nat.card ↥(co2P ⊓ centralizer {locT}) = 41287680 := by
  rw [← locD_eq_centralizer, card_locD]

theorem card_centralizer_locU :
    Nat.card ↥(co2P ⊓ centralizer {locU}) = 1474560 := card_locH3

theorem co2_conj_root
    (g : Equiv.Perm (Fin 2300))
    (hg : g ∈ co2P) (hg2 : g ^ 2 = 1)
    (hg1 : g ≠ 1) : ∃ c ∈ [locZ, locT, locU], ∃ w ∈ co2P, w * g * w⁻¹ = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (⟨g, hg⟩ : co2P) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hg2)) (fun h => hg1 (congrArg Subtype.val h))
  have key : ∀ c : co2P, IsConj (⟨g, hg⟩ : co2P) c → ∃ w ∈ co2P, w * g * w⁻¹ = c := by
    intro c hc
    obtain ⟨w, hw⟩ := isConj_iff.mp hc
    exact ⟨w, w.2, by simpa using congrArg Subtype.val hw⟩
  rcases isConj_cases_myRep ⟨g, hg⟩ hord with h | h | h
  · exact ⟨locZ, by simp, key zP h⟩
  · exact ⟨locT, by simp, key tP h⟩
  · exact ⟨locU, by simp, key uP h⟩

theorem sporadicCaseOdd_Co2_of_check
    (hY : YCensus17 (co2P.subgroupOf co2P) (fun _ => False))
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .Co2 := by
  have hX : co2P.subgroupOf co2P = ⊤ := subgroupOf_self _
  refine sporadicCaseOdd_of_yCensus17 h32 h33 co2AutModel (by rw [hX]; exact le_top) ?_ hY
  rw [hX]
  exact yCensus_top_le_top

end CFSG.ComponentClassification.RankTwoSporadic.Co2
