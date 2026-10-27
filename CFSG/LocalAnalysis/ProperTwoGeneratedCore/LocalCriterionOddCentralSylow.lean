module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylowActions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

variable {K : Type*} [Group K] [Finite K]

theorem odd_sylow_times_odd_normal_subgroup
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (B J : Subgroup K) [J.Normal] (P : Sylow p B) (hJodd : Odd (Nat.card J)) :
    Odd (Nat.card ((P : Subgroup B).map B.subtype ⊔ J : Subgroup K)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hPodd : Odd (Nat.card ((P : Subgroup B).map B.subtype : Subgroup K)) := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact hpodd.pow
  rw [sup_comm]
  exact CFSG.ComponentClassification.OddCore.odd_card_sup J _ hJodd hPodd

theorem odd_central_quotient_invariant_odd_sylow_exists
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (B J : Subgroup K) [J.Normal] (t : K) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J)) (hJB : J ≤ B)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    ∃ P : Sylow p B, t ∈ Subgroup.normalizer
      (((P : Subgroup B).map B.subtype : Subgroup K) : Set K) := by
  let P₀ : Sylow p B := Classical.choice inferInstance
  let Y := (P₀ : Subgroup B).map B.subtype ⊔ J
  have hYB : Y ≤ B := sup_le (Subgroup.map_subtype_le _) hJB
  have hJY : J ≤ Y := le_sup_right
  have hYodd : Odd (Nat.card Y) :=
    odd_sylow_times_odd_normal_subgroup p hp hpodd B J P₀ hJodd
  have hnorm := odd_central_quotient_subgroup_normalized J Y t hJY hcentral
  obtain ⟨R, hRnorm⟩ := involution_normalized_odd_subgroup_invariant_sylow
    p hp Y t ht hYodd hnorm
  have hindex : ¬ p ∣ Y.relIndex B :=
    sylow_overgroup_relIndex_prime_to p hp B Y P₀ le_sup_left
  obtain ⟨P, hPimage⟩ := sylow_extension_same_ambient_image p hp B Y hYB hindex R
  exact ⟨P, hPimage.symm ▸ hRnorm⟩

theorem odd_central_quotient_invariant_sylow_exists
    (p : ℕ) (hp : p.Prime) (B J : Subgroup K) [B.Normal] [J.Normal]
    (t : K) (ht : orderOf t = 2) (hJodd : Odd (Nat.card J)) (hJB : J ≤ B)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    ∃ P : Sylow p B, t ∈ Subgroup.normalizer
      (((P : Subgroup B).map B.subtype : Subgroup K) : Set K) := by
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · exact normal_subgroup_involution_invariant_two_sylow B t ht
  · exact odd_central_quotient_invariant_odd_sylow_exists
      p hp hpodd B J t ht hJodd hJB hcentral

theorem odd_central_quotient_invariant_odd_sylow_fixed
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (B J : Subgroup K) [J.Normal] (t : K) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J)) (hJB : J ≤ B)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J))
    (P : Sylow p B)
    (hPnorm : t ∈ Subgroup.normalizer
      (((P : Subgroup B).map B.subtype : Subgroup K) : Set K)) :
    ∃ R : Sylow p (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K),
      (R : Subgroup (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K)).map
        (B ⊓ Subgroup.centralizer ({t} : Set K)).subtype =
          (P : Subgroup B).map B.subtype ⊓ Subgroup.centralizer ({t} : Set K) := by
  let : Fact p.Prime := ⟨hp⟩
  let U := (P : Subgroup B).map B.subtype
  let Y := U ⊔ J
  let C := Subgroup.centralizer ({t} : Set K)
  have hYB : Y ≤ B := sup_le (Subgroup.map_subtype_le _) hJB
  have hJY : J ≤ Y := le_sup_right
  have hYodd : Odd (Nat.card Y) :=
    odd_sylow_times_odd_normal_subgroup p hp hpodd B J P hJodd
  have hnorm := odd_central_quotient_subgroup_normalized J Y t hJY hcentral
  obtain ⟨Q, hQimage⟩ := sylow_restriction_same_ambient_image p B Y hYB P le_sup_left
  have hQnorm : t ∈ Subgroup.normalizer
      (((Q : Subgroup Y).map Y.subtype : Subgroup K) : Set K) := hQimage.symm ▸ hPnorm
  obtain ⟨R, hRimage⟩ := involution_normalized_odd_sylow_fixed_intersection
    p hp Y t ht hYodd hnorm Q hQnorm
  let f := Subgroup.inclusion (show Y ⊓ C ≤ B ⊓ C from inf_le_inf_right C hYB)
  let W : Subgroup (B ⊓ C : Subgroup K) := (R : Subgroup (Y ⊓ C : Subgroup K)).map f
  have hindex : ¬ p ∣ Y.relIndex B :=
    sylow_overgroup_relIndex_prime_to p hp B Y P le_sup_left
  have hfac := odd_central_quotient_centralizer_factorization_eq
    p J B Y t ht hJodd hYB hJY hcentral hindex
  have hWcard : Nat.card W = p ^ (Nat.card (B ⊓ C : Subgroup K)).factorization p := by
    rw [Subgroup.card_map_of_injective
      (Subgroup.inclusion_injective (inf_le_inf_right C hYB)), R.card_eq_multiplicity, hfac]
  let S := Sylow.ofCard W hWcard
  refine ⟨S, ?_⟩
  change W.map (B ⊓ C).subtype = _
  rw [Subgroup.map_map]
  have hcomp : (B ⊓ C).subtype.comp f = (Y ⊓ C).subtype := by ext a; rfl
  rw [hcomp, hRimage, hQimage]

theorem odd_central_quotient_invariant_two_sylow_fixed
    (B J : Subgroup K) [J.Normal] (t : K) (hJodd : Odd (Nat.card J))
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J))
    (P : Sylow 2 B)
    (hPnorm : t ∈ Subgroup.normalizer
      (((P : Subgroup B).map B.subtype : Subgroup K) : Set K)) :
    ∃ R : Sylow 2 (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K),
      (R : Subgroup (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K)).map
        (B ⊓ Subgroup.centralizer ({t} : Set K)).subtype =
          (P : Subgroup B).map B.subtype ⊓ Subgroup.centralizer ({t} : Set K) := by
  let U := (P : Subgroup B).map B.subtype
  let C := Subgroup.centralizer ({t} : Set K)
  have hUC : U ≤ C := odd_central_quotient_normalized_two_subgroup_centralized
    J U t hJodd (P.isPGroup'.map B.subtype) hPnorm hcentral
  obtain ⟨R, hRimage⟩ := sylow_restriction_same_ambient_image 2 B (B ⊓ C)
    inf_le_left P (le_inf (Subgroup.map_subtype_le _) hUC)
  refine ⟨R, ?_⟩
  rw [hRimage, inf_eq_left.mpr hUC]

theorem odd_central_quotient_invariant_sylow_fixed
    (p : ℕ) (hp : p.Prime) (B J : Subgroup K) [J.Normal]
    (t : K) (ht : orderOf t = 2) (hJodd : Odd (Nat.card J)) (hJB : J ≤ B)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J))
    (P : Sylow p B)
    (hPnorm : t ∈ Subgroup.normalizer
      (((P : Subgroup B).map B.subtype : Subgroup K) : Set K)) :
    ∃ R : Sylow p (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K),
      (R : Subgroup (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K)).map
        (B ⊓ Subgroup.centralizer ({t} : Set K)).subtype =
          (P : Subgroup B).map B.subtype ⊓ Subgroup.centralizer ({t} : Set K) := by
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · exact odd_central_quotient_invariant_two_sylow_fixed B J t hJodd hcentral P hPnorm
  · exact odd_central_quotient_invariant_odd_sylow_fixed
      p hp hpodd B J t ht hJodd hJB hcentral P hPnorm

end CFSG.ProperTwoGeneratedCore
