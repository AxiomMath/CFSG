module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairWitnessPoint
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped MatrixGroups

universe u

variable {G : Type u} [Group G] [Finite G]

theorem high_rank_pair_point_data {H : Subgroup G} {z₀ : G}
    (h₀ : MinimalInvolutionPointLocalFailure H z₀)
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z₀ beta)
    {r f y : G} (hrB : r ∈ pairPointStabilizer H beta) (hr : orderOf r = 2)
    (hrz : Commute r z₀) (hrt : Commute r t) (hfr : Commute f r) (hft : Commute f t)
    (hy : y = r ∨ y = 1) (hs : orderOf (y * f * t) = 2) {a : ℕ} (ha : 1 ≤ a)
    (hF : FieldInvolutionOn (localInvolutionPointHull z₀ r) f a)
    (hA : ∃ A : Subgroup G, A ≤ pairPointStabilizer H beta ∧
      A ≤ Subgroup.centralizer ({y * f * t} : Set G) ∧ ⁅A, Subgroup.zpowers t⁆ = A ∧ A ≠ ⊥) :
    (∀ M : Subgroup G, M ≤ Subgroup.centralizer ({y * f * t} : Set G) →
      ⁅M, Subgroup.zpowers t⁆ = M → M ≤ localInvolutionPointHull z₀ (y * f * t)) ∧
    ∀ γ : rightCosetSpace H, rightCosetTranslate H γ t = γ →
      ¬ Subgroup.centralizer ({y * f * t} : Set G) ≤ rightCosetStabilizer H γ ∧
      localInvolutionPointHull z₀ r ⊓ Subgroup.centralizer ({y * f * t} : Set G) ≤
        localInvolutionPointHull z₀ (y * f * t) ∧
      SubfieldCentralizer (localInvolutionPointHull z₀ r) (y * f * t) a ∧
      Nat.card (involutionPointClass z₀ ∩ (rightCosetStabilizer H γ : Set G) ∩
        (Subgroup.centralizer ({r} : Set G) : Set G) ∩
        (Subgroup.centralizer ({y * f * t} : Set G) : Set G) : Set G) = 2 ^ a - 1 ∧
      (4 ≤ 2 ^ a → 2 ≤ twoRank (localInvolutionPointHull z₀ (y * f * t))) := by
  classical
  set s := y * f * t with hsdef
  set D := involutionPointClass z₀ with hDdef
  set Lr := localInvolutionPointHull z₀ r with hLrdef
  set Ls := localInvolutionPointHull z₀ s with hLsdef
  have htD : t ∈ D := ht.1
  have htord : orderOf t = 2 := order_two_of_mem_pointClass h₀.local_datum.distinguished_order htD
  have htH : t ∉ H := pair_flip_not_mem_point hbeta ht
  have hyt : Commute y t := by
    rcases hy with rfl | rfl
    · exact hrt
    · exact Commute.one_left t
  have hst : Commute s t := (hyt.mul_left hft).mul_left (Commute.refl t)
  have hrH : r ∈ H := pairPointStabilizer_le_point H beta hrB
  have hz₀H : z₀ ∈ H := h₀.local_datum.distinguished_mem
  have htLr : t ∈ Lr := mem_localHull htD hrt.symm
  have hescH : ¬ Subgroup.centralizer ({r} : Set G) ≤ H := fun hle =>
    htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr hrt.symm.eq))
  have hyL : ∀ x ∈ Lr, y * x = x * y := by
    intro x hx
    rcases hy with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp
        (localInvolutionPointHull_le_centralizer z₀ y hx)).symm
    · rw [one_mul, mul_one]
  have hsub := subfieldCentralizer_of_fieldInvolution ha hF (mem_normalizer_localHull hfr) hyL
    htLr hft htord
  obtain ⟨F, _, hFcard, φ, -⟩ := hF
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; positivity)
  have : CharP F 2 := char_two_of_card hFcard
  obtain ⟨k, _, hk, ⟨ψ⟩⟩ := id hsub
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := char_two_of_card hk
  have hLrs : Lr ⊓ Subgroup.centralizer ({s} : Set G) ≤ Ls := by
    apply le_of_mul_self_mem_of_equiv ψ
    intro g hg hgg
    by_cases hg1 : g = 1
    · rw [hg1]
      exact Ls.one_mem
    have hgord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
    have hgD := involution_mem_pointClass_of_mem_localHull h₀.local_datum hr hrz hescH hg.1 hgord
    exact mem_localHull hgD (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
  have htM : t ∈ Lr ⊓ Subgroup.centralizer ({s} : Set G) :=
    ⟨htLr, Subgroup.mem_centralizer_singleton_iff.mpr hst.eq.symm⟩
  have hcardM := card_inf_centralizer_of_equiv ψ htM htord
  rw [hk] at hcardM
  have hsq : ∀ g ∈ Lr ⊓ Subgroup.centralizer ({s} : Set G) ⊓ Subgroup.centralizer ({t} : Set G),
      g * g = 1 := fun g hg =>
    mul_self_of_commute_of_equiv φ htLr htord hg.1.1
      (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
  obtain ⟨-, huniq, -⟩ := (involution_point_unique_containment_action
    h₀.local_datum.distinguished_mem h₀.local_datum.distinguished_order).2
    h₀.local_datum.unique_containment
  obtain ⟨γ₀, hγ₀, -⟩ := huniq t htD
  have hγ₀' : rightCosetTranslate H γ₀ t = γ₀ := by
    rw [← pointRightCosetMul_eq_translate]
    exact hγ₀
  obtain ⟨A, hAB, hAs, hAt, hA1⟩ := hA
  have hAt' : ⁅A, Subgroup.zpowers t⁆ ≠ ⊥ := by rw [hAt]; exact hA1
  have hmoves := moves_class_flip_fixed_points h₀ hcomm hR1 hbeta ht hAB hAt'
  have hαz : rightCosetTranslate H (rightCosetMk H 1) z₀ = rightCosetMk H 1 := by
    rw [← mem_rightCosetStabilizer_iff, rightCosetStabilizer_base]
    exact hz₀H
  have hγdata : ∀ γ : rightCosetSpace H, rightCosetTranslate H γ t = γ →
      MinimalInvolutionPointLocalFailure (rightCosetStabilizer H γ) t ∧
      involutionPointClass t = D ∧ s ∈ rightCosetStabilizer H γ ∧
      r ∈ rightCosetStabilizer H γ ∧
      ¬ Subgroup.centralizer ({s} : Set G) ≤ rightCosetStabilizer H γ ∧
      ¬ Subgroup.centralizer ({r} : Set G) ≤ rightCosetStabilizer H γ := by
    intro γ hγ
    obtain ⟨hγt, hclass⟩ := minimalLocalFailure_at_fixed_point h₀ htD hγ
    refine ⟨hγt, hclass, (mem_rightCosetStabilizer_iff H γ s).mpr
      (commute_fixes_class_fixed_point h₀.local_datum htD hst hγ),
      (mem_rightCosetStabilizer_iff H γ r).mpr
      (commute_fixes_class_fixed_point h₀.local_datum htD hrt hγ), ?_, ?_⟩
    · intro hle
      obtain ⟨x, hxA, hxγ⟩ := hmoves γ hγ
      exact hxγ ((mem_rightCosetStabilizer_iff H γ x).mp (hle (hAs hxA)))
    · intro hle
      have hz₀γ : rightCosetTranslate H γ z₀ = γ := (mem_rightCosetStabilizer_iff H γ z₀).mp
        (hle (Subgroup.mem_centralizer_singleton_iff.mpr hrz.eq.symm))
      have hγα := class_fixed_point_unique h₀.local_datum (distinguished_mem_pointClass z₀)
        hz₀γ hαz
      rw [hγα] at hγ
      exact hbeta (ht.2.symm.trans hγ)
  have hLsM : ∀ M : Subgroup G, M ≤ Subgroup.centralizer ({s} : Set G) →
      ⁅M, Subgroup.zpowers t⁆ = M → M ≤ Ls := by
    intro M hMs hMt
    obtain ⟨hγt, hclass, hsγ, -, hescs, -⟩ := hγdata γ₀ hγ₀'
    have hle := le_localHull_of_commutator_eq hγt hcomm hR1 hsγ hs hst hescs hMs hMt
    rwa [localInvolutionPointHull, hclass] at hle
  refine ⟨hLsM, fun γ hγ => ?_⟩
  obtain ⟨hγt, hclass, -, hrγ, hescs, hescr⟩ := hγdata γ hγ
  set E := Lr ⊓ Subgroup.centralizer ({s} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) with hEdef
  have hX : involutionPointClass z₀ ∩ (rightCosetStabilizer H γ : Set G) ∩
      (Subgroup.centralizer ({r} : Set G) : Set G) ∩
      (Subgroup.centralizer ({s} : Set G) : Set G) = (E : Set G) \ {1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe, hEdef,
      Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨⟨hgD, hgγ⟩, hgr⟩, hgs⟩
      have hgt : Commute g t := hull_class_commute hγt hcomm hR1 hrγ hr hrt hescr
        ⟨⟨by rw [hclass]; exact hgD, hgγ⟩, hgr⟩
      refine ⟨⟨⟨mem_localHull hgD (Subgroup.mem_centralizer_singleton_iff.mp hgr), hgs⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hgt.eq⟩, ?_⟩
      intro hg1
      have := order_two_of_mem_pointClass h₀.local_datum.distinguished_order hgD
      rw [hg1, orderOf_one] at this
      omega
    · rintro ⟨⟨⟨hgL, hgs⟩, hgt⟩, hg1⟩
      have hgg : g * g = 1 := hsq g ⟨⟨hgL, hgs⟩, hgt⟩
      have hgord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
      refine ⟨⟨⟨involution_mem_pointClass_of_mem_localHull h₀.local_datum hr hrz hescH hgL
        hgord, ?_⟩, localInvolutionPointHull_le_centralizer z₀ r hgL⟩, hgs⟩
      exact (mem_rightCosetStabilizer_iff H γ g).mpr (commute_fixes_class_fixed_point
        h₀.local_datum htD (Subgroup.mem_centralizer_singleton_iff.mp hgt) hγ)
  have hEcard : Nat.card E = 2 ^ a := by rw [← hcardM]
  refine ⟨hescs, hLrs, hsub, ?_, ?_⟩
  · rw [hX, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (E.one_mem), ← Nat.card_coe_set_eq]
    rw [← hEcard]
    rfl
  · intro h4
    have hEab : IsElemAbelian 2 E := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => by rw [pow_two]; exact hsq g hg⟩
      have ha := hsq a a.2
      have hb := hsq b b.2
      have hab := hsq _ (E.mul_mem a.2 b.2)
      calc (a : G) * b = ((a : G) * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
        _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
        _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right ha]
    exact FixedPointModel.two_le_twoRank_of_le hEab (by rw [hEcard]; exact h4)
      ((inf_le_left).trans hLrs)

end CFSG.ProperTwoGeneratedCore.HighRankPair
