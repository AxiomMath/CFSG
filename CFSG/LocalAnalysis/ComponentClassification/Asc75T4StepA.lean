module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Layer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingSolvable
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoGeneral
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding

section Conclusion

variable {G : Type*} [Group G] [Finite G]

@[expose] def Thm4Case1 (Q : Subgroup G) : Prop :=
  NormalIn (twoPrimeLayerIn Q) (twoPrimeLayerIn (⊤ : Subgroup G))

@[expose] def Thm4Case2 (Q : Subgroup G) : Prop :=
  CFSG.Open.pRank 2 (twoPrimeLayerIn Q) = 1 ∧
    (1 < CFSG.Open.pRank 2 Q → ∀ g : G, g ∉ normalizer (Q : Set G) →
      Even (Nat.card (rightConjugate Q g ⊓ normalizer (Q : Set G) : Subgroup G)) →
      ∃ S : Subgroup G, IsSylowOf 2 S (rightConjugate Q g) ∧ S ≤ normalizer (Q : Set G))

@[expose] def Thm4Case3 (Q : Subgroup G) : Prop :=
  ∃ g : G, g ∉ normalizer (Q : Set G) ∧ ∃ T : Subgroup G,
    IsSylowOf 2 T (rightConjugate Q g) ∧ T ≤ normalizer (Q : Set G) ∧
    ∃ n : ℕ, 2 ≤ n ∧ ∃ φ : oUpperTwoPrime (Q ⊔ T) →*
        Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = (oddCoreIn Q).subgroupOf (oUpperTwoPrime (Q ⊔ T))

@[expose] def Thm4Conclusion (Q : Subgroup G) : Prop :=
  Thm4Case1 Q ∨ Thm4Case2 Q ∨ Thm4Case3 Q

end Conclusion

theorem asc75Theorem4_iff : Asc75Theorem4 ↔
    ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G), TightlyEmbedded Q →
      twoPrimeLayerIn Q ≠ oddCoreIn Q → Thm4Conclusion Q :=
  Iff.rfl

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem one_le_pRank_of_even {X : Subgroup G} (hX : Even (Nat.card X)) :
    1 ≤ CFSG.Open.pRank 2 X := by
  obtain ⟨⟨t, htX⟩, ht⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (even_iff_two_dvd.mp hX)
  rw [Subgroup.orderOf_mk] at ht
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  refine CFSG.SectionRank.le_pRank one_lt_two ((zpowers_le).mpr htX) ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    (by rw [Nat.card_zpowers, ht, pow_one])
  · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self t i j).eq
  · intro y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]

theorem pRank_le_twoRank {X L : Subgroup G} (hXL : X ≤ L) :
    CFSG.Open.pRank 2 X ≤ CFSG.Open.twoRank L := by
  obtain ⟨E, hEX, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two X
  refine CFSG.SectionRank.le_pRank_of_injective (A := E) one_lt_two (hE.1.is_comm.comm)
    (fun a => Subtype.ext (by simpa using hE.2 a a.2)) hcard (Subgroup.inclusion (hEX.trans hXL))
    (Subgroup.inclusion_injective _) le_top

end Rank

variable {G : Type} [Group G] [Finite G]

theorem thm4Case1_or_thm4Case2_of_oddNormalizerOverlaps {Q : Subgroup G}
    (htight : TightlyEmbedded Q) (hK : twoPrimeLayerIn Q ≠ oddCoreIn Q)
    (hodd : OddNormalizerOverlaps Q) : Thm4Case1 Q ∨ Thm4Case2 Q := by
  rcases CFSG.ComponentClassification.AschbacherStrongEmbedding.theorem_2_part_two
      CFSG.ShultStronglyClosedTI.not_minimalInvolutionPointLocalFailure
      CFSG.ComponentClassification.AschbacherStrongEmbedding.benderDoubleCoverRigidity
      Q htight hodd with hn | hse
  · exact Or.inl (normalIn_twoPrimeLayerIn_top_of_normal hn)
  right
  set L := normalClosure (Q : Set G) with hL
  have hKQ : twoPrimeLayerIn Q ≤ Q := twoPrimeLayerIn_le Q
  have hKL : twoPrimeLayerIn Q ≤ L := hKQ.trans le_normalClosure
  have hrank : CFSG.Open.twoRank L ≤ 1 := by
    by_contra h
    have hs := CFSG.ComponentClassification.AschbacherStrongEmbedding.strongly_embedded_solvable
      L _ hse (by omega)
    have hle : (twoPrimeLayerIn Q).subgroupOf L ≤ (normalizer (Q : Set G)).subgroupOf L :=
      fun x hx => hKQ.trans le_normalizer hx
    exact not_isSolvable_twoPrimeLayerIn hK
      (Group.isSolvable_of_isSolvable_injective (f := (Subgroup.inclusion hle).comp
        (subgroupOfEquivOfLe hKL).symm.toMonoidHom)
        ((Subgroup.inclusion_injective hle).comp (subgroupOfEquivOfLe hKL).symm.injective))
  refine ⟨le_antisymm ((pRank_le_twoRank hKL).trans hrank)
    (one_le_pRank_of_even (even_card_twoPrimeLayerIn hK)), fun _ g hg heven => ?_⟩
  exact absurd heven (Nat.not_even_iff_odd.mpr (hodd g hg))

end CFSG.ComponentClassification.Asc75T4
