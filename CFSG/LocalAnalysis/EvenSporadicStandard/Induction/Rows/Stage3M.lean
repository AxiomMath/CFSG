module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MRow
public import CFSG.Sporadic.GLQ.MonsterTwoRank
public import CFSG.Sporadic.Bridge.Y443Relabel

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.Monster.Existence CFSG.Monster.Existence.Compat
  CFSG.Monster.Generated CFSG.RankThree.PartOne.SPOR CFSG.YGroups.Y443

section Proved


theorem mPair_eq : MPair = PairShape (fun n => 2 * monsterBabyOrder ≤ n) := rfl

theorem mFacts : MonsterFacts (Carrier .M) :=
  monsterFacts_of_isSporadic ⟨MulEquiv.refl _⟩

theorem mPinnedFacts :
    PinnedFacts .M (fun n => 2 * monsterBabyOrder ≤ n) monsterBabyOrder monsterOrder where
  finite := Nat.finite_of_card_ne_zero (by rw [mFacts.card]; unfold monsterOrder; norm_num)
  simple := mFacts.simple
  nonabelian := mFacts.nonabelian
  card := mFacts.card
  even_card := by unfold monsterOrder; decide
  rank := fun X _ _ h => by
    obtain ⟨e⟩ := h
    have := mFacts.simple.toNontrivial
    have : Nontrivial X := e.symm.injective.nontrivial
    have h6 := CFSG.Sporadic.GLQ.monster_nontrivial_two_rank_at_least_six.2 X
      ⟨e.trans CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv⟩
    omega
  outTwo := outTwo_of_allInner mFacts.allInner
  pair := fun u K hQ => by
    have : Finite (Carrier .M) :=
      Nat.finite_of_card_ne_zero (by rw [mFacts.card]; unfold monsterOrder; norm_num)
    obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
    have hM : MonsterFacts ↥(⊤ : Subgroup (Carrier .M)) :=
      monsterFacts_of_isSporadic ⟨Subgroup.topEquiv⟩
    obtain ⟨-, hsub, hA, -, hC⟩ := m_pair_data hM huL hu2 hKL hKu hcard
    let u' : ↥(⊤ : Subgroup (Carrier .M)) := ⟨u, huL⟩
    have hu'2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
    let e : ↥(centralizer ({u'} : Set ↥(⊤ : Subgroup (Carrier .M)))) ≃* ↥K :=
      (MulEquiv.subgroupCongr hsub).symm.trans (Subgroup.subgroupOfEquivOfLe hKL)
    have hZ : Nat.card (center ↥(centralizer ({u'} :
        Set ↥(⊤ : Subgroup (Carrier .M))))) = 2 := by
      rw [← Subgroup.card_map_of_injective (centralizer ({u'} : Set _)).subtype_injective,
        hA.2.1, Nat.card_zpowers, hu'2]
    exact ⟨(card_center_of_mulEquiv' e).symm.trans hZ, (Nat.card_congr e.toEquiv).symm.trans hC⟩
  two_le := by unfold monsterBabyOrder; norm_num
  even_N := by unfold monsterBabyOrder; decide
  lt := by unfold monsterBabyOrder monsterOrder; norm_num
  cube := ⟨202547114678, by unfold monsterBabyOrder; norm_num,
    by unfold monsterBabyOrder; norm_num⟩
  ne_a7 := by unfold monsterBabyOrder; norm_num

theorem m_exists_pair :
    ∃ (u : Carrier .M) (K : Subgroup (Carrier .M)),
      PairShape (fun n => 2 * monsterBabyOrder ≤ n) (Carrier .M) ⊤ K u := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_mGriess_of_isSporadic
    (Y := Carrier .M) ⟨MulEquiv.refl _⟩
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  obtain ⟨-, a, z, ha, -, -, -, hA, -, -⟩ := hE
  have hcard := card_centralizer_of_isTwoACentralizer ha (hA a (IsConj.refl a))
    twoARemaining.toFacts
  refine ⟨φ.symm a, centralizer ({φ.symm a} : Set (Carrier .M)), mem_top _, ?_,
    le_top, fun k hk => mem_centralizer_singleton_iff.1 hk, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact ha
  · show 2 * monsterBabyOrder ≤ Nat.card ↥(centralizer ({φ.symm a} : Set _))
    rw [card_centralizer_map φ.symm a]
    exact hcard.ge

theorem m_fit (G : Type) [Group G] [Finite G] (L K : Subgroup G) (_ : IsSporadic ↥L .M)
    (_ : K ≤ L) (_ : CFSG.IsQuasisimple ↥K) (_ : CFSG.oddCore ↥K ≤ center ↥K)
    (hK : IsKPinned .M (fun n => 2 * monsterBabyOrder ≤ n) (↥K ⧸ CFSG.oddCore ↥K)) :
    2 * monsterBabyOrder ≤ Nat.card ↥K := by
  obtain ⟨u', K', hQ', ⟨f⟩⟩ := hK
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K)
  rw [Nat.card_congr f.toEquiv] at h4
  have hpos : 0 < Nat.card (CFSG.oddCore ↥K) := Nat.card_pos
  calc 2 * monsterBabyOrder ≤ Nat.card ↥K' := hQ'.2.2.2.2
    _ ≤ Nat.card ↥K := by rw [h4]; exact Nat.le_mul_of_pos_right _ hpos

noncomputable def stage3Row_m (hmult : OddMultTrivial .M) (hfix : MFixesElem) :
    Stage3Row [.M] (fun _ => MPair) :=
  stage3Row_of_pinned mPair_eq mPinnedFacts hmult (lemma36DataQ_m hmult hfix) (by norm_num)
    m_exists_pair (fun G _ _ L K hL hKL hKq hO hK => m_fit G L K hL hKL hKq hO hK)

end Proved

end CFSG.EvenSporadicStandard.Induction
