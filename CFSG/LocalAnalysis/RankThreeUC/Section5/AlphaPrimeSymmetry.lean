module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
import CFSG.LocalAnalysis.RankThreeUC.Section5.ActorInversion
import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
import CFSG.GroupTheory.OddPGroupNoncyclicChar
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

theorem two_notMem_alphaSet_of_pCore_eq_bot {G : Type} [Group G] [Finite G] (hO2 : CFSG.pCore 2 G = ⊥) :
    2 ∉ alphaSet G := by
  rintro ⟨-, hrank⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRn : (CFSG.Open.pCoreOf 2 (commutator G)).Normal := ConjAct.normal_of_characteristic_of_normal
  have hRp : IsPGroup 2 (CFSG.Open.pCoreOf 2 (commutator G)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (commutator G)
  have hRbot : CFSG.Open.pCoreOf 2 (commutator G) = ⊥ :=
    le_bot_iff.1 (hO2 ▸ CFSG.LieType.BorelTits.le_pCore 2 hRn hRp)
  have hle : CFSG.Open.pRank 2 (CFSG.Open.pCoreOf 2 (commutator G)) ≤ 1 := by
    refine CFSG.SectionRank.pRank_le Nat.one_lt_two fun E hE _ => ?_
    rw [hRbot, le_bot_iff] at hE
    rw [hE, Subgroup.card_bot]
    norm_num
  omega

theorem exponent_eq_prime_of_not_isCyclic {G : Type} [Group G] {q : ℕ} (hqp : q.Prime) {X : Subgroup G}
    (hnc : ¬ IsCyclic ↥X) (h : ∀ x ∈ X, x ^ q = 1) : Monoid.exponent ↥X = q := by
  have hdvd : Monoid.exponent ↥X ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (h y.1 y.2)
  rcases (Nat.dvd_prime hqp).1 hdvd with h1 | h1
  · exfalso
    rw [Monoid.exp_eq_one_iff] at h1
    haveI := h1
    exact hnc inferInstance
  · exact h1

theorem mem_scriptQ_of_le_of_rank_gt_one {G : Type} [Group G] [Finite G] {q : ℕ} (hqp : q.Prime) {Q X : Subgroup G}
    (hQ : Q ∈ scriptQ G q) (hXQ : X ≤ Q) (hXn : X.Normal) (hXr : 1 < CFSG.Open.pRank q X) :
    X ∈ scriptQ G q := by
  have hXnc : ¬ IsCyclic ↥X := by
    intro hcyc
    have h1 : CFSG.Open.pRank q X ≤ 1 := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_sylow_cyclic hqp fun S =>
        Subgroup.isCyclic _
    omega
  have hXexp1 : ∀ x ∈ X, x ^ q = 1 := fun x hx => by
    have h := Monoid.pow_exponent_eq_one (⟨x, hXQ hx⟩ : ↥Q)
    rw [hQ.2.2.2.1] at h
    exact congrArg Subtype.val h
  refine ⟨hXn, hQ.2.1.to_le hXQ, hXnc, exponent_eq_prime_of_not_isCyclic hqp hXnc hXexp1, ?_,
    hXQ.trans hQ.2.2.2.2.2⟩
  refine eq_bot_iff.2 ?_
  rw [← hQ.2.2.2.2.1]
  exact Subgroup.commutator_mono (Subgroup.commutator_mono hXQ hXQ) hXQ

theorem exists_mem_scriptQ_of_mem_alphaSet {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q ∈ alphaSet G)
    (hq2 : q ≠ 2) : ∃ Q ∈ scriptQ G q, 1 < CFSG.Open.pRank q Q := by
  obtain ⟨hqp, hrank⟩ := hq
  haveI : Fact q.Prime := ⟨hqp⟩
  have hRn : (CFSG.Open.pCoreOf q (commutator G)).Normal := ConjAct.normal_of_characteristic_of_normal
  have hRp : IsPGroup q (CFSG.Open.pCoreOf q (commutator G)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup q (commutator G)
  have hRle : CFSG.Open.pCoreOf q (commutator G) ≤ commutator G :=
    CFSG.LieType.BorelTits.pCoreOf_le q (commutator G)
  have hRnc : ¬ IsCyclic ↥(CFSG.Open.pCoreOf q (commutator G)) := by
    intro hcyc
    have h1 : CFSG.Open.pRank q (CFSG.Open.pCoreOf q (commutator G)) ≤ 1 := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_sylow_cyclic hqp fun S =>
        Subgroup.isCyclic _
    omega
  obtain ⟨D, hDR, hDchar, hDnc, hDexp, hDclass⟩ :=
    CFSG.GroupTheory.exists_characteristic_noncyclic_exponent_classTwo hq2 hRp hRnc
  have hDn : D.Normal := by
    haveI := hRn
    haveI := hDchar
    have h := (inferInstance :
      ((D.subgroupOf (CFSG.Open.pCoreOf q (commutator G))).map
        (CFSG.Open.pCoreOf q (commutator G)).subtype).Normal)
    rwa [Subgroup.map_subgroupOf_eq_of_le hDR] at h
  have hDp : IsPGroup q D := hRp.to_le hDR
  have hDr : 1 < CFSG.Open.pRank q D := by
    by_contra hle
    push Not at hle
    refine hDnc (CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one hqp hq2 hDp ?_)
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hle
  exact ⟨D, ⟨hDn, hDp, hDnc, exponent_eq_prime_of_not_isCyclic hqp hDnc hDexp, hDclass, hDR.trans hRle⟩, hDr⟩

theorem exists_minimal_normal_of_rank_gt_one {G : Type} [Group G] [Finite G] {q : ℕ} {D : Subgroup G}
    (hDn : D.Normal) (hDr : 1 < CFSG.Open.pRank q D) :
    ∃ P' : Subgroup G, P' ≤ D ∧ P'.Normal ∧ 1 < CFSG.Open.pRank q P' ∧
      ∀ X : Subgroup G, X.Normal → 1 < CFSG.Open.pRank q X → X ≤ P' → X = P' := by
  obtain ⟨P', ⟨hP'n, hP'D, hP'r⟩, hmin⟩ :=
    wellFounded_lt.has_min {X : Subgroup G | X.Normal ∧ X ≤ D ∧ 1 < CFSG.Open.pRank q X}
      ⟨D, hDn, le_rfl, hDr⟩
  refine ⟨P', hP'D, hP'n, hP'r, fun X hXn hXr hXP => ?_⟩
  by_contra hne
  exact hmin X ⟨hXn, hXP.trans hP'D, hXr⟩ (lt_of_le_of_ne hXP hne)

theorem exists_binaryActionRankCounterexample_of_mem_alphaSet {G : Type} [Group G] [Finite G] {p : ℕ}
    {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} (hc : BinaryActionRankCounterexample G p P T B e ρ) {q : ℕ}
    (hq : q ∈ alphaSet G) : ∃ P' : Subgroup G, BinaryActionRankCounterexample G q P' T B e ρ := by
  have hqp : q.Prime := hq.1
  haveI : Fact q.Prime := ⟨hqp⟩
  have hcF := hc.faithfulBinaryIrreducibleAction
  have h51 := hc.oddPrimeClassTwoAction
  have hS := h51.setting
  have hO2 : CFSG.pCore 2 G = ⊥ :=
    pCore_eq_bot_of_faithful_irreducible 2 ρ hcF.faithful hcF.irreducible
  have hq2 : q ≠ 2 := fun h => two_notMem_alphaSet_of_pCore_eq_bot hO2 (h ▸ hq)
  obtain ⟨D, hDQ, hDr⟩ := exists_mem_scriptQ_of_mem_alphaSet hq hq2
  obtain ⟨P', hP'D, hP'n, hP'r, hP'min⟩ := exists_minimal_normal_of_rank_gt_one (q := q) hDQ.1 hDr
  have hP'Q : P' ∈ scriptQ G q := mem_scriptQ_of_le_of_rank_gt_one hqp hDQ hP'D hP'n hP'r
  have hN : Subgroup.normalizer (P' : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hP'n
  refine ⟨P', ⟨⟨⟨hqp, hqp.odd_of_ne_two hq2, hP'Q.2.1, hP'Q.2.2.2.1, hP'Q.2.2.2.2.1, hS.twoGroup, hS.abelian,
    hS.oddOrder, hS.prod_comm, by rw [hN]; exact le_top, by rw [hN]; exact le_top⟩,
    fun b hb hb1 => hc.cyclicCentralizersAndFewComponentConjugates.cyclic_centralizer q hq P' hP'Q b hb hb1,
    h51.two_lt, h51.pi_eq, h51.exponent_Or, h51.normalizes⟩,
    ⟨hcF.faithful, hcF.irreducible, hcF.sylow, hcF.comm_Z_B, hP'n, hP'r, hP'min⟩,
    hc.cyclicCentralizersAndFewComponentConjugates, ?_⟩⟩
  rintro (h1 | h2 | ⟨-, -, h3⟩)
  · exact hc.not_concl (Or.inl h1)
  · exact hc.not_concl (Or.inr (Or.inl h2))
  · exact h3 (ActorInversion.inverted hc)

end CFSG.LocalAnalysis.RankThreeUC.Section5
