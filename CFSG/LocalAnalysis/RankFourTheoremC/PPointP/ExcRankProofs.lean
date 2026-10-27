module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcEndgame
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.RankThree.PartOne.KP.SporadicRankFi22
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple
public import CFSG.Sporadic.Bridge.Y322Central
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenPair
public import CFSG.LieType.SeitzGeneration.OuterQuotient
import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.StrongP
open CFSG.Monster.Generated (Gmat)

theorem card_le_sq_of_not_pow_three_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ^ 3 ∣ Nat.card G) {B : Subgroup G} (hB : IsElemAbelian p B) :
    Nat.card B ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p B := fun x => ⟨1, Subtype.ext (by simpa using hB.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
  have hdvd : p ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card B
  have hk2 : k ≤ 2 := by
    by_contra hk3
    exact h ((pow_dvd_pow p (by omega)).trans hdvd)
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hk2

theorem card_le_sq_of_hasNoncommPair {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h4 : ¬ p ^ 4 ∣ Nat.card G) (hN : HasNoncommPair p G) {B : Subgroup G}
    (hB : IsElemAbelian p B) : Nat.card B ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p B := fun x => ⟨1, Subtype.ext (by simpa using hB.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
  have hdvd : p ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card B
  have hk3 : k ≤ 3 := by
    by_contra h
    exact h4 ((pow_dvd_pow p (by omega)).trans hdvd)
  rcases (by omega : k ≤ 2 ∨ k = 3) with hk2 | rfl
  · rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk2
  exfalso
  have hnd : ¬ p ∣ B.index := by
    intro hi
    apply h4
    rw [← Subgroup.card_mul_index B, hk, pow_succ]
    exact Nat.mul_dvd_mul_left _ hi
  let S : Sylow p G := hpg.toSylow hnd
  obtain ⟨x, y, -, -, hxy, hH⟩ := hN
  obtain ⟨T, hT⟩ := hH.exists_le_sylow
  have hxT : x ∈ (T : Subgroup G) := hT (Subgroup.subset_closure (by simp))
  have hyT : y ∈ (T : Subgroup G) := hT (Subgroup.subset_closure (by simp))
  let e := Sylow.equiv T S
  have h1 : (⟨x, hxT⟩ : (T : Subgroup G)) * ⟨y, hyT⟩ = ⟨y, hyT⟩ * ⟨x, hxT⟩ := by
    apply e.injective
    rw [map_mul, map_mul]
    exact hB.1.is_comm.comm (e ⟨x, hxT⟩) (e ⟨y, hyT⟩)
  exact hxy (congrArg Subtype.val h1)

theorem le_inner_of_not_dvd_card_outer {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer K)) {A : Subgroup (MulAut K)} (hA : IsPGroup p A) :
    A ≤ (MulAut.conj : K →* MulAut K).range := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut K) := MulEquiv.finite_left
  refine CFSG.LieType.SeitzGeneration.le_inner_of_coprime_card_outer ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA
  rw [hk]
  exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 h)

section Fi22


theorem card_group_fi22 : Nat.card TauCeti.SporadicName.Fi22.Group = 64561751654400 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr CFSG.Sporadic.Fi22.fi22EquivJ.toEquiv,
    CFSG.Sporadic.Fi22.card_J]

theorem card_le_of_fi22_five {K : Type*} [Group K] [Finite K]
    (h : Nonempty (K ≃* TauCeti.SporadicName.Fi22.Group)) {B : Subgroup K}
    (hB : IsElemAbelian 5 B) : Nat.card B ≤ 5 ^ 2 := by
  obtain ⟨e⟩ := h
  refine card_le_sq_of_not_pow_three_dvd Nat.prime_five ?_ hB
  rw [Nat.card_congr e.toEquiv, card_group_fi22]
  norm_num

end Fi22

section Fi22Outer


theorem card_outer_of_fi22 {K : Type*} [Group K]
    (h : Nonempty (K ≃* TauCeti.SporadicName.Fi22.Group)) : Nat.card (Outer K) = 2 := by
  obtain ⟨e⟩ := h
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  let f : K ≃* CFSG.Blueprint.NativeSporadic.Fi22 := e.trans b.symm
  rw [Nat.card_congr
    (@equivalence K CFSG.Blueprint.NativeSporadic.Fi22 _ Units.instGroup f).toEquiv]
  exact CFSG.RankThree.PartOne.card_outer_fi22_carrier

end Fi22Outer

section Monster


theorem nonempty_mulEquiv_gmat_of_M {K : Type*} [Group K]
    (h : Nonempty (K ≃* TauCeti.SporadicName.M.Group)) : Nonempty (K ≃* Gmat) := by
  obtain ⟨φ⟩ := h
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (MulEquiv.refl (CFSG.Blueprint.NativeSporadic.Carrier .M))
  exact ⟨φ.trans (b.symm.trans e)⟩

section Rank


theorem kFactExcludedRank : KFactExcludedRank := by
  intro K _ _ p i hp hi he B hB
  rcases hi with ⟨rfl, rfl⟩ | ⟨hp', rfl⟩
  · exact card_le_of_fi22_five he hB
  obtain ⟨e⟩ := nonempty_mulEquiv_gmat_of_M he
  have hK : Nat.card K = monsterOrder := by
    rw [Nat.card_congr e.toEquiv, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
  rcases hp' with rfl | rfl
  · exact card_le_sq_of_not_pow_three_dvd hp (by rw [hK]; norm_num [monsterOrder]) hB
  · exact card_le_sq_of_hasNoncommPair hp (by rw [hK]; norm_num [monsterOrder])
      (CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_thirteen_of_mulEquiv_Gmat e) hB

end Rank

section Inner


theorem kFactExcludedInner : KFactExcludedInner := by
  intro K _ _ p i hp hi he A hA
  rcases hi with ⟨h, hp7, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨e⟩ := he
    refine le_inner_of_not_dvd_card_outer hp ?_ hA
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.RankThree.PartOne.not_dvd_outer_alternating hp (by omega) h
  · refine le_inner_of_not_dvd_card_outer hp ?_ hA
    rw [card_outer_of_fi22 he]
    norm_num
  · obtain ⟨e⟩ := nonempty_mulEquiv_gmat_of_M he
    intro α _
    obtain ⟨g, rfl⟩ := CFSG.ComponentClassification.BMCase.inner_of_equiv e
      CFSG.RankThree.PartOne.SPOR.allInner_Gmat α
    exact ⟨g, rfl⟩

end Inner

section Endgame


theorem pPointExclusionFive_of_partI (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut) : PPointExclusionFive :=
  pPointExclusionFive_of_kFacts' h243 h244 hsig kFactExcludedRank kFactExcludedInner

end Endgame

end Monster

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
