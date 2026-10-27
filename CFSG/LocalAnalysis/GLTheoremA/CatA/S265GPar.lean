module

public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.SeitzGeneration.ExcParabolicCard
public import CFSG.RankThree.PartOne.KF.F4ParabolicSums

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

section Entrywise

variable
  {τ : Tag} {K : Type} [Field K]

theorem entrywise_mem_parabolic (σ : K ≃+* K) {J : Set (Fin τ.rank)} {g : ModGL τ K}
    (hg : g ∈ parabolicSubgroup τ K J) :
    Units.map (entrywiseHom σ.toRingHom) g ∈ parabolicSubgroup τ K J := by
  have hle : parabolicSubgroup τ K J ≤
      (parabolicSubgroup τ K J).comap (Units.map (entrywiseHom σ.toRingHom)) := by
    refine sup_le (fun b hb => Subgroup.mem_comap.2 ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_sup_left (entrywise_mem_borelGroup (σ := σ) hb)
    · rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, entrywise_weylElt_one σ j]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, rfl⟩)
  exact hle hg

end Entrywise

section Index


theorem parabolicSum_thirteen [Fintype (WeylGroup .F4)] (q : ℕ) :
    parabolicSum .F4 (maskSet .F4 13 : Set (Fin Tag.F4.rank)) q =
      (1 + q + q ^ 2) * parabolicSum .F4 (maskSet .F4 5 : Set (Fin Tag.F4.rank)) q := by
  have htail : chainCheck CFSG.RankThree.PartOne.KFU.f4ChainA1A2.tail 5 = true := by
    have h := CFSG.RankThree.PartOne.KFU.f4ChainA1A2_check
    rw [CFSG.RankThree.PartOne.KFU.f4ChainA1A2, chainCheck, Bool.and_eq_true] at h
    exact h.2
  rw [parabolicSum_eq_of_chainCheck q _ _ CFSG.RankThree.PartOne.KFU.f4ChainA1A2_check,
    parabolicSum_eq_of_chainCheck q _ _ htail]
  simp [CFSG.RankThree.PartOne.KFU.f4ChainA1A2, ChainStep.value, geomSum,
    Finset.sum_range_succ] <;> ring

variable
  {K : Type} [Field K] [Finite K]

theorem parabolic_five_le_thirteen :
    parabolicSubgroup .F4 K (maskSet .F4 5 : Set (Fin Tag.F4.rank)) ≤
      parabolicSubgroup .F4 K (maskSet .F4 13 : Set (Fin Tag.F4.rank)) :=
  ((standard_parabolic_cells .F4 K).2.2.2.1 _ _).2 (Finset.coe_subset.2 (by decide))

theorem index_five_thirteen :
    (((parabolicSubgroup .F4 K (maskSet .F4 5 : Set (Fin Tag.F4.rank))).subgroupOf
      (adjointGroup .F4 K)).subgroupOf
        ((parabolicSubgroup .F4 K (maskSet .F4 13 : Set (Fin Tag.F4.rank))).subgroupOf
          (adjointGroup .F4 K))).index = 1 + Nat.card K + Nat.card K ^ 2 := by
  classical
  haveI : Fintype (WeylGroup .F4) := Fintype.ofFinite _
  haveI : Finite (ModGL .F4 K) := finite_modGL
  set P5 := parabolicSubgroup .F4 K (maskSet .F4 5 : Set (Fin Tag.F4.rank)) with hP5
  set P13 := parabolicSubgroup .F4 K (maskSet .F4 13 : Set (Fin Tag.F4.rank)) with hP13
  have h5C : P5 ≤ adjointGroup .F4 K := parabolicSubgroup_le_adjointGroup _ _ _
  have h13C : P13 ≤ adjointGroup .F4 K := parabolicSubgroup_le_adjointGroup _ _ _
  have hle : P5.subgroupOf (adjointGroup .F4 K) ≤ P13.subgroupOf (adjointGroup .F4 K) :=
    Subgroup.comap_mono parabolic_five_le_thirteen
  have hmul := Subgroup.card_mul_index
    ((P5.subgroupOf (adjointGroup .F4 K)).subgroupOf (P13.subgroupOf (adjointGroup .F4 K)))
  have h1 : Nat.card ((P5.subgroupOf (adjointGroup .F4 K)).subgroupOf
      (P13.subgroupOf (adjointGroup .F4 K))) = Nat.card P5 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h5C).toEquiv)
  have h2 : Nat.card (P13.subgroupOf (adjointGroup .F4 K)) = Nat.card P13 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h13C).toEquiv
  rw [h1, h2] at hmul
  obtain ⟨-, -, -, -, -, -, hcell⟩ := standard_parabolic_cells .F4 K
  have h13 : Nat.card P13 = (1 + Nat.card K + Nat.card K ^ 2) * Nat.card P5 := by
    rw [hP13, hP5, hcell, hcell, CFSG.LieType.SeitzGeneration.finsum_parabolicWeylGroup_eq,
      CFSG.LieType.SeitzGeneration.finsum_parabolicWeylGroup_eq, parabolicSum_thirteen]
    ring
  rw [h13, mul_comm (1 + Nat.card K + Nat.card K ^ 2)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

theorem not_three_dvd_index_five_thirteen (hq : Nat.card K % 3 = 2) :
    ¬ 3 ∣ (((parabolicSubgroup .F4 K (maskSet .F4 5 : Set (Fin Tag.F4.rank))).subgroupOf
      (adjointGroup .F4 K)).subgroupOf
        ((parabolicSubgroup .F4 K (maskSet .F4 13 : Set (Fin Tag.F4.rank))).subgroupOf
          (adjointGroup .F4 K))).index := by
  rw [index_five_thirteen]
  intro h
  have h3 : (1 + Nat.card K + Nat.card K ^ 2) % 3 = 1 := by
    rw [Nat.add_mod, Nat.add_mod 1, Nat.pow_mod, hq]
  omega

end Index

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
