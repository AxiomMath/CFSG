module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical
public import CFSG.LieType.TitsSimplicity.LeviQuasisimple
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.SeitzGeneration.Dispatch
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.BQ

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity CFSG.LieType.TitsSimplicity.Levi
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup

theorem exists_simpleSection_map {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y]
    (π : K →* Y) (hker : π.ker ≤ center K) (L : Subgroup K) (hL : CFSG.IsQuasisimple ↥L) :
    ∃ W : Subgroup Y, S622IsSimpleSection (L.map π) W ∧
      W.relIndex (L.map π) = Nat.card (↥L ⧸ center ↥L) ∧ Nat.card W ∣ Nat.card (center ↥L) := by
  obtain ⟨-, hsimple, hnab⟩ := hL
  have hψs : Function.Surjective (π.subgroupMap L) := π.subgroupMap_surjective L
  have hkerψ : (π.subgroupMap L).ker ≤ (QuotientGroup.mk' (center ↥L)).ker := by
    intro x hx
    rw [QuotientGroup.ker_mk']
    have hx' : (x : K) ∈ π.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      simpa using congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hx') y)
  obtain ⟨φ, hφψ⟩ : ∃ φ : ↥(L.map π) →* ↥L ⧸ center ↥L,
      ∀ x, φ (π.subgroupMap L x) = (x : ↥L ⧸ center ↥L) :=
    ⟨_, MonoidHom.liftOfRightInverse_comp_apply _ _ (Function.rightInverse_surjInv hψs)
      ⟨QuotientGroup.mk' (center ↥L), hkerψ⟩⟩
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨_, hφψ x⟩
  have hφker : φ.ker = (center ↥L).map (π.subgroupMap L) := by
    have hcomp : φ.comp (π.subgroupMap L) = QuotientGroup.mk' (center ↥L) :=
      MonoidHom.ext hφψ
    rw [← Subgroup.map_comap_eq_self_of_surjective hψs φ.ker, MonoidHom.comap_ker, hcomp,
      QuotientGroup.ker_mk']
  haveI := hsimple
  refine ⟨φ.ker.map (L.map π).subtype, S622IsSimpleSection.of_surjective φ hφs hnab, ?_, ?_⟩
  · have hsub : (φ.ker.map (L.map π).subtype).subgroupOf (L.map π) = φ.ker :=
      Subgroup.comap_map_eq_self_of_injective (L.map π).subtype_injective φ.ker
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ hφs,
      Subgroup.card_top]
  · rw [Subgroup.card_subtype, hφker]
    exact Subgroup.card_map_dvd _ _

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

@[expose] def radicalOff (D : UniversalRootDatum K) (I : Finset (Fin D.rank)) : Subgroup K :=
  ⨆ j ∈ ((I : Set (Fin D.rank))ᶜ), radical D j

theorem leviC_orderEmbOfFin (I : Finset (Fin D.rank)) :
    leviC D (I.orderEmbOfFin rfl) = levi D.rootGroup I := by
  rw [leviC, Finset.image_orderEmbOfFin_univ]

theorem isPGroup_radicalOff {p : ℕ} (hU : IsPGroup p (posUnipotent D)) (I : Finset (Fin D.rank)) :
    IsPGroup p (radicalOff D I) :=
  hU.to_le (iSup₂_le fun j _ => radical_le_posUnipotent j)

theorem not_dvd_card_torus {Y : Type} [Group Y] [Finite K] {π : K →* Y} {M : ℕ}
    (h : BorelQuotient D n H π M) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ¬ p ∣ Nat.card (⨆ i, H i : Subgroup K) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(⨆ i, H i : Subgroup K)) p hdvd
  have hmem : (t : K) ∈ Subgroup.closure (⋃ i, (H i : Set K)) := by
    rw [← Subgroup.iSup_eq_closure]
    exact t.2
  have hpow : (t : K) ^ M = 1 := by
    refine pow_eq_one_of_mem_closure ?_ ?_ hmem
    · intro a ha b hb _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
      exact h.extras.torus_commute i j a hi b hj
    · intro s hs
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
      exact h.torus_pow i s hi
  apply hpM
  rw [← ht, ← Subgroup.orderOf_coe]
  exact orderOf_dvd_of_pow_eq_one hpow

theorem dvd_card_quotient_center_levi [Finite K] {C : Finset (Fin D.rank)} {i : Fin D.rank}
    (hi : i ∈ C) (hZ : center ↥(rankOne D.rootGroup i) = ⊥) {f : ℕ}
    (hf : f ∣ Nat.card (rankOne D.rootGroup i)) :
    f ∣ Nat.card (↥(levi D.rootGroup C) ⧸ center ↥(levi D.rootGroup C)) := by
  have hle : rankOne D.rootGroup i ≤ levi D.rootGroup C := rankOne_le_levi D.rootGroup hi
  refine hf.trans (Subgroup.card_dvd_of_injective
    ((QuotientGroup.mk' (center ↥(levi D.rootGroup C))).comp (Subgroup.inclusion hle)) ?_)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hxy := congrArg Subtype.val (hx (Subgroup.inclusion hle y))
  exact Subtype.ext hxy

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.BQ
