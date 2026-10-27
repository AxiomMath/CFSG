module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact23Sylow
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.PermSylowTwo.SymCore
import CFSG.GroupTheory.SylowInfNormal
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.SignalizerFunctorTheorem.McBride

private theorem even_card_of_isQuasisimple {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : Even (Nat.card Q) := by
  by_contra h
  rw [Nat.not_even_iff_odd] at h
  have : Nontrivial Q := by
    have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
    exact (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q (CFSG.FeitThompson.isSolvable_of_odd_natCard _ h)

private theorem isPGroup_of_twoResidual_eq_bot {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (h : twoResidual H = ⊥) : IsPGroup 2 H := by
  intro x
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H x x.2
  rw [h, Subgroup.mem_bot] at hk
  exact ⟨k, Subtype.ext hk⟩

private theorem not_isSylowTwoOf_of_isGomiChevTwo {G : Type} [Group G] [Finite G]
    {X Y : Subgroup G} (hX : IsGomiChevTwo ↥X) (hYnorm : (Y.subgroupOf X).Normal)
    (hY : IsSylowTwoOf Y X) : False := by
  have hle : Y.subgroupOf X ≤ CFSG.pCore 2 ↥X :=
    CFSG.LieType.BorelTits.le_pCore 2 hYnorm hY.2.1.comap_subtype
  rw [hX.2.1] at hle
  have hsub : Y.subgroupOf X = ⊥ := le_bot_iff.mp hle
  have hYbot : Y = ⊥ := by
    have hd : Disjoint Y X := Subgroup.subgroupOf_eq_bot.mp hsub
    rw [disjoint_iff] at hd
    rwa [inf_eq_left.mpr hY.1] at hd
  have h2 : ¬ 2 ∣ Nat.card X := by
    have h := hY.2.2
    rw [hYbot] at h
    simpa using h
  have heven : Even (Nat.card X) := even_card_of_isQuasisimple hX.1
  rw [even_iff_two_dvd] at heven
  exact h2 heven

theorem inf_centralizer_le_of_gomiChevRadical (hRad : GomiChevRadical) {G : Type} [Group G]
    [Finite G] {B U : Subgroup G} (hB : IsGomiChevTwo ↥B)
    (hZ : B ⊓ centralizer (B : Set G) = ⊥) (hU : IsSylowTwoOf U B) :
    B ⊓ centralizer (U : Set G) ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup G := B ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf hU.1 Subgroup.le_normalizer
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 U B :=
    (CFSG.ABGLocalTools.isSylowOf_iff).mpr ⟨hU.1, hU.2.1, hU.2.2⟩
  have hPB : P < B := by
    refine lt_of_le_of_ne inf_le_left fun hEq => ?_
    have hBP : B ≤ normalizer (U : Set G) := (le_of_eq hEq.symm).trans inf_le_right
    exact not_isSylowTwoOf_of_isGomiChevTwo hB
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hU.1).mpr hBP) hU
  have hres : twoResidual (B ⊓ centralizer (pCoreOf 2 P : Set G)) = ⊥ :=
    le_bot_iff.mp ((hRad G B U P hB hSyl le_rfl hPB).2.trans (le_of_eq hZ))
  have hSylP : CFSG.ABGLocalTools.IsSylowOf 2 U P := hSyl.of_le hUP inf_le_left
  have hO2U : pCoreOf 2 P ≤ U := by
    obtain ⟨Q, hQ⟩ := hSylP.exists_sylow_eq_subgroupOf
    have : (CFSG.pCore 2 P).Normal := CFSG.pCore_normal
    have hle : CFSG.pCore 2 P ≤ (Q : Subgroup P) :=
      CFSG.pCore_isPGroup.le_sylow_of_normal Q
    rw [hQ] at hle
    rw [← Subgroup.map_subgroupOf_eq_of_le hUP]
    exact Subgroup.map_mono hle
  have hC_le : B ⊓ centralizer (U : Set G) ≤ B ⊓ centralizer (pCoreOf 2 P : Set G) :=
    inf_le_inf_left B (Subgroup.centralizer_le hO2U)
  have hCpg : IsPGroup 2 (B ⊓ centralizer (U : Set G) : Subgroup G) :=
    (isPGroup_of_twoResidual_eq_bot hres).to_le hC_le
  have hCnorm : B ⊓ centralizer (U : Set G) ≤ normalizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  have hCUpg : IsPGroup 2 (B ⊓ centralizer (U : Set G) ⊔ U : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hCpg hU.2.1 hCnorm
  exact le_sup_left.trans (PermSylowTwo.le_of_isSylowTwoOf_of_isPGroup hU le_sup_right
    (sup_le inf_le_left hU.1) hCUpg)

private theorem normalizer_inf_ne_top {G : Type} [Group G] [Finite G] {L H : Subgroup G}
    (hLc : IsGomiChevTwo ↥L)
    (hDP : IsDirectProduct (Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom)
      (normalClosure (L : Set G)))
    (hJ : IsSylowTwoOf (H ⊓ normalClosure (L : Set G)) (normalClosure (L : Set G))) :
    normalizer ((H ⊓ normalClosure (L : Set G)) : Set G) ≠ ⊤ := by
  intro htop
  have hJn : (H ⊓ normalClosure (L : Set G)).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hLmem : L ∈ Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom :=
    ⟨1, by ext y; simp⟩
  have hSylL : IsSylowTwoOf (L ⊓ (H ⊓ normalClosure (L : Set G))) L :=
    isSylowTwoOf_inf_of_normal hJ (hDP.le hLmem) (hDP.le_normalizer hLmem)
  have hLnorm : L ≤ normalizer ((L ⊓ (H ⊓ normalClosure (L : Set G)) : Subgroup G) : Set G) :=
    fun l hl => inf_normalizer_le_normalizer_inf ⟨le_normalizer hl, by
      rw [Subgroup.normalizer_eq_top_iff.mpr hJn]
      exact Subgroup.mem_top l⟩
  exact not_isSylowTwoOf_of_isGomiChevTwo hLc
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hLnorm) hSylL

private theorem inf_centralizer_le_normalClosure {G : Type} [Group G] [Finite G]
    {L H : Subgroup G} (hRad : GomiChevRadical) (hLc : IsGomiChevTwo ↥L)
    (hZ : L ⊓ centralizer (L : Set G) = ⊥)
    (hDP : IsDirectProduct (Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom)
      (normalClosure (L : Set G)))
    (hJ : IsSylowTwoOf (H ⊓ normalClosure (L : Set G)) (normalClosure (L : Set G))) :
    normalClosure (L : Set G) ⊓
      centralizer ((H ⊓ normalClosure (L : Set G)) : Set G) ≤ H ⊓ normalClosure (L : Set G) := by
  refine inf_centralizer_le (X := H ⊓ normalClosure (L : Set G)) hDP fun B hB => ?_
  obtain ⟨g, rfl⟩ := hB
  have hBc : IsGomiChevTwo ↥(L.map (MulAut.conj g).toMonoidHom) :=
    hLc.of_mulEquiv (L.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)
  have hBZ : L.map (MulAut.conj g).toMonoidHom ⊓
      centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = ⊥ :=
    map_conj_inf_centralizer_eq_bot hZ g
  have hBmem : L.map (MulAut.conj g).toMonoidHom ∈
      Set.range fun k : G => L.map (MulAut.conj k).toMonoidHom := ⟨g, rfl⟩
  have hU' : IsSylowTwoOf (L.map (MulAut.conj g).toMonoidHom ⊓
      (H ⊓ normalClosure (L : Set G))) (L.map (MulAut.conj g).toMonoidHom) :=
    isSylowTwoOf_inf_of_normal hJ (hDP.le hBmem) (hDP.le_normalizer hBmem)
  have h := inf_centralizer_le_of_gomiChevRadical hRad hBc hBZ hU'
  rw [inf_comm (H ⊓ normalClosure (L : Set G)) (L.map (MulAut.conj g).toMonoidHom)]
  exact h.trans inf_le_right

theorem exists_of_isSylowTwoOf_inf_normalClosure (hRad : GomiChevRadical) {G : Type} [Group G]
    [Finite G] {L H : Subgroup G} (hL : GomiConjugatesCommute L)
    (hZ : L ⊓ centralizer (L : Set G) = ⊥) (hLc : IsGomiChevTwo ↥L)
    (hJ : IsSylowTwoOf (H ⊓ normalClosure (L : Set G)) (normalClosure (L : Set G))) :
    ∃ M : Subgroup G, M ≠ ⊤ ∧ Odd M.index ∧ normalizer (H : Set G) ≤ M ∧
      twoResidual (M ⊓ normalClosure (L : Set G) ⊓
        centralizer (pCoreOf 2 (M ⊓ normalClosure (L : Set G)) : Set G)) = ⊥ := by
  let N : Subgroup G := normalClosure (L : Set G)
  let J : Subgroup G := H ⊓ N
  let M : Subgroup G := normalizer (J : Set G)
  have hJ' : IsSylowTwoOf J N := hJ
  have hDP : IsDirectProduct (Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom) N :=
    isDirectProduct_conj hL.commute hZ
  have hMne : M ≠ ⊤ := normalizer_inf_ne_top hLc hDP hJ'
  have hNJ : N ⊓ centralizer (J : Set G) ≤ J :=
    inf_centralizer_le_normalClosure hRad hLc hZ hDP hJ'
  have hMindex : Odd M.index := odd_index_normalizer_of_isSylowTwoOf hJ'
  have hNH : normalizer (H : Set G) ≤ M := normalizer_le_normalizer_inf_of_normal
  have hJMN : J ≤ M ⊓ N := le_inf le_normalizer inf_le_right
  have hJsubn : (J.subgroupOf (M ⊓ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJMN).mpr inf_le_left
  have hJpCore : J ≤ pCoreOf 2 (M ⊓ N) :=
    PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hJMN hJsubn hJ'.2.1
  have hCN : M ⊓ N ⊓ centralizer (pCoreOf 2 (M ⊓ N) : Set G) ≤ J :=
    (le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans (Subgroup.centralizer_le hJpCore))).trans hNJ
  exact ⟨M, hMne, hMindex, hNH, twoResidual_eq_bot_of_isPGroup (hJ'.2.1.to_le hCN)⟩

end CFSG.GroupTheory

end
