module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXDef
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Simp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTInd
import CFSG.Walter.AStar.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem odd_card_oddCore_l34g (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem l34g_noncomm_of_simple {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hcent : center Y = ⊥) : ∃ a b : Y, a * b ≠ b * a := by
  by_contra hnab
  push Not at hnab
  have htop : center Y = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact (hnab x y).symm
  rw [htop] at hcent
  exact bot_ne_top hcent.symm

private theorem oddCore_eq_bot_of_simpleFStar {Y : Type} [Group Y] [Finite Y]
    (h : SimpleFStarQuotient Y) : CFSG.oddCore Y = ⊥ := by
  obtain ⟨hsimp, hcent⟩ := l34g_simple_of_simpleFStar h
  haveI : IsSimpleGroup Y := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore Y) with hbot | htop
  · exact hbot
  · exfalso
    have hodd : Odd (Nat.card Y) := by
      have hO := odd_card_oddCore_l34g Y
      rwa [htop, Subgroup.card_top] at hO
    exact Nat.not_even_iff_odd.mpr hodd
      (CFSG.Walter.even_card_of_isSimpleGroup (l34g_noncomm_of_simple hcent))

private theorem smallF3StarQuotient_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q']
    (e : Q ≃* Q') (h : SmallF3StarQuotient Q) : SmallF3StarQuotient Q' := by
  unfold SmallF3StarQuotient at h ⊢
  rcases h with h | h | h | h
  · exact Or.inl (LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (LieModel.of_mulEquiv e h)))

private theorem false_of_component_isSolvable_l34g {X : Type} [Group X] {K : Subgroup X}
    (hK : CFSG.IsComponent K) (hs : Group.IsSolvable ↥K) : False := by
  haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  haveI : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isSolvable ↥K hs

private theorem l34g_fix_one_eq_top (Y : Type) [Group Y] : L34GFix (1 : MulAut Y) = ⊤ := by
  ext y
  simp [l34g_mem_fix]

theorem l34g_isQuasisimple_of_starQuotient {Y : Type} [Group Y] [Finite Y]
    (hY : L34GStarQuotient Y) : CFSG.IsQuasisimple Y := by
  rcases hY with h | h
  · obtain ⟨hsimp, hcent⟩ := l34g_simple_of_simpleFStar h
    haveI : IsSimpleGroup Y := hsimp
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := Y)
      (l34g_noncomm_of_simple hcent)).1
  · exact h.1

theorem l34g_inFStar_top_of_starQuotient {Y : Type} [Group Y] [Finite Y]
    (hY : L34GStarQuotient Y) : InFStar (⊤ : Subgroup Y) := by
  have hF : IsFStarGroup Y := by
    rcases hY with h | h
    · have hSF : SimpleFStarQuotient Y := h
      have hbot := oddCore_eq_bot_of_simpleFStar hSF
      have hq := l34g_isQuasisimple_of_starQuotient (Y := Y) (Or.inl hSF)
      have e : Y ⧸ CFSG.oddCore Y ≃* Y :=
        (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
      unfold SimpleFStarQuotient at h
      rcases h with hΩ | hS
      · exact Or.inl ⟨hq, Or.inl (smallF3OmegaQuotient_of_mulEquiv e.symm hΩ)⟩
      · exact Or.inr ⟨hq, smallF3StarQuotient_of_mulEquiv e.symm hS⟩
    · obtain ⟨hq, htwo⟩ := h
      have hne : CFSG.oddCore Y ≠ ⊤ := by
        intro htop
        have hodd : Odd (Nat.card Y) := by
          have hO := odd_card_oddCore_l34g Y
          rwa [htop, Subgroup.card_top] at hO
        have h2dvd : 2 ∣ Nat.card Y := by
          have hcd := Subgroup.card_dvd_of_le (show center Y ≤ (⊤ : Subgroup Y) from le_top)
          rwa [htwo.1, Subgroup.card_top] at hcd
        exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2dvd)
      haveI : Nontrivial (Y ⧸ CFSG.oddCore Y) := QuotientGroup.nontrivial_iff.mpr hne
      have hle : CFSG.oddCore Y ≤ center Y :=
        sec63PT_oddCore_le_center hq (MulEquiv.refl (Y ⧸ CFSG.oddCore Y))
      have hoddO := odd_card_oddCore_l34g Y
      have hdvd : Nat.card (CFSG.oddCore Y) ∣ 2 := by
        rw [← htwo.1]
        exact Subgroup.card_dvd_of_le hle
      have hcard : Nat.card (CFSG.oddCore Y) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
        · exact h1
        · exact absurd (h2 ▸ hoddO) (by decide)
      have hbot : CFSG.oddCore Y = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        haveI : Subsingleton ↥(CFSG.oddCore Y) := (Nat.card_eq_one_iff_unique.mp hcard).1
        exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥(CFSG.oddCore Y)) 1)
      have e : Y ⧸ CFSG.oddCore Y ≃* Y :=
        (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
      exact Or.inl ⟨hq, Or.inr (isTwoU43_of_mulEquiv e.symm htwo)⟩
  change IsFStarGroup ↥(⊤ : Subgroup Y)
  exact isFStarGroup_of_mulEquiv Subgroup.topEquiv.symm hF

theorem l34g_isComponentIn_top_of_quasisimple {Y : Type} [Group Y] (hq : CFSG.IsQuasisimple Y) :
    IsComponentIn (⊤ : Subgroup Y) (⊤ : Subgroup Y) := by
  refine isComponentIn_of_normal le_top
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq) ?_
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.normal_top

theorem l34g_eq_top_of_isComponentIn_top {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple Y) {J : Subgroup Y} (hJ : IsComponentIn J (⊤ : Subgroup Y)) :
    J = ⊤ := by
  let X := ↥(⊤ : Subgroup Y)
  have hXq : CFSG.IsQuasisimple X :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  have hXc : CFSG.IsComponent (⊤ : Subgroup X) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hXq,
      Subgroup.IsSubnormal.top⟩
  have hK : CFSG.IsComponent (J.subgroupOf (⊤ : Subgroup Y)) := hJ.2
  rcases CFSG.LocalCores.distinct_components_commute hK hXc with h | h
  · exact le_antisymm le_top (Subgroup.subgroupOf_eq_top.mp h)
  · exfalso
    have hle : J.subgroupOf (⊤ : Subgroup Y) ≤ center X :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mp h
    exact false_of_component_isSolvable_l34g hK
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))

theorem l34g_coreKGA_one {Y : Type} [Group Y] [Finite Y] (hY : L34GStarQuotient Y)
    (B : Subgroup Y) :
    ∃ J : Subgroup Y, IsComponentIn J (L34GFix (1 : MulAut Y)) ∧ InFStar J ∧ B ≤ J := by
  refine ⟨⊤, ?_, l34g_inFStar_top_of_starQuotient hY, le_top⟩
  rw [l34g_fix_one_eq_top]
  exact l34g_isComponentIn_top_of_quasisimple (l34g_isQuasisimple_of_starQuotient hY)

theorem l34g_coreKGB_one {Y : Type} [Group Y] [Finite Y] (hY : L34GStarQuotient Y)
    {J : Subgroup Y} (hJ : IsComponentIn J (L34GFix (1 : MulAut Y))) {b : Y} (hb : b ∈ J)
    (hI : IsI4PlusIn J b) : IsI4PlusIn (⊤ : Subgroup Y) b := by
  rw [l34g_fix_one_eq_top] at hJ
  have hJtop : J = ⊤ :=
    l34g_eq_top_of_isComponentIn_top (l34g_isQuasisimple_of_starQuotient hY) hJ
  rwa [hJtop] at hI

end CFSG.OddStandard.SmallF3.Omega
