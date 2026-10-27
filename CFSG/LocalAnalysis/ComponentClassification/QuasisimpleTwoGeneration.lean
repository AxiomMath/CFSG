module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

open CFSG.Open

namespace CFSG.ComponentClassification.QuasisimpleTwoGeneration

theorem residual_eq_bot_of_odd_card {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : TwoResidual.subgroup G = ⊥ := by
  apply le_antisymm _ bot_le
  apply sSup_le
  intro twoSubgroup htwo
  obtain ⟨exponent, hcard⟩ := htwo.exists_card_eq
  have hcardOne : Nat.card twoSubgroup = 1 := by
    apply Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left exponent)
    · rw [hcard]
    · exact Subgroup.card_subgroup_dvd_card _
  exact (Subgroup.card_eq_one.mp hcardOne).le

theorem residual_eq_top_of_corefree {G : Type*} [Group G] [Finite G]
    (hquasisimple : IsQuasisimple G) (hcorefree : componentClassificationOddCore G = ⊥) :
    TwoResidual.subgroup G = ⊤ := by
  let : (TwoResidual.subgroup G).Characteristic := TwoResidual.characteristic G
  rcases Quasisimple.normal_le_center_or_eq_top hquasisimple (TwoResidual.subgroup G) with
    hcentral | htop
  · let : Group.IsPerfect G := ⟨hquasisimple.1⟩
    let : Nontrivial G := Quasisimple.nontrivial hquasisimple
    let sylow : Sylow 2 G := Classical.choice inferInstance
    have hsylowCentral : (sylow : Subgroup G) ≤ Subgroup.center G :=
      (TwoResidual.twoSubgroup_le _ sylow.isPGroup').trans hcentral
    let : IsMulCommutative (sylow : Subgroup G) := isMulCommutative_iff.mpr
      fun left right => Subtype.ext
        ((Subgroup.mem_center_iff.mp (hsylowCentral left.property)) right).symm
    have hnormalizer : Subgroup.normalizer (sylow : Set G) ≤
        Subgroup.centralizer (sylow : Set G) := by
      intro element _
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      exact ((Subgroup.mem_center_iff.mp (hsylowCentral hmember)) element).symm
    let transfer := MonoidHom.transferSylow sylow hnormalizer
    have htransfer : transfer = 1 := PerfectAutomorphisms.hom_eq_one_of_commutative transfer
    have hkernel : transfer.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr htransfer
    have hnotTwo : ¬ 2 ∣ Nat.card G := by
      have hnot := MonoidHom.not_dvd_card_ker_transferSylow sylow hnormalizer
      change ¬ 2 ∣ Nat.card transfer.ker at hnot
      simpa only [hkernel, Subgroup.card_top] using hnot
    have hodd : Odd (Nat.card G) := Nat.coprime_two_left.mp
      (Nat.prime_two.coprime_iff_not_dvd.mpr hnotTwo)
    have hcoreTop : (⊤ : Subgroup G) ≤ componentClassificationOddCore G :=
      OddCore.maximal G ⊤ inferInstance (by simpa only [Subgroup.card_top] using hodd)
    rw [hcorefree] at hcoreTop
    exact (not_le_of_gt (bot_lt_top : (⊥ : Subgroup G) < ⊤) hcoreTop).elim
  · exact htop

theorem even_card_central_quotient {G : Type*} [Group G] [Finite G]
    (hquasisimple : IsQuasisimple G) (hcorefree : componentClassificationOddCore G = ⊥) :
    Even (Nat.card (G ⧸ Subgroup.center G)) := by
  by_contra hnotEven
  have hnotTwo : ¬ 2 ∣ Nat.card (G ⧸ Subgroup.center G) :=
    fun hdiv => hnotEven (even_iff_two_dvd.mpr hdiv)
  have hodd : Odd (Nat.card (G ⧸ Subgroup.center G)) := Nat.coprime_two_left.mp
    (Nat.prime_two.coprime_iff_not_dvd.mpr hnotTwo)
  have hmap := TwoResidual.image_of_surjective (QuotientGroup.mk' (Subgroup.center G))
    (QuotientGroup.mk'_surjective _)
  rw [residual_eq_top_of_corefree hquasisimple hcorefree,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    residual_eq_bot_of_odd_card hodd] at hmap
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasisimple.2
  exact (not_le_of_gt (bot_lt_top : (⊥ : Subgroup (G ⧸ Subgroup.center G)) < ⊤)
    hmap.le).elim

end CFSG.ComponentClassification.QuasisimpleTwoGeneration
