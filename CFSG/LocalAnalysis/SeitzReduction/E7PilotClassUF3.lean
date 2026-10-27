module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF4Perfect
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZCore
public import CFSG.LocalAnalysis.SeitzReduction.EPilotWeakF3

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)

variable {K : Type} [Field K]

theorem leviU_le_normalizer_radicalU :
    leviU K ≤ normalizer (radicalU K : Set (adjointGroup .E7 K)) := by
  have hMN : parabolicLevi .E7 K uNodes ≤
      normalizer (parabolicRadical .E7 K uNodes : Set (ModGL .E7 K)) :=
    (parabolicLevi_le_parabolicSubgroup uNodes).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical uNodes)
  have h : (parabolicLevi .E7 K uNodes).subgroupOf (adjointGroup .E7 K) ≤
      normalizer ((parabolicRadical .E7 K uNodes).subgroupOf (adjointGroup .E7 K) :
        Set (adjointGroup .E7 K)) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro y
    have hmN := mem_normalizer_iff.1 (hMN (mem_subgroupOf.1 hm)) (y : ModGL .E7 K)
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact hmN
  rw [leviU, radicalU, ← map_equiv_normalizer_eq]
  exact map_mono h

theorem radicalU_inf_leviU : radicalU K ⊓ leviU K = ⊥ := by
  rw [radicalU, leviU, ← map_inf_eq _ _ _ (MulAut.conj _).injective]
  have h : (parabolicRadical .E7 K uNodes).subgroupOf (adjointGroup .E7 K) ⊓
      (parabolicLevi .E7 K uNodes).subgroupOf (adjointGroup .E7 K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hq, hm⟩ := mem_inf.1 hx
    have h1 := mem_inf.2 ⟨mem_subgroupOf.1 hq, mem_subgroupOf.1 hm⟩
    rw [parabolicRadical_inf_parabolicLevi uNodes, mem_bot] at h1
    exact mem_bot.2 (Subtype.ext h1)
  rw [h, Subgroup.map_bot]

theorem isPGroup_radicalU [Finite K] [CharP K 2] : IsPGroup 2 (radicalU K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQC : parabolicRadical .E7 K uNodes ≤ adjointGroup .E7 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  obtain ⟨-, hQp, -⟩ :=
    (parabolic_root_radical_Levi_factors .E7 K uNodes).2.2.2.2.2.2.2.2.2.2.2.2 2
  exact (F4Pilot.isPGroup_subgroupOf_of_le hQC hQp).map _

variable (K) in
@[expose] noncomputable def uLevi : Subgroup (adjointGroup .E7 K) :=
  perfectCore (leviU K ⊓ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)))

theorem uLevi_le_leviU_inf_centralizer :
    uLevi K ≤ leviU K ⊓ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)) :=
  perfectCore_le _

theorem uLevi_le_leviU : uLevi K ≤ leviU K :=
  uLevi_le_leviU_inf_centralizer.trans inf_le_left

theorem uLevi_le_centralizer :
    uLevi K ≤ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)) :=
  uLevi_le_leviU_inf_centralizer.trans inf_le_right

theorem commutator_uLevi [Finite K] : ⁅uLevi K, uLevi K⁆ = uLevi K := by
  have : Finite (ModGL .E7 K) := finite_modGL
  exact perfectCore_perfect _

theorem uF4_le_uLevi [CharP K 2] : uF4 K ≤ uLevi K :=
  uF4_le_perfectCore_leviU_inf_centralizer

theorem highRootSL2_le_uLevi [CharP K 2] :
    (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) ≤ uLevi K :=
  highRootSL2_le_uF4.trans uF4_le_uLevi

theorem uLevi_le_normalizer_radicalU :
    uLevi K ≤ normalizer (radicalU K : Set (adjointGroup .E7 K)) :=
  uLevi_le_leviU.trans leviU_le_normalizer_radicalU

theorem uLevi_le_perfectCore_centralizer [Finite K] :
    uLevi K ≤ perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) :=
  le_perfectCore_of_perfect uLevi_le_centralizer commutator_uLevi

theorem perfectCore_centralizer_e7Rep_three_le [Finite K] [CharP K 2] :
    perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) ≤
      radicalU K ⊔ uLevi K := by
  have : Finite (ModGL .E7 K) := finite_modGL
  have hMN : leviU K ⊓ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)) ≤
      normalizer (radicalU K : Set (adjointGroup .E7 K)) :=
    inf_le_left.trans leviU_le_normalizer_radicalU
  rw [centralizer_e7Rep_three_eq]
  exact E6Pilot.perfectCore_sup_le hMN

theorem perfectCore_centralizer_e7Rep_three_eq [Finite K] [CharP K 2] :
    perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) =
      (perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) ⊓ radicalU K) ⊔
        uLevi K :=
  EPilot.perfectCore_eq_inf_sup_of_le_sup uLevi_le_normalizer_radicalU commutator_uLevi
    uLevi_le_centralizer perfectCore_centralizer_e7Rep_three_le

variable (K) in
@[expose] noncomputable def uCoreRadical : Subgroup (adjointGroup .E7 K) :=
  perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) ⊓ radicalU K

theorem perfectCore_centralizer_e7Rep_three_eq_sup [Finite K] [CharP K 2] :
    perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) =
      uCoreRadical K ⊔ uLevi K :=
  perfectCore_centralizer_e7Rep_three_eq

theorem isPGroup_uCoreRadical [Finite K] [CharP K 2] : IsPGroup 2 (uCoreRadical K) :=
  isPGroup_radicalU.to_le inf_le_right

theorem uCoreRadical_comm {a b : adjointGroup .E7 K} (ha : a ∈ uCoreRadical K)
    (hb : b ∈ uCoreRadical K) : a * b = b * a :=
  radicalU_comm (mem_inf.1 ha).2 (mem_inf.1 hb).2

theorem uLevi_le_normalizer_uCoreRadical [Finite K] :
    uLevi K ≤ normalizer (uCoreRadical K : Set (adjointGroup .E7 K)) :=
  EPilot.le_normalizer_inf_of_le_of_le_normalizer uLevi_le_normalizer_radicalU
    uLevi_le_perfectCore_centralizer

theorem disjoint_uCoreRadical_uLevi : Disjoint (uCoreRadical K) (uLevi K) :=
  EPilot.disjoint_inf_of_disjoint (disjoint_iff.2 (eq_bot_iff.2
    ((inf_le_inf_left _ uLevi_le_leviU).trans radicalU_inf_leviU.le)))

end CFSG.SeitzReduction.E7Pilot
