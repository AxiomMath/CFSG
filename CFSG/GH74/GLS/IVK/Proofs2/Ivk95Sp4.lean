module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Sp4Aux
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Inner

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4

namespace Ivk95Sp4

variable {F : Type} [Field F] [Finite F]

theorem isComponent_E1 (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    IsComponent ((E1 F).subgroupOf (centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))))) := by
  have hE1C : E1 F ≤ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))) :=
    (E1_le_X0 h2).trans X0_le_centralizer
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE1C).symm
    (isQuasisimple_E1 h2 h4), ?_⟩
  exact isSubnormal_subgroupOf_of_normalizes (B := X0 F) (E1_le_X0 h2)
    (fun _ hb _ ha => conj_mem_E1 h2 hb ha)
    (fun _ hc _ hb => conj_mem_map_centralizer (T1 F) hc hb)

theorem isComponent_E2 (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    IsComponent ((E2 F).subgroupOf (centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))))) := by
  have hE2C : E2 F ≤ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))) :=
    (E2_le_X0 h2).trans X0_le_centralizer
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE2C).symm
    (isQuasisimple_E2 h2 h4), ?_⟩
  exact isSubnormal_subgroupOf_of_normalizes (B := X0 F) (E2_le_X0 h2)
    (fun _ hb _ ha => conj_mem_E2 h2 hb ha)
    (fun _ hc _ hb => conj_mem_map_centralizer (T1 F) hc hb)

theorem four_le_card_of_odd (hodd : Odd (Nat.card F)) (h3 : Nat.card F ≠ 3) : 4 ≤ Nat.card F := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨k, hk⟩ := hodd
  omega

theorem false_of_u2 (hodd : Odd (Nat.card F)) (h : Ivk95Cfg (u2 F)) : False := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hle : Ez (u2 F) ≤ Lsub F := perfect_le_L h2 h.le_cent h.perfect
  by_cases h3 : Nat.card F = 3
  · have := isSolvable_Lsub_of_card_three h3
    exact h.not_solvable (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  · exact false_of_simple_between h (isSimpleGroup_Lsub (four_le_card_of_odd hodd h3)) hle
      Lsub_le_centralizer

theorem false_of_u1 (hodd : Odd (Nat.card F)) (h : Ivk95Cfg (u1 F)) : False := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hX0 : Ez (u1 F) ≤ X0 F := perfect_le_map_centralizer (T1 F) h.le_cent h.perfect
  by_cases h3 : Nat.card F = 3
  · have := isSolvable_X0_of_card_three h2 h3
    exact h.not_solvable (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hX0) (Subgroup.inclusion_injective hX0))
  have h4 : 4 ≤ Nat.card F := four_le_card_of_odd hodd h3
  have hE1C : E1 F ≤ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))) :=
    (E1_le_X0 h2).trans X0_le_centralizer
  have hE2C : E2 F ≤ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))) :=
    (E2_le_X0 h2).trans X0_le_centralizer
  have hE1K : E1 F ≤ Ez (u1 F) := by
    have := le_Ez_of_isComponent (isComponent_E1 h2 h4)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE1C] at this
  have hE2K : E2 F ≤ Ez (u1 F) := by
    have := le_Ez_of_isComponent (isComponent_E2 h2 h4)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE2C] at this
  rcases eq_or_commute_of_isComponent hE1C h.le_cent (isComponent_E1 h2 h4) h.isComponent with
    heq | hcomm
  · refine not_forall_comm_of_isQuasisimple (isQuasisimple_E2 h2 h4) fun a ha b hb => ?_
    exact commute_E1_E2 (heq ▸ hE2K ha) hb
  · exact not_forall_comm_of_isQuasisimple (isQuasisimple_E1 h2 h4)
      fun a ha b hb => hcomm a ha b (hE1K hb)

end Ivk95Sp4

theorem ivk95_sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk95Empty (fun X _ => LieModel X .PSp 2 p f) := by
  intro p f hp hp2 hf
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hJ
  have hodd : Odd (Nat.card F) := odd_card_of_card_eq hp hp2 hF
  have hzo : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz.ord
  obtain ⟨φ, hφ⟩ := exists_model_conj hodd hzo
  have hz' : Ivk95Cfg (φ (e z)) := hz.of_equiv (e.trans φ)
  rcases hφ with h | h
  · rw [h] at hz'
    exact Ivk95Sp4.false_of_u1 hodd hz'
  · rw [h] at hz'
    exact Ivk95Sp4.false_of_u2 hodd hz'

end CFSG.GH74.GLS.IVK.Proofs2
