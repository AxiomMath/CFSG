module

public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreIface
public import CFSG.Blueprint.Catalog

import CFSG.GH74.KGroups.PSL2
import CFSG.Walter.ReeOrder.JT.PSL24

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Blueprint

theorem oddCore_lieModel_psl_two_two_two {S : Type} [Group S] (h : LieModel S .PSL 2 2 2) :
    IsSimpleGroup S ∧ Nat.card S = 60 := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 2) 2 2
    (by norm_num) (GaloisField.card 2 2 (by norm_num)) h
  exact ⟨CFSG.Walter.JT.isSimpleGroup_of_psl24 e, CFSG.Walter.JT.card_of_psl24 e⟩

theorem oddCore_lieModel_psl_two_four {L : Type} [Group L] (h : LieModel L .PSL 2 2 4) :
    IsSimpleGroup L ∧ Nat.card L = 4080 := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 4) 2 4
    (by norm_num) (GaloisField.card 2 4 (by norm_num)) h
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]; norm_num
  constructor
  · have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; norm_num)
    exact e.isSimpleGroup
  · rw [Nat.card_congr e.toEquiv]
    have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (K := GaloisField 2 4) (CharTwo.neg_eq 1)
    have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center
      (K := GaloisField 2 4)
    rw [hK, hcenter] at hcard
    norm_num at hcard
    exact hcard

theorem odd_core_inf_ker_eq_bot_A_of_lieModel {H N : Type*} [Group H] [Finite H] [Group N]
    (ρ : H →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ) (π : H →* N) (Hh : Subgroup H)
    (hperf : commutator Hh = ⊤) (hodd : Odd (Nat.card π.ker))
    {L : Type} [Group L] (hL : LieModel L .PSL 2 2 4) (e : Hh.map π ≃* L) :
    Hh ⊓ π.ker = ⊥ ∧ Nonempty (Hh ≃* L) := by
  obtain ⟨hs, hc⟩ := oddCore_lieModel_psl_two_four hL
  have := hs
  have h := odd_core_inf_ker_eq_bot_A ρ hρ π Hh hperf hodd e.isSimpleGroup
    (by rw [Nat.card_congr e.toEquiv, hc])
  obtain ⟨e₂⟩ := oddCore_nonempty_mulEquiv_map_of_inf_ker_eq_bot π Hh h
  exact ⟨h, ⟨e₂.trans e⟩⟩

theorem odd_core_inf_ker_eq_bot_B_of_lieModel {H N : Type*} [Group H] [Finite H] [Group N]
    (ρ : H →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ) (π : H →* N) (Hh : Subgroup H)
    (hperf : commutator Hh = ⊤) (hodd : Odd (Nat.card π.ker))
    {S₁ S₂ : Type} [Group S₁] [Group S₂] (h₁ : LieModel S₁ .PSL 2 2 2)
    (h₂ : LieModel S₂ .PSL 2 2 2) (e : Hh.map π ≃* S₁ × S₂) :
    Hh ⊓ π.ker = ⊥ ∧ Nonempty (Hh ≃* S₁ × S₂) := by
  obtain ⟨hs₁, hc₁⟩ := oddCore_lieModel_psl_two_two_two h₁
  obtain ⟨hs₂, hc₂⟩ := oddCore_lieModel_psl_two_two_two h₂
  have := hs₁
  have := hs₂
  have h := odd_core_inf_ker_eq_bot_B ρ hρ π Hh hperf hodd hc₁ hc₂ e
  obtain ⟨e₂⟩ := oddCore_nonempty_mulEquiv_map_of_inf_ker_eq_bot π Hh h
  exact ⟨h, ⟨e₂.trans e⟩⟩

end CFSG.OddStandard.Seitz77
