module

public import CFSG.CGT.PushingUpLit.Glue.BlockInX
public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {G T E : Subgroup Γ}

theorem oTwoIn_eq_pCoreOf (E : Subgroup Γ) : oTwoIn E = pCoreOf 2 E := by
  unfold oTwoIn pCoreOf inSubgroup
  show Subgroup.map E.subtype (CFSG.pCore 2 ↥E) = Subgroup.map E.subtype (CFSG.Open.pCore 2 ↥E)
  try with_reducible rfl

theorem blockU_eq (hE : IsBTBlock G T E) : blockU E = pCoreOf 2 E := by
  unfold blockU
  rw [oTwoIn_eq_pCoreOf]
  exact hE.perfect

theorem blockZ_eq (hE : IsBTBlock G T E) :
    blockZ E = pCoreOf 2 E ⊓ Subgroup.centralizer (E : Set Γ) := by
  unfold blockZ
  rw [blockU_eq hE]

section Finite

variable [Finite Γ]

theorem pCoreOf_irred (hE : IsBTBlock G T E) (hchar : CharTwo E) (N : Subgroup Γ)
    (hCN : pCoreOf 2 E ⊓ Subgroup.centralizer (E : Set Γ) ≤ N) (hNW : N ≤ pCoreOf 2 E)
    (hNn : ∀ g ∈ E, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    N = pCoreOf 2 E ⊓ Subgroup.centralizer (E : Set Γ) ∨ N = pCoreOf 2 E := by
  have hX := Glue.isShortGroup_of_isBTBlock hE hchar
  have := blockU_irred_of_short hX N (by rwa [blockZ_eq hE]) (by rwa [blockU_eq hE]) hNn
  rwa [blockZ_eq hE, blockU_eq hE] at this

theorem inf_centralizer_lt_pCoreOf (hE : IsBTBlock G T E) (hchar : CharTwo E) :
    pCoreOf 2 E ⊓ Subgroup.centralizer (E : Set Γ) < pCoreOf 2 E := by
  have hX := Glue.isShortGroup_of_isBTBlock hE hchar
  have := blockZ_lt_of_short hX
  rwa [blockZ_eq hE, blockU_eq hE] at this

theorem pCoreOf_ne_bot (hE : IsBTBlock G T E) (hchar : CharTwo E) : pCoreOf 2 E ≠ ⊥ := by
  intro h
  have := inf_centralizer_lt_pCoreOf hE hchar
  rw [h] at this
  exact not_lt_bot this

end Finite

end CFSG.CGT.PushingUpLit.BHS6
