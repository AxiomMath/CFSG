module

public import CFSG.GH74.KGroups.Sz8
public import CFSG.GH74.KGroups.CoverEven
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2Rank
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFam

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

theorem lem711_l2 :
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Lem711Empty (fun X _ => LieModel X .PSL 2 p f) := by
  intro p f hp hp2 hf X _ _ L K x y h hL
  exact h.false_of_autRank fun E hE =>
    ComponentClassification.AutL2Facts.cfL2Rank ↥L p f hp hp2 hf hL E hE

theorem lem711_l28 :
    Lem711Empty (fun X _ => LieModel X .PSL 2 2 3) := by
  intro X _ _ L K x y h hL
  exact h.false_of_fixed_solvable fun α hα2 hα1 M hM =>
    KGroups.L28.fixed_solvable hL α hα2 hα1 M hM

theorem lem711_m11 :
    Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .M11) := by
  intro X _ _ L K x y h hL
  exact h.false_of_fixed_solvable fun α hα2 hα1 M hM =>
    KGroups.M11.fixed_solvable hL α hα2 hα1 M hM

theorem lem711_sz8 :
    Lem711Empty (fun X _ => LieModel X .twistedB2 0 2 3) := by
  intro X _ _ L K x y h hL
  obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel hL
  exact h.false_of_fixed_solvable fun α hα2 hα1 M hM =>
    KGroups.Sz8.fixed_solvable e α hα2 hα1 M hM


theorem lem711_l216 :
    Lem711Empty (fun X _ => LieModel X .PSL 2 2 4) := by
  intro X _ _ L K x y h hL
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := ↥L) (f := 4) (by norm_num) hL
  have hB : GH74.Uniqueness.Bender.BenderType ↥L 4 1 1 := .linear 4 (by norm_num) e
  have hcard := hB.card_eq
  refine h.false_of_card fun hd => ?_
  rw [hcard] at hd
  norm_num at hd

theorem lem711_j1 :
    Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .J1) := by
  intro X _ _ L K x y h hJ
  obtain ⟨e0⟩ := hJ
  let e : ↥L ≃* CFSG.Open.walterJ1 := e0.trans CFSG.Walter.walterJ1EquivNative.symm
  refine h.false_of_card fun hd => ?_
  rw [Nat.card_congr e.toEquiv, CFSG.Walter.J1Props.card_walterJ1] at hd
  norm_num at hd

theorem lem711_u34 :
    Lem711Empty (fun X _ => LieModel X .PSU 3 2 2) := by
  intro X _ _ L K x y h hL
  have hS : Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 2 2 := by
    rcases hL with ⟨-, hS⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hS
    all_goals exact absurd ht (by decide)
  obtain ⟨e⟩ := (RankTwoShapes.statedClassicalModel_PSU_three_two_iff ↥L 2 le_rfl).1 hS
  have hB : GH74.Uniqueness.Bender.BenderType ↥L 2 3 _ := .unitary 2 le_rfl e
  exact h.false_of_autRank fun E hE => by
    have := (hB.card_le_of_sq_eq_one_aut E hE).1
    omega


theorem lem711_ree :
    ∀ f : ℕ, Lem711Empty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro f X _ _ L K x y h hM
  have hR : ReeTitsModel ↥L .twistedG2 3 f := by
    rcases hM with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact hR
    · exact absurd hh (by decide)
  exact h.false_of_rank_out (r := 3) (s := 0) (by norm_num)
    (fun E hE => IVK.GHInv.ree_card_elementary_le hR E hE)
    (fun E hE => IVK.GHInv.ree_card_outer_elementary hR E hE)


end CFSG.GH74.GLS
