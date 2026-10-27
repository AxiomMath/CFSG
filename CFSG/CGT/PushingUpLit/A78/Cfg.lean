module

public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
public import CFSG.CGT.PushingUpLit.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.CGT.PushingUpLit.BHS
open CFSG.Assembly.RankThreeEven (projSL projSp)

structure A78Side (G : Type) [Group G] [Finite G] (L T J : Subgroup G) (e : ℕ) : Prop where
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T (Subgroup.normalizer (L : Set G))
  elem : CFSG.Open.IsElemAbelian 2 (oTwoIn (L ⊔ T))
  quot : ∃ φ : ↥(L ⊔ oTwoIn (L ⊔ T)) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e),
    Function.Surjective φ ∧ φ.ker = (oTwoIn (L ⊔ T)).subgroupOf (L ⊔ oTwoIn (L ⊔ T))
  nat : IsNatSL L (oTwoIn (L ⊔ T)) e
  sylowJ : CFSG.ABGLocalTools.IsSylowOf 2 J (L ⊔ oTwoIn (L ⊔ T))
  unique : CFSG.maximalTwoLocalsContaining ((L ⊔ T : Subgroup G) : Set G) =
    {Subgroup.normalizer (L : Set G)}

structure A78Cfg (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ) : Prop where
  kproper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G
  simple : IsSimpleGroup G
  charTwo : CFSG.Assembly.IsCharTwoType G
  two_le : 2 ≤ e
  ne_norm : Subgroup.normalizer (L₁ : Set G) ≠ Subgroup.normalizer (L₂ : Set G)
  side₁ : A78Side G L₁ T (oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T)) e
  side₂ : A78Side G L₂ T (oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T)) e

theorem A78Cfg.symm {G : Type} [Group G] [Finite G] {L₁ L₂ T : Subgroup G} {e : ℕ}
    (h : A78Cfg G L₁ L₂ T e) : A78Cfg G L₂ L₁ T e :=
  ⟨h.kproper, h.simple, h.charTwo, h.two_le, h.ne_norm.symm,
    by rw [sup_comm (oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T))]; exact h.side₂,
    by rw [sup_comm (oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T))]; exact h.side₁⟩

end CFSG.CGT.PushingUpLit.A78
