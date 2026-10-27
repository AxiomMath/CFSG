module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAdm
public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs
public import CFSG.Open.StandardDefs
public import CFSG.Open.StatedDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsSL
public import CFSG.CGT.PushingUpLit.BHS6.OffenderNormalizes
public import CFSG.CGT.PushingUpLit.CGT6.EmbK
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.Blueprint CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (StatedClassicalModel standardIsStandardSubgroup)

section Cfg

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def LayerQ (G Y : Subgroup (MulAut V)) : Type :=
  ↥(conjClosure Y G) ⧸ Subgroup.center ↥(conjClosure Y G)

instance (G Y : Subgroup (MulAut V)) : Group (LayerQ G Y) :=
  inferInstanceAs (Group (↥(conjClosure Y G) ⧸ Subgroup.center ↥(conjClosure Y G)))

@[expose] def YSL (Y : Subgroup (MulAut V)) (f : ℕ) : Prop :=
  Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq f))

@[expose] def YSL5 (Y : Subgroup (MulAut V)) : Prop :=
  Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))

@[expose] def YAlt (Y : Subgroup (MulAut V)) (m : ℕ) : Prop :=
  Nonempty (↥Y ≃* alternatingGroup (Fin m))

@[expose] def OuterT (G T Y : Subgroup (MulAut V)) : Prop :=
  ∃ t ∈ T, orderOf t = 2 ∧ t ∉ conjClosure Y G

@[expose] def OmegaPlusType (Y : Subgroup (MulAut V)) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaPlusAct n) Y (commV Y) ⊥

@[expose] def Twin (G Y : Subgroup (MulAut V)) : Prop :=
  YSL5 Y ∧ ∃ x ∈ G, Y.map (MulAut.conj x).toMonoidHom ≠ Y ∧
    ⁅Y, Y.map (MulAut.conj x).toMonoidHom⁆ = ⊥

structure EndCfg4 (G T Y : Subgroup (MulAut V)) : Prop extends Emb4Cfg G T Y where
  hcls2 : InClassX ↥(yuHol Y) ∨
    ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥
  std : standardIsStandardSubgroup (Y.subgroupOf G) ∨ Twin G Y
  quasi : CFSG.Open.IsQuasisimple ↥(conjClosure Y G)
  fstar : generalizedFitting ↥G = (conjClosure Y G).subgroupOf G
  oddZ : Odd (Nat.card ↥(Subgroup.center ↥(conjClosure Y G)))
  irr : ∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤

end Cfg

@[expose] def SmallList (Q : Type) [Group Q] : Prop :=
  NativeSporadic.IsSporadic Q .M12 ∨ NativeSporadic.IsSporadic Q .J1 ∨
    NativeSporadic.IsSporadic Q .J2 ∨ Nonempty (Q ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨ StatedClassicalModel Q .PSL 2 5 2 ∨
    StatedClassicalModel Q .PSL 3 5 1 ∨ StatedClassicalModel Q .PSU 3 5 1

@[expose] def End4Small (P : (Q : Type) → [Group Q] → Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → YSL Y 2 → P (LayerQ G Y) → False

@[expose] def End415 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → YSL5 Y → False

@[expose] def End4Alt : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → ∀ m : ℕ, 7 ≤ m → Odd m → YAlt Y m → False

@[expose] def EndFour : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → False

@[expose] def Stage2Out : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → EndCfg4 G T Y

section Stage2

variable {V : Type} [CommGroup V] [Finite V]

structure Out49 (G Y : Subgroup (MulAut V)) : Prop where
  hcls2 : InClassX ↥(yuHol Y) ∨
    ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥
  std : standardIsStandardSubgroup (Y.subgroupOf G) ∨ Twin G Y

structure Out410 (G Y : Subgroup (MulAut V)) : Prop where
  quasi : CFSG.Open.IsQuasisimple ↥(conjClosure Y G)
  fstar : generalizedFitting ↥G = (conjClosure Y G).subgroupOf G
  oddZ : Odd (Nat.card ↥(Subgroup.center ↥(conjClosure Y G)))
  irr : ∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤

theorem endCfg4_of_outs {G T Y : Subgroup (MulAut V)} (cfg : Emb4Cfg G T Y) (h9 : Out49 G Y)
    (h10 : Out410 G Y) : EndCfg4 G T Y :=
  ⟨cfg, h9.hcls2, h9.std, h10.quasi, h10.fstar, h10.oddZ, h10.irr⟩

end Stage2

@[expose] def Step49 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → ¬ OmegaPlusType Y → Out49 G Y

@[expose] def End4OmegaPlus : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → OmegaPlusType Y → False

@[expose] def Step410 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → Out49 G Y → Out410 G Y

theorem stage2Out_of_steps (h9 : Step49) (h10 : Step410) (hΩ : End4OmegaPlus) : Stage2Out := by
  intro V _ _ hV G T Y cfg
  by_cases h : OmegaPlusType Y
  · exact (hΩ V hV G T Y cfg h).elim
  · exact endCfg4_of_outs cfg (h9 V hV G T Y cfg h) (h10 V hV G T Y cfg (h9 V hV G T Y cfg h))

theorem emb4End_of_stages (h2 : Stage2Out) (h3 : EndFour) : Emb4End :=
  fun V _ _ hV G T Y cfg => h3 V hV G T Y (h2 V hV G T Y cfg)

end CFSG.CGT.PushingUpLit.CGT6
