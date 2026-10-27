module

public import CFSG.LargeExtraspecial.S12InspW4Split
public import CFSG.LargeExtraspecial.S12InspPSLDec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Subgroup Module CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl (S : Setting G) (g : G) (t : S.O) : Prop :=
  S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
    (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
    S.S12SpSixSpin g

structure Ctx (S : Setting G) (g : G) (t : S.O) : Prop where
  haQ : g * S.z * g⁻¹ ∈ S.QG
  hne : g * S.z * g⁻¹ ≠ S.z
  hw : S.width = 4
  ht : t ∈ S.Lbar g
  htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2
  hS : S.S12Standing g t
  hred : ¬ S.IsReducible12

@[expose] def XIrred (S : Setting G) (g : G) : Prop :=
  ∀ U : Submodule (ZMod 2) S.Qt, S12InspPSL.IsInv (S.actX12 g) U → U = ⊥ ∨ U = ⊤

theorem inspW4Input_iff :
    InspW4Input ↔
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
        Ctx S g t →
        ((S.IsNondeg12 g ∧ CFSG.Timmesfeld.Outcome (S.Xbar12 g)) ∨
          (¬ S.IsNondeg12 g ∧
            S12FischerConclusion (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g))) → Concl S g t := by
  constructor
  · intro h G _ _ _ S g t hc hcls
    exact h G S g t hc.haQ hc.hne hc.hw hc.ht hc.htA hc.hS hc.hred hcls
  · intro h G _ _ _ S g t haQ hne hw ht htA hS hred hcls
    exact h G S g t ⟨haQ, hne, hw, ht, htA, hS, hred⟩ hcls

end CFSG.GF2Type.Smith1979.W4Insp
