module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K}

structure LinCtx (d : Data G h) : Prop where
  gms : GMSK.GMSUnitarySharpKRankOneStatement
  gmsL : GMSK.GMSLinearStandardLayerListKRankOneStatement
  hyp : d.Hyp
  caseA : d.M₂Linear

theorem LinCtx.toCaseHyp {d : Data G h} (hl : d.LinCtx) : d.CaseHyp := ⟨hl.gms, hl.gmsL, hl.hyp⟩

namespace CaseBData

variable {d : Data G h} (c : d.CaseBData)

@[expose] def Bc : Subgroup G := (d.F ⊔ c.Kc) ⊓ d.D

@[expose] def Bt : Subgroup G := c.Bc.map (MulAut.conj d.t).toMonoidHom

@[expose] def NaturalSplit (F A A' : Subgroup G) {Y : Subgroup G} {k : Type} [Field k]
    (φ : Y ≃* SL(2, k)) : Prop :=
  A ⊔ A' = F ∧ A ⊓ A' = ⊥ ∧
    (∃ θ : (Fin 2 → k) → G, Timmesfeld.ARS.IsNaturalModule φ θ ∧ Set.range θ = (A : Set G)) ∧
    ∃ θ : (Fin 2 → k) → G, Timmesfeld.ARS.IsNaturalModule φ θ ∧ Set.range θ = (A' : Set G)

structure Sec41 : Prop where
  centerIn_eq : CFSG.centerIn (d.Uc c.S c.X) =
    d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G)
  card : Nat.card (CFSG.centerIn (d.Uc c.S c.X)) = (2 ^ f) ^ 4
  splitY : ∃ P' : Subgroup G, P' ≤ c.X ∧
    NaturalSplit d.F (d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G))
      (d.F ⊓ centralizer (P' : Set G)) c.φY
  free : ∀ y ∈ c.Y, Odd (orderOf y) → y ≠ 1 → ∀ z ∈ d.F, y * z * y⁻¹ = z → z = 1

structure Sec42 : Prop where
  elem : CFSG.IsElementaryAbelian 2 c.Bc
  card : Nat.card c.Bc = (2 ^ f) ^ 12
  inf : c.Bc ⊓ c.Bt = d.F
  sup : c.Bc ⊔ c.Bt = d.D
  card_inf_E : Nat.card (c.Bc ⊓ d.E : Subgroup G) = (2 ^ f) ^ 8

structure Sec43Out (R : Subgroup G) : Prop where
  card_le : ∀ Y : Subgroup G, Y ≤ R → CFSG.IsElementaryAbelian 2 Y →
    Nat.card Y ≤ 4 * Nat.card (Y ⊓ c.S : Subgroup G)
  card_fix : ∀ r ∈ R, r ∉ c.S → ∀ Z : Subgroup G, Z ≤ c.S → CFSG.IsElementaryAbelian 2 Z →
    (∀ z ∈ Z, r * z = z * r) → Nat.card (Z ⊔ d.E : Subgroup G) ≤ (2 ^ f) ^ 2 * Nat.card d.E

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
