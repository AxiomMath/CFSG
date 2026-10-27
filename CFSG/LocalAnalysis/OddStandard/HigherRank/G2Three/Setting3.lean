module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

section Setting

variable {G : Type} [Group G]

@[expose] def ActsAs (L : Subgroup G) (g : G) (α : MulAut (L ⧸ center L)) : Prop :=
  ∀ x : ↥L, ∃ y : ↥L, (y : G) = g * x * g⁻¹ ∧ α (QuotientGroup.mk x) = QuotientGroup.mk y

@[expose] def Sec1.SFrame.IsLift (L : Subgroup G) (fr : SFrame G)
    (fr' : SFrame (MulAut (L ⧸ center L))) : Prop :=
  (fr.u₁ ∈ L ∧ ActsAs L fr.u₁ fr'.u₁) ∧ (fr.b₁ ∈ L ∧ ActsAs L fr.b₁ fr'.b₁) ∧
  (fr.u₂ ∈ L ∧ ActsAs L fr.u₂ fr'.u₂) ∧ (fr.b₂ ∈ L ∧ ActsAs L fr.b₂ fr'.b₂) ∧
  (fr.h₀ ∈ L ∧ ActsAs L fr.h₀ fr'.h₀)

end Setting

structure Setting3 (G : Type) [Group G] [Finite G] (L : Subgroup G) where
  fr : SFrame G
  fr' : Frame (MulAut (L ⧸ center L))
  facts : fr'.Facts (innerAut (L ⧸ center L))
  lift : fr.IsLift L fr'.toSFrame
  sylow_S : IsSylowIn 2 L fr.S
  t : G
  t_mem : t ∈ centralizer (L : Set G)
  t_order : orderOf t = 2
  R : Subgroup G
  T : Subgroup G
  sylow_R : IsSylowIn 2 (L ⊔ centIn (centralizer ({t} : Set G)) L) R
  sylow_T : IsSylowIn 2 (centralizer ({t} : Set G)) T
  S_le_R : fr.S ≤ R
  R_le_T : R ≤ T

namespace Setting3

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

@[expose] def H : Subgroup G := centralizer ({s.t} : Set G)

@[expose] def oddH : Subgroup G := (CFSG.oddCore ↥s.H).map s.H.subtype

@[expose] def tCoset (Y : Subgroup G) : Set G := {w | ∃ y ∈ Y, w = y * s.t}

@[expose] def Fact31 : Prop :=
  IsSylowIn 2 (centralizer (L : Set G)) (zpowers s.t) ∧
  centIn s.H L = zpowers s.t ⊔ s.oddH ∧
  (∀ g : G, g * s.t * g⁻¹ ∉ L) ∧
  conjClass (normalizer (cen s.R : Set G)) s.t = s.tCoset (cen s.fr.S)

@[expose] def X : Subgroup G := normalizer ((s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G)

@[expose] def C₂ : Subgroup G :=
  pCoreOf 2 (⁅centIn s.X (cen s.fr.B), normIn s.H s.fr.B⁆ ⊔ (s.fr.B ⊔ zpowers s.t))

@[expose] def T₂ : Subgroup G := s.T ⊔ s.C₂

structure Ext (s : Setting3 G L) where
  T₁ : Subgroup G
  sylow : IsSylowIn 2 (normalizer (cen s.R : Set G)) T₁
  T_le : s.T ≤ T₁

variable {s}

open scoped Classical in
@[expose] noncomputable def Ext.R₁ (e : Ext s) : Subgroup G :=
  if s.R = s.T then e.T₁ else normIn e.T₁ (closure {s.fr.a₁, s.fr.b₁})

@[expose] def Ext.FactDef (e : Ext s) : Prop :=
  (s.R ≠ s.T →
    SecProp s.T (zpowers s.t)
      (fun Y _ _ _ => ∀ P : Sylow 2 (MulAut (L ⧸ center L)), Nonempty (Y ≃* P)) ∧
    ∃ g ∈ s.T, g ∉ s.R ∧ ActsAs L g s.fr'.σ ∧ (g ^ 2 = 1 ∨ g ^ 2 = s.t)) ∧
  s.T.relIndex e.T₁ = 2 ∧ conjClass e.T₁ s.t = s.tCoset (cen s.fr.S)

@[expose] def Ext.Fact32 (e : Ext s) : Prop :=
  (s.fr.A ≤ e.T₁ ∧ (s.fr.A.subgroupOf e.T₁).Normal) ∧
  (s.fr.S ≤ e.T₁ ∧ (s.fr.S.subgroupOf e.T₁).Normal) ∧
  e.R₁ ⊓ s.T = s.R ∧ (s.R ≠ s.T → e.R₁.relIndex e.T₁ = 2)

@[expose] def Ext.Fact33 (e : Ext s) : Prop :=
  (s.X = normalizer ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) ∧
    normalizer ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) = normIn s.H s.fr.B ⊔ s.C₂ ∧
    normIn s.H s.fr.B ⊔ s.C₂ ≤ normalizer (s.fr.B : Set G)) ∧
  ⁅s.oddH, s.C₂⁆ = ⊥ ∧ s.H ⊓ s.C₂ = s.fr.B ⊔ zpowers s.t ∧
  conjClass s.C₂ s.t = s.tCoset (cen s.fr.B) ∧
  SecProp s.C₂ (s.fr.B ⊔ zpowers s.t) (fun Y _ _ π =>
    ∃ φ : Y ≃* ↥(cen s.fr.B), ∀ n ∈ normIn s.H s.fr.B, ∀ c c' : ↥s.C₂,
      (c' : G) = n * c * n⁻¹ → ((φ (π c') : ↥(cen s.fr.B)) : G) = n * (φ (π c) : G) * n⁻¹) ∧
  e.T₁ ≤ s.T₂ ∧ IsSylowIn 2 s.X s.T₂ ∧
  SecProp s.T₂ (centIn s.T (cen s.fr.B)) (fun Y _ _ π =>
    Nonempty (Y ≃* DihedralGroup 4) ∧
      {V : Subgroup Y | IsE 2 ↥V} =
        {((centIn s.T₂ (cen s.fr.B)).subgroupOf s.T₂).map π, (e.T₁.subgroupOf s.T₂).map π})

end Setting3

@[expose] def Fusion31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ s : Setting3 G L, s.Fact31

@[expose] def Fusion3Def : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ (s : Setting3 G L) (e : Setting3.Ext s), e.FactDef

@[expose] def Fusion32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ (s : Setting3 G L) (e : Setting3.Ext s), e.Fact32

@[expose] def Fusion33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ (s : Setting3 G L) (e : Setting3.Ext s), e.Fact33

end CFSG.OddStandard.HigherRank.G2Three
