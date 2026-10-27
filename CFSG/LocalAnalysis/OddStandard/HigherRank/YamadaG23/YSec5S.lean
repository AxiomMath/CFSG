module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def Sec5Intro : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ (s : Setting3 G L) (e : Setting3.Ext s), ¬ BranchA e →
      ∃ d : G, d ∈ C0 e ∧ orderOf d = 2 ∧ d ∉ zt s ∧ Intro5 e d

@[expose] def Sec51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx5pre G L, c.s.R ≠ c.s.T →
      ∃ g : G, g ∈ c.s.T ∧ g ∉ c.s.R ∧ ActsAs L g c.s.fr'.σ ∧ g ^ 2 = 1 ∧ g * c.d * g⁻¹ = c.d

@[expose] def Ctx5.Fact52 (c : Ctx5 G L) : Prop :=
  c.s.C₂ = M2 c.s ⊔ zpowers c.s.t ∧ M2 c.s ≠ c.s.C₂ ∧ C0 c.e ≤ c.s.C₂ ∧
  SecProp c.s.C₂ (cen c.s.fr.B) (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y))

@[expose] def Ctx5.Fact53 (c : Ctx5 G L) : Prop :=
  normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) =
      normIn c.s.H c.s.fr.A ⊔ zpowers c.d ∧
  normIn c.s.H c.s.fr.A ⊔ zpowers c.d ≤ normalizer (C0 c.e : Set G) ∧
  SecProp c.e.T₁ c.s.fr.Z (fun Y _ _ π =>
    thompsonRank (⊤ : Subgroup Y) = ((C1 c.e).subgroupOf c.e.T₁).map π)

@[expose] def Ctx5.Fact54 (c : Ctx5 G L) : Prop :=
  (normalizer ((c.s.fr.F ⊔ zpowers c.s.t : Subgroup G) : Set G) = normIn c.s.H c.s.fr.F ⊔ M3 c.s ∧
    c.s.H ⊓ M3 c.s = c.s.fr.F ∧ conjClass (M3 c.s) c.s.t = c.s.tCoset c.s.fr.F ∧
    SecProp (M3 c.s) c.s.fr.F (fun Y _ _ π =>
      ∃ φ : Y ≃* ↥c.s.fr.F, ∀ n ∈ normIn c.s.H c.s.fr.F, ∀ m m' : ↥(M3 c.s),
        (m' : G) = n * m * n⁻¹ → ((φ (π m') : ↥c.s.fr.F) : G) = n * (φ (π m) : G) * n⁻¹)) ∧
  (C3 c.s = M3 c.s ⊔ zpowers c.s.t ∧ C0 c.e ≤ C3 c.s ∧
    ⁅C1 c.e, C3 c.s⁆ ≤ c.s.fr.F ⊔ C0 c.e) ∧
  (centIn (M2 c.s) c.s.fr.F ≤ M3 c.s ∧ M2 c.s = centIn (M2 c.s) c.s.fr.F ⊔ c.s.fr.B ∧
    c.s.fr.F.relIndex (centIn (M2 c.s) c.s.fr.F) = 4 ∧ R2 c.s ≤ R3 c.s ∧
    (R2 c.s).relIndex (R3 c.s) = 2)

@[expose] def Ctx5.Fact55 (c : Ctx5 G L) : Prop :=
  c.s.R ≠ c.s.T → ∀ m ∈ M3 c.s, c.g * m * c.g⁻¹ = m

@[expose] def Ctx5.Fact56 (c : Ctx5 G L) : Prop :=
  (normalizer ((c.s.fr.E ⊔ zpowers c.s.t : Subgroup G) : Set G) = normIn c.s.H c.s.fr.E ⊔ C4 c.s ∧
    c.s.H ⊓ C4 c.s = c.s.fr.E ⊔ zpowers c.s.t ∧ conjClass (C4 c.s) c.s.t = c.s.tCoset c.s.fr.E ∧
    SecProp (C4 c.s) (c.s.fr.E ⊔ zpowers c.s.t) (fun Y _ _ π =>
      ∃ φ : Y ≃* ↥c.s.fr.E, ∀ n ∈ normIn c.s.H c.s.fr.E, ∀ m m' : ↥(C4 c.s),
        (m' : G) = n * m * n⁻¹ → ((φ (π m') : ↥c.s.fr.E) : G) = n * (φ (π m) : G) * n⁻¹)) ∧
  (C0 c.e ≤ C4 c.s ∧ ⁅C1 c.e, C4 c.s⁆ ≤ c.s.fr.E ⊔ C0 c.e)

@[expose] def Ctx5.Fact57 (c : Ctx5 G L) : Prop :=
  V1 c.e ≤ M2 c.s ∧
  ((V1 c.e = closure {c.s.fr.z, c.d} ∧ IsElemAbelian 2 (M3 c.s)) ∨
   (V1 c.e = zpowers (c.d * c.s.t) ∧ IsMulCommutative ↥(M3 c.s) ∧
    (∃ r : ℕ, Nonempty (↥(M3 c.s) ≃* (Fin r → Multiplicative (ZMod 4)))) ∧
    ∀ m ∈ M3 c.s, c.s.t * m * c.s.t⁻¹ = m⁻¹))

@[expose] def Ctx5.Facts5 (c : Ctx5 G L) : Prop :=
  c.Fact52 ∧ c.Fact53 ∧ c.Fact54 ∧ c.Fact55 ∧ c.Fact56 ∧ c.Fact57

@[expose] def Sec52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx5 G L, c.Fact52

@[expose] def Sec53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx5 G L, c.Fact53

@[expose] def Sec54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx5 G L, c.Fact54

@[expose] def Sec55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx5 G L, c.Fact55

@[expose] def Sec56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx5 G L, c.Fact56

@[expose] def Sec57 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx5 G L, c.Fact57

@[expose] def Sec5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx5 G L, c.Facts5

theorem sec5_of (h52 : Sec52) (h53 : Sec53) (h54 : Sec54) (h55 : Sec55) (h56 : Sec56)
    (h57 : Sec57) : Sec5 :=
  fun G _ _ L hS hL c => ⟨h52 G L hS hL c, h53 G L hS hL c, h54 G L hS hL c, h55 G L hS hL c,
    h56 G L hS hL c, h57 G L hS hL c⟩

end CFSG.OddStandard.HigherRank.YamadaG23
