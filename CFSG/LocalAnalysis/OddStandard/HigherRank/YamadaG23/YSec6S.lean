module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Ext26
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank.G2Three.Sec2
  CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def Ctx6.Fact61 (c : Ctx6 G L) : Prop :=
  normalizer (C0 c.e : Set G) ≤ normalizer (C1 c.e : Set G) ∧
  normalizer (C1 c.e : Set G) ≤ normalizer (AV1 c.e : Set G) ∧
  normalizer (AV1 c.e : Set G) ≤ normalizer (V1 c.e : Set G) ∧
  (normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G)).relIndex
    (normalizer (C0 c.e : Set G)) = 2 ∧
  centralizerSection (C1 c.e) (V1 c.e) = c.s.oddH ⊔ C1 c.e ∧
  SecProp (normalizer (C1 c.e : Set G)) (c.s.oddH ⊔ C1 c.e) (fun Y _ _ _ =>
    ∃ X : Subgroup (MulAut (alternatingGroup (Fin 6))),
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ≤ X ∧
        Nonempty (Y ≃* ↥X)) ∧
  IsSylowIn 2 (normalizer (C1 c.e : Set G)) (c.s.T ⊔ M3 c.s)

@[expose] def Ctx6.Fact62 (c : Ctx6 G L) : Prop := IsHSType ↥(S3 c.s)

@[expose] def Ctx6.Fact63 (c : Ctx6 G L) : Prop := c.s.R ≠ c.s.T

@[expose] def Ctx6.Facts6 (c : Ctx6 G L) : Prop := c.Fact61 ∧ c.Fact62 ∧ c.Fact63

@[expose] def Ctx6.Four1 (c : Ctx6 G L) : Prop :=
  IsQuotIso (normalizer (AV1 c.e : Set G)) (centralizerSection (AV1 c.e) (V1 c.e))
    (Equiv.Perm (Fin 6))

@[expose] def Ctx6.Four2 (c : Ctx6 G L) : Prop :=
  IsSylowIn 2 (centralizerSection (AV1 c.e) (V1 c.e)) (C1 c.e) ∧
  normalizer (AV1 c.e : Set G) =
    normalizer (C1 c.e : Set G) ⊔ centralizerSection (AV1 c.e) (V1 c.e)

@[expose] def Ctx6.Four3 (c : Ctx6 G L) : Prop :=
  IsQuotIso (normalizer (C0 c.e : Set G) ⊔ centralizerSection (AV1 c.e) (V1 c.e))
    (centralizerSection (AV1 c.e) (V1 c.e)) ↥blockStab

@[expose] def Ctx6.Four4 (c : Ctx6 G L) : Prop :=
  Even ((normalizer (AV1 c.e : Set G)).relIndex (normalizer (V1 c.e : Set G)))

@[expose] def Ctx6.Four (c : Ctx6 G L) : Prop := c.Four1 ∧ c.Four2 ∧ c.Four3 ∧ c.Four4

@[expose] def Sec61 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.Fact61

@[expose] def Sec62 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.Fact62

@[expose] def Sec63 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.Fact63

@[expose] def Sec6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.Facts6

@[expose] def Sec64a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.Four1 ∧ c.Four2 ∧ c.Four3

@[expose] def Sec64b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.Four4

@[expose] def Sec64 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.Four

theorem sec6_of (h61 : Sec61) (h62 : Sec62) (h63 : Sec63) : Sec6 :=
  fun G _ _ L hS hL c => ⟨h61 G L hS hL c, h62 G L hS hL c, h63 G L hS hL c⟩

theorem sec64_of (ha : Sec64a) (hb : Sec64b) : Sec64 :=
  fun G _ _ L hS hL c => ⟨(ha G L hS hL c).1, (ha G L hS hL c).2.1, (ha G L hS hL c).2.2,
    hb G L hS hL c⟩

end CFSG.OddStandard.HigherRank.YamadaG23
