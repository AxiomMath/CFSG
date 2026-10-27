module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def Gomi1RKP : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Gh Zh Ah : Subgroup Γ) (t : Γ),
    (∀ H : Subgroup Γ, H ≤ Gh → CFSG.IsQuasisimple ↥H →
      CFSG.Blueprint.Catalog (↥H ⧸ center ↥H)) →
    Zh ≤ Gh → (∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x) →
    Nonempty (↥Zh ≃* Multiplicative (ZMod 4)) →
    Zh ≤ Ah → Ah ≤ Gh → Zh.relIndex Ah = 16 →
    (∀ a ∈ Ah, ∀ b ∈ Ah, ⁅a, b⁆ ∈ Zh) → (∀ a ∈ Ah, a ^ 2 ∈ Zh) →
    IsQuotIso (normIn Gh Ah) (Gh ⊓ centralizerSection Ah Zh) (Equiv.Perm (Fin 6)) →
    IsSylowIn 2 (Gh ⊓ centralizerSection Ah Zh) Ah →
    Even ((normIn Gh Ah).relIndex Gh) →
    (¬ ∀ a ∈ Ah, ∀ b ∈ Ah, a * b = b * a) →
    orderOf t = 2 → t ∈ normalizer (Gh : Set Γ) → t ∈ normalizer (Zh : Set Γ) →
    Ah ≤ Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh →
    Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh ≤ normalizer (Ah : Set Γ) →
    IsQuotIso (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh)
      (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh ⊓ (Gh ⊓ centralizerSection Ah Zh))
      ↥blockStab →
    (∀ n ∈ normIn Gh Ah, ∃ m ∈ normIn Gh Ah, ∃ c ∈ Gh ⊓ centralizerSection Ah Zh,
      n = m * c ∧ ⁅m, t⁆ ∈ Ah) →
    (∃ z ∈ Zh, ⁅z, t⁆ ≠ 1) →
    ∃ Hh : Subgroup Γ, Hh ≤ Gh ∧ (Hh.subgroupOf Gh).Characteristic ∧ CFSG.IsQuasisimple ↥Hh ∧
      Zh ≤ Hh ∧ centIn Gh Hh = Zh ⊔ (CFSG.oddCore ↥Gh).map Gh.subtype ∧
      IsSU43 (↥Hh ⧸ CFSG.oddCore ↥Hh)

end CFSG.OddStandard.HigherRank.YamadaG23
