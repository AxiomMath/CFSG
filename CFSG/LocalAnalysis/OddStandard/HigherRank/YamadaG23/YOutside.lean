module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec6S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Core
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def HasPSL6Sylow (B : Type) [Group B] : Prop :=
  ∃ (p f : ℕ) (S : Type) (_ : Group S), p.Prime ∧ 0 < f ∧ p ^ f % 4 = 3 ∧
    CFSG.Blueprint.LieModel S .PSL 6 p f ∧
    ∃ (P : Sylow 2 B) (P' : Sylow 2 S), Nonempty (↥P ≃* ↥P')

@[expose] def Gomi1R : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Gh Zh Ah : Subgroup Γ) (t : Γ),
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
      (IsSU43 (↥Hh ⧸ CFSG.oddCore ↥Hh) ∨ HasPSL6Sylow (↥Hh ⧸ center ↥Hh))

@[expose] def FooteSylowL6 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → HasPSL6Sylow S →
    (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 4 = 3 ∧ CFSG.Blueprint.LieModel S .PSL 6 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 4 = 1 ∧ CFSG.Blueprint.LieModel S .PSU 6 p f)

@[expose] def SettingExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 → ∃ s : Setting3 G L, s.t = t

@[expose] def Y6F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.toCtx5.Facts5 → c.Facts6 → c.Four →
      ∃ (z : G) (K : Subgroup G), Case3Core G z K

end CFSG.OddStandard.HigherRank.YamadaG23
