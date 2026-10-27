module

public import CFSG.CGT.Stroth77.Section41
public import CFSG.CGT.Stroth77.Section41HS
public import CFSG.LocalAnalysis.OddStandard.ONan76Gold

public section

namespace CFSG.CGT.Stroth77

open CFSG.ComponentClassification.HSFLit (GorensteinHarrisInput)

theorem StrothFrame.IsD.isSporadic_HS_of_stroth41_all
    (hGH : GorensteinHarrisInput) {G : Type} [Group G] [Finite G] {F : StrothFrame G}
    {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ} (h : F.IsD D dD)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hR : τ.m = τ.n → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D)
    (h227 : (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
      ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n)
    (hall : ∀ x ∈ omegaIn 1 F.A, ∀ y ∈ omegaIn 1 F.A, orderOf x = 2 → orderOf y = 2 →
      IsConj x y) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .HS := by
  obtain ⟨hτ, hS, φ, hφ, hker⟩ := h.stroth_4_1 hSN hR h227 hall
  exact h.isSporadic_HS_of_stroth41 hGH
    (fun P => OddStandard.ONan76.false_of_alperinFrame_of_gold CFSG.Goldschmidt.coreStatement P) hτ hS φ hφ hker

end CFSG.CGT.Stroth77
