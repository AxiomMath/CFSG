module

public import CFSG.LargeExtraspecial.S111SIIso
public import CFSG.LargeExtraspecial.S111SHMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

@[expose] def ShultF6ResidualNI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    Hyp S g → ¬ S.IsReducible → 6 ≤ S.width →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) →
    ∀ (P : Sylow 2 S.Mbar) (t : S.Mbar), (t : S.O) ∈ S.Lbar g → t ≠ 1 →
      t ∈ (P : Subgroup S.Mbar) → (∀ x ∈ (P : Subgroup S.Mbar), x * t = t * x) →
      IsMulCommutative (wcl t) → wcl t ≤ P →
      (∀ a ∈ wcl t, ∀ x : S.Mbar, x⁻¹ * a * x ∈ (P : Subgroup S.Mbar) → x⁻¹ * a * x ∈ wcl t) →
      GoldschmidtConcl S.Mbar P (wcl t) →
      (Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
        timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar) →
      (∃ s ∈ wclSet t, s ≠ t) →
      False

theorem shultF6Residual_of (h : ShultF6ResidualNI) : ShultF6Residual := by
  intro G _ _ _ S g hy hirr h6 hT P t ht ht1 htP htc hab hWP hcl hGo h55
  by_cases hni : ∃ s ∈ wclSet t, s ≠ t
  · exact h G S g hy hirr h6 hT P t ht ht1 htP htc hab hWP hcl hGo h55 hni
  · push Not at hni
    refine false_of_isolated hy hirr h6 ht (fun e => ht1 (Subtype.ext e)) fun x hx hc => ?_
    have hs : (⟨x, hx⟩ : S.Mbar) * t * (⟨x, hx⟩ : S.Mbar)⁻¹ ∈ wclSet t :=
      ⟨⟨x, hx⟩, rfl, Subtype.ext (by simpa using hc)⟩
    simpa using congrArg Subtype.val (hni _ hs)

theorem shultInput111_of_NI
    (h : ShultF6ResidualNI) : ShultInput111 :=
  shultInput111_of (shultF6Residual_of h)

end CFSG.LargeExtraspecial.S11
