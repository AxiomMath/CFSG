module

public import CFSG.ClassicalInvolution.Asc77.AscS22J
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

section Ab

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Hyp22FourthTwinAb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      dComp Ω K = dstarComp Ω K →
        ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃

variable {p f}

theorem hyp22FourthTwin_of_ab (h : Hyp22FourthTwinAb p f) : Hyp22FourthTwin p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hd
  by_cases heq : dComp Ω K = dstarComp Ω K
  · exact h G Ω K K' K₃ z u₁ u₂ u₃ hd heq
  · have hP : PartIHyp p f Ω := ⟨hd.stand.odd, hd.stand.five, hd.stand.hyp, hd.stand.aEmpty⟩
    exact T7V.exists_fourth_twin hd
      (fun W hW _ => thompsonGraphAll G Ω hP hd.stand.mem heq hW)

end Ab

section Wire

theorem hyp22SettingWyl_of_ab {p f : ℕ} [Fact p.Prime] (h : Hyp22FourthTwinAb p f) :
    T7V.Hyp22SettingWyl p f :=
  hyp22SettingWyl_of_fourthTwin p f (hyp22FourthTwin_of_ab h)

end Wire

end S22

end CFSG.ClassicalInvolution.Asc77
