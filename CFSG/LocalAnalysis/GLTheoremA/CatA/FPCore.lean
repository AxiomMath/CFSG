module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCyc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPD4
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Assembly CFSG.StandardType

section Core

variable {R : Type} [Group R] {I F : Set (MulAut R)}

theorem fixNum_eq_of_core {p : ℕ} (hp : 0 < p)
    (hodd : ∀ α : MulAut R, α ^ p = 1 → CentralMod I α →
      ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, α = u * f)
    (hls : ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, u * f ∉ I → (u * f) ^ p = 1 →
      ∃ f' ∈ F, ∃ u' ∈ I, orderOf f' = p ∧ u * f = u' * f' * u'⁻¹)
    (hcyc : ∃ f₀ : MulAut R, ∀ f ∈ F, f ∈ Subgroup.zpowers f₀)
    {α β : MulAut R} (hα : α ^ p = 1) (hβ : β ^ p = 1) (hαI : α ∉ I) (hβI : β ∉ I)
    (hcα : CentralMod I α) (hcβ : CentralMod I β) : fixNum α = fixNum β := by
  obtain ⟨f₀, hf₀⟩ := hcyc
  have key : ∀ γ : MulAut R, γ ^ p = 1 → γ ∉ I → CentralMod I γ →
      ∃ (u : MulAut R) (g : MulAut R), g ∈ F ∧ orderOf g = p ∧ γ = u * g * u⁻¹ := by
    intro γ hγ hγI hcγ
    obtain ⟨u, hu, f, hf, hγuf⟩ := hodd γ hγ hcγ
    have hnot : u * f ∉ I := hγuf ▸ hγI
    have hpow : (u * f) ^ p = 1 := hγuf ▸ hγ
    obtain ⟨f', hf', u', hu', hord, heq⟩ := hls u hu f hf hnot hpow
    exact ⟨u', f', hf', hord, hγuf.trans heq⟩
  obtain ⟨u, f, hf, hfo, rfl⟩ := key α hα hαI hcα
  obtain ⟨v, g, hg, hgo, rfl⟩ := key β hβ hβI hcβ
  rw [fixNum_conj, fixNum_conj]
  exact (fixNum_eq_of_orderOf_eq hp (hf₀ f hf) (hf₀ g hg) hfo hgo).symm

end Core

@[expose] def FixConst (p : ℕ) : LargeEvenRawCont := fun R _ I _ =>
  IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ α β : MulAut R, α ^ p = 1 → β ^ p = 1 → α ∉ I → β ∉ I → CentralMod I α → CentralMod I β →
      fixNum α = fixNum β


theorem canonFixConst {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h3 : ¬ (lab.tag = .triD4 ∧ p = 3)) :
    MI.CAll lab (FixConst p) := by
  have h := ((canonOddAutCentral hp hp2 hlab).and (canonRawFieldConj hp hp2 hlab h3)).and
    (canonFieldCyc hlab)
  refine h.mono ?_
  rintro R _ I F ⟨⟨hodd, hls⟩, hcyc⟩ hs hna α β hα hβ hαI hβI hcα hcβ
  exact fixNum_eq_of_core hp.pos (hodd hs hna) (hls hs hna) hcyc hα hβ hαI hβI hcα hcβ

end FP

end CFSG.LocalAnalysis.GLTheoremA
