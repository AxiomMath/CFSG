module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangRankOneFrame
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenConsumer
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ11.G2Seven
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.Open

set_option linter.unusedSectionVars false


theorem exists_langFrame_G2_odd (X : Type) [Field X] [Finite X] (hX : Odd (Nat.card X)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card X + 1) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (Γ E : Subgroup (ModGL Tag.G2 K₂)),
      IsLangFrame Tag.G2 K₂ p Γ E ∧ Nonempty (adjointGroup Tag.G2 X ≃* Γ) := by
  classical
  have hq5 : 5 ≤ Nat.card X := by
    have h1 : p ≤ Nat.card X + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
    obtain ⟨m, hm⟩ := hX
    omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₂, hF₂, hfin₂, hAlg, σ, hdeg, hσ⟩ := exists_quadratic_ext (K := X)
  obtain ⟨g, z, hg, -, hzdef, ⟨hz, hw⟩, hΓ, -, -, ⟨S₀, hS₀⟩, ⟨E, hEmem, hEle, hEcard, -, -⟩,
      hρ, -, hcent⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers X hX hp (by omega) hpq K₂ hdeg σ hσ
  have hGEN := g2_qplus_generation hX hq5 K₂ hdeg σ hσ hg hzdef hz hw
  have : Finite (ModGL Tag.G2 K₂) := finite_modGL
  refine ⟨K₂, hF₂, hfin₂, conjEntrywiseImage X g, E, isLangFrame_of_rankOneCentralizers hp hpq
    (fun α _ => rootSL2_injective_of_field α) S₀ hS₀ hEmem hEle hGEN hρ
    (fun a h1 h2 hk => ?_), ?_⟩
  · obtain ⟨α, hα, hk', hc, -⟩ := (hcent a h1 h2).2 hk
    exact ⟨α, hα, hk', hc⟩
  · let ψ : ModGL Tag.G2 X →* ModGL Tag.G2 K₂ :=
      (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap X K₂))
    have hψ : Function.Injective ψ :=
      (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := Tag.G2) (algebraMap X K₂))
    exact ⟨Subgroup.equivMapOfInjective (adjointGroup Tag.G2 X) ψ hψ⟩

theorem innerPlaneBalance_adjointG2_qplus_odd (X : Type) [Field X] [Finite X]
    (hX : Odd (Nat.card X)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card X + 1) :
    InnerPlaneBalance p (adjointGroup Tag.G2 X) := by
  obtain ⟨K₂, hF₂, hfin₂, Γ, E, hF, ⟨ε⟩⟩ := exists_langFrame_G2_odd X hX hp hp5 hpq
  have hinj := conj_injective_of_mulEquiv ε
    (mulAut_conj_injective_adjointGroup (τ := Tag.G2) (K := X))
  exact InnerPlaneBalance.of_mulEquiv ε (innerPlaneBalance_of_langFrame hp hF hinj)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
