module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangG2EvenGen
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthBase
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangG2EvenData
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenConsumer

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ11.G2Seven
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Open

set_option linter.unusedSectionVars false


theorem exists_langFrame_G2_even (hmax : MaxSL2SL2G2) (X : Type) [Field X] [Finite X] [CharP X 2]
    [IsSimpleGroup (adjointGroup Tag.G2 X)] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card X + 1) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (Γ E : Subgroup (ModGL Tag.G2 K₂)),
      IsLangFrame Tag.G2 K₂ p Γ E ∧ Nonempty (adjointGroup Tag.G2 X ≃* Γ) := by
  classical
  obtain ⟨K₂, hF₂, hfin₂, hAlg, σ, hdeg, hσ⟩ := exists_quadratic_ext (K := X)
  have : Finite (ModGL Tag.G2 K₂) := finite_modGL
  obtain ⟨P, g, hgdef, ⟨S₀, hS₀⟩, hTcomm, ⟨E, hEmem, hEle, hEcard⟩, hρ, hcent⟩ :=
    even_lang_setup hp (by omega) hpq hdeg σ hσ
  have hgen := even_G2_generation hmax hp hp5 hpq P g hgdef rfl S₀ hS₀ hTcomm hEmem hEle hEcard
    hρ hcent
  refine ⟨K₂, hF₂, hfin₂, conjEntrywiseImage X g, E, isLangFrame_of_rankOneCentralizers hp hpq
    (fun α _ => rootSL2_injective_of_field α) S₀ hS₀ hEmem hEle hgen hρ
    (fun a h1 h2 hk => (hcent a h1 h2).2 hk), ?_⟩
  let ψ : ModGL Tag.G2 X →* ModGL Tag.G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap X K₂))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := Tag.G2) (algebraMap X K₂))
  exact ⟨Subgroup.equivMapOfInjective (adjointGroup Tag.G2 X) ψ hψ⟩

theorem innerPlaneBalance_adjointG2_qplus_even (hmax : MaxSL2SL2G2) (X : Type) [Field X]
    [Finite X] [CharP X 2] [IsSimpleGroup (adjointGroup Tag.G2 X)] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card X + 1) : InnerPlaneBalance p (adjointGroup Tag.G2 X) := by
  obtain ⟨K₂, hF₂, hfin₂, Γ, E, hF, ⟨ε⟩⟩ := exists_langFrame_G2_even hmax X hp hp5 hpq
  have hinj := conj_injective_of_mulEquiv ε
    (mulAut_conj_injective_adjointGroup (τ := Tag.G2) (K := X))
  exact InnerPlaneBalance.of_mulEquiv ε (innerPlaneBalance_of_langFrame hp hF hinj)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
