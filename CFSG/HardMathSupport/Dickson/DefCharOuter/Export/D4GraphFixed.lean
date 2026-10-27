module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4GraphSigma
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.FixedDataTri

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

set_option linter.unusedSectionVars false


theorem d4_fixedData_graphOne {K : Type} [Field K] [Finite K] [CharP K 3]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (α : MulAut (adjointGroup Tag.D4 K))
    (hαdef : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1))
    (hα3 : α ^ 3 = 1) : FixedData3 (fixSubgroup α) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f, hf, hKf⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 3 ^ f := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨K₃, hF₃, hFin₃, hAlg, Fr, hK₃, hFr, ψ, φ, -, hφ3, hφo, -, hfix1, hfix2, -, -⟩ :=
    dual_data_one (ℓ := 3) hf K hKf α hα3 g a hαdef
  have hchar : CharP K₃ 3 :=
    charP_of_injective_algebraMap (algebraMap K K₃).injective 3
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :=
    finite_graphFixedRootGroup_D4 Fr
  have hφfix : FixedData3 (fixSubgroup φ) :=
    fixedData3_trialityD4_three hf hK₃ Fr hFr φ hφ3 hφo
  have hinjA : Function.Injective (baseChangeAdj (algebraMap K K₃)) := fun u u' h =>
    Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h))
  let ι' : adjointGroup Tag.D4 K →* adjointGroup Tag.D4 K₃ :=
    (ψ : adjointGroup Tag.D4 K₃ ≃* adjointGroup Tag.D4 K₃).toMonoidHom.comp
      (baseChangeAdj (algebraMap K K₃))
  have hι' : Function.Injective ι' := ψ.injective.comp hinjA
  have hmap : (fixSubgroup α).map ι' =
      (fixSubgroup φ).map (graphFixedInclusion K₃ Fr) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨y, hy1, hy2⟩ := hfix1 ⟨u, hu⟩
      exact ⟨y, hy2, hy1⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, hu⟩ := hfix2 y hy
      exact ⟨u.1, u.2, hu.symm⟩
  haveI : Finite (adjointGroup Tag.D4 K) := by
    haveI : Finite (ModGL Tag.D4 K) := finite_modGL
    infer_instance
  refine FixedData3.of_map_injective ι' hι' ?_
  rw [hmap]
  exact FixedData3.map_injective (graphFixedInclusion K₃ Fr)
    (graphFixedInclusion_injective' K₃ Fr) hφfix

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
