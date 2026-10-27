module

public import CFSG.HardMathSupport.Foote.FamilyReduction.SL5Models
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssemblyHolds
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieChar
public import CFSG.Timmesfeld.Final.Simple
public import CFSG.HardMathSupport.Foote.FamilyReduction.Transport

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem not_comp5_oddLie {Q : Type} [Group Q] {τ : StatedLieTag} {n ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ5 : ℓ ≠ 5) (hadm : StatedLieAdmissible τ n ℓ f)
    (hQ : LieModel Q τ n ℓ f) : ¬ Comp5 Q := by
  rintro ⟨α, hα, K, hK, ⟨eK⟩⟩
  rcases CFSG.ComponentClassification.CatLeafProof.gls3OddLieAutComponentsInput_holds Q τ n ℓ f
      hℓ hℓ2 hadm hQ α hα K hK with ⟨τ', n', f', -, hmodel'⟩ | ⟨-, -, -, hL8⟩
  · exact hℓ5 (CFSG.ComponentClassification.HarrisLit.L35.char_eq_of_pslTwo (p := 5) (m := 1)
      Nat.prime_five (by norm_num) (by norm_num) hℓ2 (lieModel_psl_two_five_of_sl5 eK.symm) hmodel')
  · exact not_isSimpleGroup_sl2_five eK.symm (CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL8)

end CFSG.HardMathSupport.Foote.FamilyReduction
