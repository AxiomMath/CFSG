module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.Open.RankThreeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def KFact64iiNPC : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (H Q M₀ : Subgroup A) (x z : A),
    p.Prime → 5 ≤ p → CFSG.Open.IsKGroup ↥H → orderOf x = p → orderOf z = p → x * z = z * x →
    x ∉ zpowers z → CFSG.ABGLocalTools.IsSylowOf p Q H → zpowers x ⊔ zpowers z ≤ Q →
    (∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) → x ∉ (frattini ↥Q).map Q.subtype →
    (∀ h ∈ H, h * z * h⁻¹ ∈ zpowers x ⊔ zpowers z → h * z * h⁻¹ ∈ zpowers z) →
    Q ≤ M₀ → M₀ ≤ H → normalizer (zpowers z : Set A) ⊓ H ≤ M₀ →
    ¬ H ≤ M₀ ⊔ rankThreePrimeCore p H →
    ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
      ¬ CFSG.HasNormalPComplement p ↥(H ⊓ centralizer ({b} : Set A))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
