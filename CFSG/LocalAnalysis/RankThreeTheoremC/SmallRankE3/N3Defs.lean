module

public import CFSG.ClassicalInvolution.Q3.Sec13EndSp4
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.ClassicalInvolution.Q3.Sec13

variable {Γ : Type} [Group Γ]

open scoped Classical in
structure PsiSpec (S : Subgroup Γ) (z : Γ) (Ψ : ↥S →* Multiplicative Sp4.V4) : Prop where
  surj : Function.Surjective Ψ
  ker_iff : ∀ s : S, Ψ s = 1 ↔ ((s : Γ) = 1 ∨ (s : Γ) = z)
  form : ∀ s s' : S, Sp4.symp (Multiplicative.toAdd (Ψ s)) (Multiplicative.toAdd (Ψ s')) =
    if (s : Γ) * s' * (s : Γ)⁻¹ * (s' : Γ)⁻¹ = 1 then 0 else 1

@[expose] def ActsAs (S Zc : Subgroup Γ) (Ψ : ↥S →* Multiplicative Sp4.V4) (g : Γ)
    (φ : Sp4.V4 ≃+ Sp4.V4) : Prop :=
  ∀ (s s' : S) (k : Γ), k ∈ Zc → g * (s : Γ) * g⁻¹ = (s' : Γ) * k →
    φ (Multiplicative.toAdd (Ψ s)) = Multiplicative.toAdd (Ψ s')

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
