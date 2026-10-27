module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def AutPSL2FusionInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
    Blueprint.LieModel Y .PSL 2 p f →
    ∀ K : Subgroup (MulAut Y), innAut Y ≤ K →
    ∀ T : Subgroup (MulAut Y), T ≤ K → (∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = T.subgroupOf K) →
    ∀ v : MulAut Y, SylowAutData T v →
    ∀ ι ∈ (T ⊓ innAut Y) ⊓ centralizer ((T ⊓ innAut Y : Subgroup (MulAut Y)) : Set (MulAut Y)),
      orderOf ι = 2 →
    ∀ x ∈ (T ⊓ innAut Y) ⊔ zpowers v, orderOf x = 2 →
      ∃ k ∈ K, k * x * k⁻¹ = ι ∨ k * x * k⁻¹ = v ^ (orderOf v / 2) ∨
        k * x * k⁻¹ = v ^ (orderOf v / 2) * ι

end CFSG.ComponentClassification.HarrisLit
