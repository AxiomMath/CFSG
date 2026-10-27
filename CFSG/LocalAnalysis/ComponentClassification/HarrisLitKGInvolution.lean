module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGField
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def AutPSL2InvolutionInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
    Blueprint.LieModel Y .PSL 2 p f →
    ∀ K : Subgroup (MulAut Y), innAut Y ≤ K →
    ∀ T : Subgroup (MulAut Y), T ≤ K → (∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = T.subgroupOf K) →
    ∀ v : MulAut Y, SylowAutData T v →
      (∀ ι ∈ (T ⊓ innAut Y) ⊓
          centralizer ((T ⊓ innAut Y : Subgroup (MulAut Y)) : Set (MulAut Y)), orderOf ι = 2 →
        IsPGroup 2 (↥(K ⊓ centralizer {ι}) ⧸ pPrimeCore 2 ↥(K ⊓ centralizer {ι}))) ∧
      IsPGroup 2 (↥(K ⊓ normalizer (((T ⊓ innAut Y) ⊔ zpowers v : Subgroup (MulAut Y)) :
          Set (MulAut Y))) ⧸
        pPrimeCore 2 ↥(K ⊓ normalizer (((T ⊓ innAut Y) ⊔ zpowers v : Subgroup (MulAut Y)) :
          Set (MulAut Y)))) ∧
      ∀ α ∈ T, α ∉ (T ⊓ innAut Y) ⊔ zpowers v → α ^ 2 = 1 →
        Nonempty (↥(fixedPoints α) ≃* DihedralGroup ((p ^ f + 1) / 2)) ∧
        IsPGroup 2 (↥(K ⊓ centralizer {α}) ⧸ pPrimeCore 2 ↥(K ⊓ centralizer {α}))

end CFSG.ComponentClassification.HarrisLit
