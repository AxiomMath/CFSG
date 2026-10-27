module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def AutPSL2CentralizerInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
    Blueprint.LieModel Y .PSL 2 p f →
    (∀ k : MulAut Y, IsFieldAutPSL2 k → ∀ ι ∈ innAut Y, (ι * k) ^ 2 = 1 →
      IsFieldAutPSL2 (ι * k)) ∧
    ∀ K : Subgroup (MulAut Y), innAut Y ≤ K →
    ∀ T : Subgroup (MulAut Y), T ≤ K → (∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = T.subgroupOf K) →
    ∀ v : MulAut Y, SylowAutData T v → ∀ k ∈ K, IsFieldAutPSL2 k →
    ∀ Q : Subgroup (MulAut Y), Q ≤ K → IsPGroup 2 Q → Q ≤ centralizer {k} →
      Nat.card Q ≤ Nat.card ((T ⊓ innAut Y) ⊔ zpowers v : Subgroup (MulAut Y))

end CFSG.ComponentClassification.HarrisLit
