module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf

@[expose] def InnerInv (g : A5 × A5) : Prop :=
  ∃ a : A5, a ≠ 1 ∧ a ^ 2 = 1 ∧ (g = (a, 1) ∨ g = (1, a))

variable {L L' : Type} [Group L] [Group L']

structure CoreHyp (N : Subgroup L) (N' : Subgroup L') (θ : L →* A5 × A5) (θ' : L' →* A5 × A5)
    (ψ : A5 × A5 ≃* A5 × A5) (φ : L → L') (z : L) : Prop where
  surj : Function.Surjective θ
  surj' : Function.Surjective θ'
  ker : ∀ l : L, θ l = 1 ↔ l ∈ N
  ker' : ∀ l' : L', θ' l' = 1 ↔ l' ∈ N'
  iso : IsSubIso N N' φ
  pgroup : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k = 1
  z_mem : z ∈ N
  z_ne_one : z ≠ 1
  z_central : ∀ l : L, l * z = z * l
  centre : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x = 1 ∨ x = z
  exists_compat : ∀ l : L, ∃ l' : L', θ' l' = ψ (θ l) ∧ Compat N φ l l'
  exists_compat' : ∀ l' : L', ∃ l : L, θ' l' = ψ (θ l) ∧ Compat N φ l l'
  inner_sq_ne : ∀ l : L, InnerInv (θ l) → l ^ 2 ≠ 1
  inner_sq_ne' : ∀ l' : L', InnerInv (θ' l') → l' ^ 2 ≠ 1
  inner_exists : ∀ l : L, InnerInv (θ l) → ∃ q ∈ N, (l * q) ^ 2 = z

end CFSG.EvenSporadicStandard.HNRecog.ML1
