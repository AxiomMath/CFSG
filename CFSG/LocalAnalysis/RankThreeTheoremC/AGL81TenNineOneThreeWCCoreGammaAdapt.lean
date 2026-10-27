module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGamma

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup

variable {B : Type} [Group B] [Finite B] {K : Subgroup B} [K.Normal]

theorem false_of_fuse_gamma_inn (hZ : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1)
    (hinn : ∀ φ : MulAut K, (∃ m : ℕ, φ ^ 3 ^ m = 1) → ∃ g : K, ∀ x : K, φ x = g * x * g⁻¹)
    (hfuse : ∀ (T : Sylow 3 K) (a : K), a ∈ (T : Subgroup K) → orderOf a = 3 →
      (∀ t ∈ (T : Subgroup K), t * a * t⁻¹ = a) →
      ∃ (R : Subgroup K) (n : K), R ≤ (T : Subgroup K) ∧ ¬ IsCyclic R ∧
        n ∈ normalizer (R : Set K) ∧ n * a * n⁻¹ ∈ (T : Subgroup K) ∧ n * a * n⁻¹ ∉ zpowers a)
    (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
    (A : Subgroup (MulAut.conjNormal (H := K)).range) (hA3 : Nat.card A = 3)
    (Y : Subgroup (MulAut.conjNormal (H := K)).range)
    (hY : GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y)
    (hwc : IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y) : False :=
  false_of_fuse_gamma hZ (fun _ φ hφ _ => hinn φ ⟨1, by rw [pow_one]; exact hφ⟩) hfuse S A hA3
    Y hY hwc

theorem false_of_fuse_gamma_out (hZ : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1)
    (hinnT : ∀ (T : Sylow 3 K) (φ : MulAut K), (∃ m : ℕ, φ ^ 3 ^ m = 1) →
      (∀ t ∈ (T : Subgroup K), φ t = t) → ∃ g : K, ∀ x : K, φ x = g * x * g⁻¹)
    (hfuse : ∀ (T : Sylow 3 K) (a : K), a ∈ (T : Subgroup K) → orderOf a = 3 →
      (∀ t ∈ (T : Subgroup K), t * a * t⁻¹ = a) →
      ∃ (R : Subgroup K) (n : K), R ≤ (T : Subgroup K) ∧ ¬ IsCyclic R ∧
        n ∈ normalizer (R : Set K) ∧ n * a * n⁻¹ ∈ (T : Subgroup K) ∧ n * a * n⁻¹ ∉ zpowers a)
    (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
    (A : Subgroup (MulAut.conjNormal (H := K)).range) (hA3 : Nat.card A = 3)
    (Y : Subgroup (MulAut.conjNormal (H := K)).range)
    (hY : GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y)
    (hwc : IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y) : False :=
  false_of_fuse_gamma hZ (fun T φ hφ hfix => hinnT T φ ⟨1, by rw [pow_one]; exact hφ⟩ hfix)
    hfuse S A hA3 Y hY hwc

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
