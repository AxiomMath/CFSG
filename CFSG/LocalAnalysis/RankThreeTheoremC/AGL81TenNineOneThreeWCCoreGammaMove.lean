module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGamma
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup

theorem gamma_of_fuse_normalizer {G : Type*} [Group G] [Finite G] {T : Subgroup G} {a : G}
    (haT : a ∈ T) (hoa : orderOf a = 3)
    (h : ∃ n ∈ normalizer (T : Set G), n * a * n⁻¹ ∉ zpowers a) :
    ∃ (R : Subgroup G) (n : G), R ≤ T ∧ ¬ IsCyclic R ∧ n ∈ normalizer (R : Set G) ∧
      n * a * n⁻¹ ∈ T ∧ n * a * n⁻¹ ∉ zpowers a := by
  obtain ⟨n, hn, hout⟩ := h
  have hin : n * a * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn a).mp haT
  refine ⟨T, n, le_rfl, ?_, hn, hin, hout⟩
  refine not_isCyclic_of_mem haT hin hoa ?_ hout
  rw [show n * a * n⁻¹ = MulAut.conj n a from rfl, MulEquiv.orderOf_eq, hoa]

variable {B : Type} [Group B] [Finite B] {K : Subgroup B} [K.Normal]

theorem false_of_move_gamma (hZ : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1)
    (hinn : ∀ φ : MulAut K, (∃ m : ℕ, φ ^ 3 ^ m = 1) → ∃ g : K, ∀ x : K, φ x = g * x * g⁻¹)
    (hmove : ∀ (T : Sylow 3 K) (a : K), a ∈ (T : Subgroup K) → orderOf a = 3 →
      ∃ n ∈ normalizer ((T : Subgroup K) : Set K), n * a * n⁻¹ ∉ zpowers a)
    (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
    (A : Subgroup (MulAut.conjNormal (H := K)).range) (hA3 : Nat.card A = 3)
    (Y : Subgroup (MulAut.conjNormal (H := K)).range)
    (hY : GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y)
    (hwc : IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y) : False :=
  false_of_fuse_gamma hZ (fun _ φ hφ _ => hinn φ ⟨1, by rw [pow_one]; exact hφ⟩)
    (fun T a ha hoa _ => gamma_of_fuse_normalizer ha hoa (hmove T a ha hoa)) S A hA3 Y hY hwc

theorem false_of_transitive_gamma (hZ : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1)
    (hinn : ∀ φ : MulAut K, (∃ m : ℕ, φ ^ 3 ^ m = 1) → ∃ g : K, ∀ x : K, φ x = g * x * g⁻¹)
    (htr : ∀ (T : Sylow 3 K) (a b : K), a ∈ (T : Subgroup K) → b ∈ (T : Subgroup K) → a ≠ 1 →
      b ≠ 1 → ∃ n ∈ normalizer ((T : Subgroup K) : Set K), n * a * n⁻¹ = b)
    (h9 : ∀ T : Sylow 3 K, 3 < Nat.card (T : Subgroup K))
    (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
    (A : Subgroup (MulAut.conjNormal (H := K)).range) (hA3 : Nat.card A = 3)
    (Y : Subgroup (MulAut.conjNormal (H := K)).range)
    (hY : GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y)
    (hwc : IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y) : False :=
  false_of_move_gamma hZ hinn (move_of_transitive htr h9) S A hA3 Y hY hwc

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
