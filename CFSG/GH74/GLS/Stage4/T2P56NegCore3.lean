module

public import CFSG.GH74.GLS.Stage4.T2P56NegCore
public import CFSG.GH74.GLS.Stage4.T2P56NegWr

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank

section Core3

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem exists_J_core_neg_three (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover) (hStd : Std G)
    (hr : pRank 2 G = 3) (hSet : Ch6Setup G Gs q q z K₁ K₂ F₁ F₂)
    (hnormK : ∀ c : G, c * z = z * c →
      (∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂))
    {p : ℕ} (hNum : Ch6NumD p q q) (hq4 : q % 4 = 3) {u : G} {H : Subgroup G} {w₁ w₂ a : G}
    (cfg : Ch6NegCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q z u K₁ K₂ H w₁ w₂)
    (haN : a ∈ normalizer (H : Set G)) (ha3 : a ^ 3 ∈ H) (ha1 : a⁻¹ * z * a = u)
    (ha2 : a⁻¹ * u * a = z * u) (hw₂a : ∃ h ∈ H, w₂ * a * w₂⁻¹ = a⁻¹ * h) {y : G}
    (hyH : y ∈ H ⊓ K₁) (hyp : (orderOf y).Prime) (hyodd : Odd (orderOf y))
    (hya : a * y * a⁻¹ = y) :
    ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₂ ≤ J ∧
      (IsSLnEps 3 ↥J (-1) q ∨ IsLnEps 3 ↥J (-1) q) := by
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyp
    exact Nat.not_prime_one hyp
  have hay : a * y = y * a := by
    calc a * y = (a * y * a⁻¹) * a := by group
      _ = y * a := by rw [hya]
  obtain ⟨h₀, hh₀, hwa⟩ := hw₂a
  refine exists_J_core_neg_of_shape hL hL3 hStd hSet hnormK hNum cfg ha1 ha2 hyH hyp hyodd hya
    (Or.inr ⟨hq4, ?_⟩)
  exact hasWreathedSylow_neg hr cfg hq4 (fun g hg h2 => twoElt_mem_residual hg h2) hyH.1 hy1 hyodd
    haN ha3 ha1 ha2 hay (w := w₂) (hSet.comm y hyH.2 w₂ cfg.w₂_mem).symm
    (Subgroup.mem_normalizer_fintype cfg.w₂_normH) cfg.w₂_sq cfg.w₂_u hh₀ hwa

end Core3

end CFSG.GH74.GLS.Stage4.Rest
