module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Types
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6SmallB
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Big
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6SmallA
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6SmallC

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section KleinInn

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem gammaAut_eq_top_of_inner_outer (hF : L2Field F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) (e : K ≃* L2 F)
    {W : Subgroup (MulAut K)} {z w : MulAut K} (hzW : z ∈ W) (hwW : w ∈ W) (hz : z ∈ innAut K)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hw : w ∈ innDiagSub e) (hwI : w ∉ innAut K) (hw2 : w ^ 2 = 1)
    (hcomm : z * w = w * z) :
    CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W = ⊤ := by
  have hw1 : w ≠ 1 := fun h => hwI (by rw [h]; exact one_mem _)
  have htop := sup_fixed_eq_top_of_inner_outer hF hq e hz hz1 hz2 hw hwI hw2 hcomm
  rw [eq_top_iff, ← htop]
  exact sup_le (fixedSubgroup_le_gammaAut hzW (orderOf_eq_two_of_sq hz2 hz1))
    (fixedSubgroup_le_gammaAut hwW (orderOf_eq_two_of_sq hw2 hw1))

theorem gammaAut_eq_top_of_outer_outer (hF : L2Field F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) (e : K ≃* L2 F) (N : L2Notation e)
    {W : Subgroup (MulAut K)} {f₁ f₂ : MulAut K} (h1W : f₁ ∈ W) (h2W : f₂ ∈ W) (h1 : f₁ ^ 2 = 1)
    (h2 : f₂ ^ 2 = 1) (hD1 : f₁ ∉ innDiagSub e) (hD2 : f₂ ∉ innDiagSub e) (hne : f₁ ≠ f₂)
    (hcomm : f₁ * f₂ = f₂ * f₁) : CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W = ⊤ := by
  have h9 := card_eq_nine_of_not_mem_innDiagSub hF e hq hD1
  have hf1 : f₁ ≠ 1 := fun h => hD1 (by rw [h]; exact one_mem _)
  have hf2 : f₂ ≠ 1 := fun h => hD2 (by rw [h]; exact one_mem _)
  have htop := sup_fixed_eq_top_of_outer_outer hF h9 e N h1 h2 hD1 hD2 hne hcomm
  rw [eq_top_iff, ← htop]
  exact sup_le (fixedSubgroup_le_gammaAut h1W (orderOf_eq_two_of_sq h1 hf1))
    (fixedSubgroup_le_gammaAut h2W (orderOf_eq_two_of_sq h2 hf2))

theorem klein_le_innAut (hF : L2Field F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) (e : K ≃* L2 F) (N : L2Notation e)
    {W E : Subgroup (MulAut K)} (hEW : E ≤ W) (hE4 : Nat.card ↥E = 4) (hEsq : ∀ a ∈ E, a ^ 2 = 1)
    (hΓ : CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W ≠ ⊤) : E ≤ innAut K := by
  by_contra hnI
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    comm_of_sq_eq_one (hEsq a ha) (hEsq b hb) (hEsq _ (E.mul_mem ha hb))
  rcases exists_pair_of_klein_not_inn hF e hE4 hEsq hnI with
    ⟨z, hzE, w, hwE, hz1, hzI, hwD, hwI⟩ | ⟨f₁, hf₁E, f₂, hf₂E, hD1, hD2, hne⟩
  · exact hΓ (gammaAut_eq_top_of_inner_outer hF hq e (hEW hzE) (hEW hwE) hzI hz1 (hEsq z hzE) hwD hwI
      (hEsq w hwE) (hEc z hzE w hwE))
  · exact hΓ (gammaAut_eq_top_of_outer_outer hF hq e N (hEW hf₁E) (hEW hf₂E) (hEsq f₁ hf₁E)
      (hEsq f₂ hf₂E) hD1 hD2 hne (hEc f₁ hf₁E f₂ hf₂E))

end KleinInn

end CFSG.GH74.GLS.IVK.Proofs2
