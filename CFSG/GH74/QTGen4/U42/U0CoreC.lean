module

public import CFSG.GH74.QTGen4.U42.U0CoreB
public meta import CFSG.GH74.QTGen4.U42.U0CoreB
public meta import CFSG.Quasithin.H13.A5Setting
public meta import CFSG.Quasithin.Background.G2A5
public meta import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.QuasithinUnique CFSG.Quasithin.H13.A5 Subgroup

theorem conj_inr_inl (σ : Equiv.Perm (Fin 5)) (u : W5) :
    (SemidirectProduct.inr σ : Mc) * (SemidirectProduct.inl u : Mc) *
        (SemidirectProduct.inr σ : Mc)⁻¹ =
      (SemidirectProduct.inl (pact σ u) : Mc) := by
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.inv_right]

theorem conj_inl_mem_of_B {X : Subgroup Mc} (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) (h4 : σ 4 = 4) {u : W5}
    (hu : (SemidirectProduct.inl u : Mc) ∈ X) :
    (SemidirectProduct.inl (pact σ u) : Mc) ∈ X := by
  have h := hXB _ (inr_mem_Bc hσ h4) _ hu
  rwa [conj_inr_inl] at h

end CFSG.GH74.QTGen4.U42
