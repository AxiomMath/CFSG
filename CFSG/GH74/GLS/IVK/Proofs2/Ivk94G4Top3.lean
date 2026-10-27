module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abOPrime

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open CFSG.GH74.GLS Subgroup
open scoped MatrixGroups

section SL2Three

theorem zmod3_eq_neg_one_of_not_isSquare : ∀ x : ZMod 3, ¬IsSquare x → x = -1 := by decide

theorem zmod3_mul_adj : ∀ p q r s : ZMod 3, p * s - q * r = -1 →
    (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) (ZMod 3)) * !![-s, q; r, -p] = 1 := by
  decide

theorem zmod3_twisted_pow_four :
    ∀ u : SL(2, ZMod 3), ∀ p q r s : ZMod 3, p * s - q * r = -1 →
      ((!![p, q; r, s] * (u : Matrix (Fin 2) (Fin 2) (ZMod 3)) * !![-s, q; r, -p]) *
        (u : Matrix (Fin 2) (Fin 2) (ZMod 3))) ^ 4 = 1 := by
  decide

theorem conjSLAut_zmod3_twisted_pow_four {g : GL (Fin 2) (ZMod 3)}
    (hg : ¬IsSquare ((Matrix.GeneralLinearGroup.det g : (ZMod 3)ˣ) : ZMod 3)) (u : SL(2, ZMod 3)) :
    (conjSLAut g u * u) ^ 4 = 1 := by
  have hdet : ((Matrix.GeneralLinearGroup.det g : (ZMod 3)ˣ) : ZMod 3) = -1 :=
    zmod3_eq_neg_one_of_not_isSquare _ hg
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hdet
  obtain ⟨p, q, r, s, hM⟩ : ∃ p q r s : ZMod 3,
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hM, Matrix.det_fin_two_of] at hdet
  have hN : ((g⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![-s, q; r, -p] := by
    rw [Matrix.coe_units_inv, hM]
    exact Matrix.inv_eq_right_inv (zmod3_mul_adj p q r s hdet)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, conjSLAut_coe, hN, hM,
    Matrix.SpecialLinearGroup.coe_one]
  exact zmod3_twisted_pow_four u p q r s hdet

end SL2Three

section OddShape

variable {Y : Type} [Group Y]

theorem ConjData.le_oPrimeResidual_zmod3 {t : Y} (ht : t * t = 1) {K : Subgroup Y}
    {e : ↥K ≃* SL(2, ZMod 3)} {g : GL (Fin 2) (ZMod 3)} (h : ConjData t K e g)
    (hg : ¬IsSquare ((Matrix.GeneralLinearGroup.det g : (ZMod 3)ˣ) : ZMod 3)) :
    K ≤ oPrimeResidual 2 Y := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htN : t ∈ oPrimeResidual 2 Y :=
    Subgroup.subset_closure ⟨1, by rw [pow_one, pow_two]; exact ht⟩
  intro x hx
  obtain ⟨y, hy, hey⟩ := conjData_iff.1 h ⟨x, hx⟩
  have hy' : (y : Y) = t * x * t⁻¹ := hy
  have hw : (y * ⟨x, hx⟩ : ↥K) ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_mul, hey, map_one]
    exact conjSLAut_zmod3_twisted_pow_four hg _
  have hw' : ((y : Y) * x) ^ 4 = 1 := by
    have h1 : (((y * ⟨x, hx⟩ : ↥K) ^ 4 : ↥K) : Y) = 1 := by rw [hw]; rfl
    rwa [Subgroup.coe_pow, Subgroup.coe_mul] at h1
  have hsq : (t * x) ^ 2 = (y : Y) * x := by
    rw [hy', hti, pow_two]
    group
  have htx : t * x ∈ oPrimeResidual 2 Y := by
    refine Subgroup.subset_closure ⟨3, ?_⟩
    rw [show 2 ^ 3 = 2 * 4 from rfl, pow_mul, hsq]
    exact hw'
  have hx' : x = t * (t * x) := by rw [← mul_assoc, ht, one_mul]
  rw [hx']
  exact mul_mem htN htx

variable {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem Shape.I₁_le_oPrimeResidual_of_card_three [Finite F₁] (S : Shape Y F₁ F₂)
    (h : Nat.card F₁ = 3) : S.I₁ ≤ oPrimeResidual 2 Y := by
  have : Fintype F₁ := Fintype.ofFinite F₁
  have hc : Fintype.card F₁ = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, h, ZMod.card]
  let σ : F₁ ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  exact (S.mapField₁ σ).act₁.le_oPrimeResidual_zmod3 S.t_sq (S.mapField₁ σ).ns₁

theorem Shape.I₁_le_oPrimeResidual_of_odd [Finite F₁] (S : Shape Y F₁ F₂)
    (h : Odd (Nat.card F₁)) : S.I₁ ≤ oPrimeResidual 2 Y := by
  have h1 : 1 < Nat.card F₁ := Finite.one_lt_card
  obtain ⟨k, hk⟩ := h
  by_cases h3 : Nat.card F₁ = 3
  · exact S.I₁_le_oPrimeResidual_of_card_three h3
  · exact le_oPrimeResidual_of_equiv S.I₁ S.e₁ (oPrimeResidual_sl2 (by omega))

end OddShape

theorem Shape.oPrimeResidual_eq_top_of_odd {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (S : Shape Y F₁ F₂) (h₁ : Odd (Nat.card F₁)) (h₂ : Odd (Nat.card F₂)) :
    oPrimeResidual 2 Y = ⊤ := by
  have hI₁ : S.I₁ ≤ oPrimeResidual 2 Y := S.I₁_le_oPrimeResidual_of_odd h₁
  have hI₂ : S.I₂ ≤ oPrimeResidual 2 Y := S.swap.I₁_le_oPrimeResidual_of_odd h₂
  have ht : S.t ∈ oPrimeResidual 2 Y :=
    Subgroup.subset_closure ⟨1, by rw [pow_one, pow_two]; exact S.t_sq⟩
  rw [eq_top_iff, ← S.gen]
  exact sup_le (sup_le hI₁ hI₂) ((Subgroup.zpowers_le).2 ht)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
