module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStab

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup
open CFSG.Glauberman.Dickson (h826_pglMap h826_pglMap_mk h826_pglMap_injective)

variable {F : Type} [Field F] [Finite F]

theorem isSquare_of_mem_fixed {K₀ : Subfield F} (hcard : Nat.card F = Nat.card K₀ ^ 2)
    (hodd : IsOddPrimePower (Nat.card F)) (x : K₀) : IsSquare (x : F) := by
  classical
  by_cases hx : (x : F) = 0
  · rw [hx]
    exact ⟨0, by ring⟩
  have : Fintype F := Fintype.ofFinite F
  have : Fintype K₀ := Fintype.ofFinite K₀
  have h2 : ringChar F ≠ 2 := by
    intro h
    apply two_ne_zero_of_isOddPrimePower hodd
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this
    exact_mod_cast this
  rw [FiniteField.isSquare_iff h2 hx, ← Nat.card_eq_fintype_card, hcard]
  have hx0 : x ≠ 0 := fun h => hx (by rw [h]; rfl)
  have hpow : x ^ (Fintype.card K₀ - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
  rw [← Nat.card_eq_fintype_card] at hpow
  have hrodd : Odd (Nat.card K₀) := by
    have hFodd : Odd (Nat.card F) := by
      obtain ⟨p, n, -, hpodd, -, hc⟩ := hodd
      rw [hc]
      exact hpodd.pow
    rw [hcard] at hFodd
    exact Nat.Odd.of_mul_left (by rwa [← pow_two])
  obtain ⟨k, hk⟩ := hrodd
  have e : Nat.card K₀ ^ 2 / 2 = (Nat.card K₀ - 1) * (k + 1) := by
    rw [hk]
    have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    rw [this, show 2 * k + 1 - 1 = 2 * k by omega]
    omega
  rw [e, pow_mul]
  have := congrArg (fun y : K₀ => (y : F) ^ (k + 1)) hpow
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, one_pow] at this
  exact this

theorem mem_psl2Range_of_pgl2FieldAut_fixed {σ : F ≃+* F} {K₀ : Subfield F}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    (h90 : ∀ c : F, c * σ c = 1 → ∃ y : Fˣ, (y : F) / σ y = c) (hσσ : ∀ x, σ (σ x) = x)
    (hcard : Nat.card F = Nat.card K₀ ^ 2) (hodd : IsOddPrimePower (Nat.card F))
    {g : PGL2 F} (hg : pgl2FieldAut F σ g = g) :
    g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  obtain ⟨y, rfl⟩ := mem_range_of_pgl2FieldAut_fixed hK₀ h90 hσσ hg
  obtain ⟨H₀, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  rw [h826_pglMap_mk, pgl2_mk_mem_psl2_range_iff_det_isSquare]
  have e : ((Matrix.GeneralLinearGroup.map K₀.subtype H₀ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = ((H₀ : Matrix (Fin 2) (Fin 2) K₀).det : F) := by
    change (K₀.subtype.mapMatrix (H₀ : Matrix (Fin 2) (Fin 2) K₀)).det = _
    rw [← RingHom.map_det]
    rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, e]
  exact isSquare_of_mem_fixed hcard hodd _

end CFSG.ComponentClassification.AutL2Facts
