module

public import CFSG.LocalAnalysis.ComponentInitial.FieldNineSymmetricSixModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial

namespace FieldNine

open Equiv CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {K : Type*} [Field K] [CharP K 3] {i : K}

@[expose] def coord (i : K) (p : ZMod 3 × ZMod 3) : K :=
  ZMod.castHom (dvd_refl 3) K p.1 + ZMod.castHom (dvd_refl 3) K p.2 * i

theorem coord_add (p q : ZMod 3 × ZMod 3) : coord i (p + q) = coord i p + coord i q := by
  simp only [coord, Prod.fst_add, Prod.snd_add, map_add]
  ring

theorem coord_mul (hi : i * i = -1) (p q : ZMod 3 × ZMod 3) :
    coord i p * coord i q = coord i (mulModel p q) := by
  simp only [coord, mulModel, map_sub, map_add, map_mul]
  linear_combination (ZMod.castHom (dvd_refl 3) K p.2 * ZMod.castHom (dvd_refl 3) K q.2) * hi

theorem coord_zero : coord i 0 = 0 := by
  simp [coord]

theorem coord_neg_one : coord i (-1, 0) = -1 := by
  change ZMod.castHom (dvd_refl 3) K (-1) + ZMod.castHom (dvd_refl 3) K 0 * i = -1
  rw [map_neg, map_one, map_zero, zero_mul, add_zero]

theorem eq_zero_of_coord_eq_zero (hi : i * i = -1) {p : ZMod 3 × ZMod 3} (h : coord i p = 0) :
    p = 0 := by
  have h1 : coord i p * coord i (conjModel p) = ZMod.castHom (dvd_refl 3) K (normModel p) := by
    rw [coord_mul hi]
    simp only [coord, mulModel, conjModel, normModel, map_sub, map_add, map_mul, map_neg]
    ring
  rw [h, zero_mul, eq_comm, map_eq_zero_iff _ (ZMod.castHom (dvd_refl 3) K).injective] at h1
  exact eq_zero_of_normModel_eq_zero p h1

theorem coord_injective (hi : i * i = -1) : Function.Injective (coord i) := by
  intro p q h
  have h1 := coord_add (i := i) (p - q) q
  rw [sub_add_cancel, h] at h1
  exact sub_eq_zero.1 (eq_zero_of_coord_eq_zero hi (by linear_combination -h1))

theorem coord_bijective [Fintype K] (hi : i * i = -1) (hK : Fintype.card K = 9) :
    Function.Bijective (coord i) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨coord_injective hi, by rw [hK]; rfl⟩

@[expose] def coordEquiv [Fintype K] (hi : i * i = -1) (hK : Fintype.card K = 9) :
    ZMod 3 × ZMod 3 ≃ K :=
  Equiv.ofBijective (coord i) (coord_bijective hi hK)

@[expose] def pointEquiv [Fintype K] (hi : i * i = -1) (hK : Fintype.card K = 9) :
    Omega K ≃ Fin 10 :=
  (Equiv.optionCongr (coordEquiv hi hK)).symm.trans labelEquiv

theorem permCongr_pointEquiv [Fintype K] (hi : i * i = -1) (hK : Fintype.card K = 9)
    {g : Perm (Omega K)} {gM : Perm (Option (ZMod 3 × ZMod 3))}
    (h : ∀ y, g (Option.map (coord i) y) = Option.map (coord i) (gM y)) :
    (pointEquiv hi hK).permCongr g = labelEquiv.permCongr gM := by
  have hoc : ∀ y, Equiv.optionCongr (coordEquiv hi hK) y = Option.map (coord i) y := fun _ => rfl
  ext x
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply]
  simp only [pointEquiv, Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm, hoc, h]
  rw [← hoc, Equiv.symm_apply_apply]

theorem translation_coord (p : ZMod 3 × ZMod 3) (y : Option (ZMod 3 × ZMod 3)) :
    translation K (coord i p) (Option.map (coord i) y) =
      Option.map (coord i) (translationModel p y) := by
  cases y with
  | none => rfl
  | some q =>
    change some (coord i q + coord i p) = some (coord i (q + p))
    rw [coord_add]

theorem inversion_coord (hi : i * i = -1) (y : Option (ZMod 3 × ZMod 3)) :
    inversion K (Option.map (coord i) y) = Option.map (coord i) (inversionModel y) := by
  cases y with
  | none =>
    rw [Option.map_none, inversion_none, inversionModel_apply]
    change some 0 = some (coord i 0)
    rw [coord_zero]
  | some q =>
    by_cases hq : q = 0
    · subst hq
      rw [Option.map_some, coord_zero, inversion_zero, inversionModel_apply]
      rfl
    · have hc : coord i q ≠ 0 := fun h => hq (eq_zero_of_coord_eq_zero hi h)
      rw [Option.map_some, inversion_nonzero K _ hc, inversionModel_apply]
      simp only [inversionFun, hq, ite_false, Option.map_some]
      have h1 : coord i q * coord i (negInvModel q) = -1 := by
        rw [coord_mul hi, mulModel_negInvModel q hq]
        exact coord_neg_one
      have h2 : (coord i q)⁻¹ = -coord i (negInvModel q) :=
        inv_eq_of_mul_eq_one_right (by rw [mul_neg, h1, neg_neg])
      rw [h2, neg_neg]

theorem fieldExtension_coord (hi : i * i = -1) {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3)
    (y : Option (ZMod 3 × ZMod 3)) :
    fieldExtension K σ (Option.map (coord i) y) = Option.map (coord i) (frobeniusModel y) := by
  cases y with
  | none => rfl
  | some q =>
    change some (σ (coord i q)) = some (coord i (conjModel q))
    rw [hσ, pow_succ, sq, coord_mul hi, coord_mul hi, mulModel_mulModel_self]

variable [Fintype K] (hi : i * i = -1) (hK : Fintype.card K = 9)

include hi in
theorem permCongr_translation (b : K) :
    (pointEquiv hi hK).permCongr (translation K b) =
      translationLabel ((coordEquiv hi hK).symm b) := by
  have hb : coord i ((coordEquiv hi hK).symm b) = b := (coordEquiv hi hK).apply_symm_apply b
  conv_lhs => rw [← hb]
  exact permCongr_pointEquiv hi hK (translation_coord _)

theorem permCongr_inversion :
    (pointEquiv hi hK).permCongr (inversion K) = inversionLabel :=
  permCongr_pointEquiv hi hK (inversion_coord hi)

theorem permCongr_fieldExtension {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3) :
    (pointEquiv hi hK).permCongr (fieldExtension K σ) = frobeniusLabel :=
  permCongr_pointEquiv hi hK (fieldExtension_coord hi hσ)

theorem coordEquiv_symm_coord (p : ZMod 3 × ZMod 3) : (coordEquiv hi hK).symm (coord i p) = p :=
  (coordEquiv hi hK).symm_apply_apply p

end FieldNine

end CFSG.LocalAnalysis.ComponentInitial
