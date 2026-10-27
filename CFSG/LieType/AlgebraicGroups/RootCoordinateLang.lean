module

public import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalRegularity
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

open scoped CFSG.ConvolutionPoints

theorem exists_eq_inv_mul_of_forall_coe_eq {τ : Tag} {L : Type} [Field L]
    {S S' : MulAut (adjointGroup τ L)} (hS : ∀ x : adjointGroup τ L, ∃ h, x = h⁻¹ * S h)
    (h : ∀ g : adjointGroup τ L, (S' g : ModGL τ L) = S g) (x : adjointGroup τ L) :
    ∃ h, x = h⁻¹ * S' h := by
  have hSS : S' = S := MulEquiv.ext fun g => Subtype.ext (h g)
  rw [hSS]
  exact hS x

theorem realizedPointEquiv_pointMap_pow
    {L : Type} [Field L] [IsAlgClosed L]
    (Frc : realizedCoord Tag.G2 L →ₐc[L] realizedCoord Tag.G2 L)
    (Fr : MulAut (adjointGroup Tag.G2 L))
    (hFrc : ∀ φ, realizedPointEquiv Tag.G2 L (pointMap Frc φ) =
      Fr (realizedPointEquiv Tag.G2 L φ))
    (a : ℕ) (φ : WithConv (realizedCoord Tag.G2 L →ₐ[L] L)) :
    realizedPointEquiv Tag.G2 L (pointMap (Frc ^ a) φ) =
      (Fr ^ a) (realizedPointEquiv Tag.G2 L φ) := by
  induction a generalizing φ with
  | zero => rfl
  | succ a ih =>
    rw [pow_succ, pointMap_mul, hFrc, ih, pow_succ', MulAut.mul_apply]

theorem exceptional_Lang_root_coordinate_surjectivity
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L]
    [IsAlgClosed L] [CharP L p] :
    (∀ (τ : Tag) (e : ℕ), 1 ≤ e →
      (∃ S : MulAut (adjointGroup τ L), ∀ g, (S g : ModGL τ L) =
        Units.map (entrywiseHom (iterateFrobenius L p e)) (g : ModGL τ L)) ∧
      ∀ S : MulAut (adjointGroup τ L), (∀ g, (S g : ModGL τ L) =
        Units.map (entrywiseHom (iterateFrobenius L p e)) (g : ModGL τ L)) →
        ∀ x : adjointGroup τ L, ∃ h, x = h⁻¹ * S h) ∧
    (∀ (t : TwistTag) (e : ℕ), 1 ≤ e → ∀ j : ℤ,
      (∃ S : MulAut (adjointGroup t.tag L), ∀ g, (S g : ModGL t.tag L) = diagramMap t L ^ j *
        Units.map (entrywiseHom (iterateFrobenius L p e)) (g : ModGL t.tag L) *
          (diagramMap t L ^ j)⁻¹) ∧
      ∀ S : MulAut (adjointGroup t.tag L), (∀ g, (S g : ModGL t.tag L) = diagramMap t L ^ j *
        Units.map (entrywiseHom (iterateFrobenius L p e)) (g : ModGL t.tag L) *
          (diagramMap t L ^ j)⁻¹) →
        ∀ x : adjointGroup t.tag L, ∃ h, x = h⁻¹ * S h) ∧
    (p = 3 → ∀ Φ : MulAut (adjointGroup Tag.G2 L), IsG2Exceptional L Φ →
      ∀ Fr : MulAut (adjointGroup Tag.G2 L), (∀ g, (Fr g : ModGL Tag.G2 L) =
        Units.map (entrywiseHom (iterateFrobenius L p 1)) (g : ModGL Tag.G2 L)) →
      ∀ (a : ℕ) (x : adjointGroup Tag.G2 L), ∃ h, x = h⁻¹ * (Φ * Fr ^ a) h) := by
  refine ⟨fun τ e he => ?_, fun t e he j => ?_, fun hp Φ hΦ Fr hFr a x => ?_⟩
  · obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity p L e he).1 τ
    exact ⟨⟨S, hS⟩, fun S' hS' => exists_eq_inv_mul_of_forall_coe_eq hLang fun g => by
      rw [hS', hS]⟩
  · obtain ⟨S, hS, hLang⟩ :=
      (exceptional_all_characteristic_field_Lang_surjectivity p L e he).2 t j
    exact ⟨⟨S, hS⟩, fun S' hS' => exists_eq_inv_mul_of_forall_coe_eq hLang fun g => by
      rw [hS', hS]⟩
  · subst hp
    obtain ⟨σ, hσ, -, ⟨Frc, hFrc⟩, hall⟩ := exceptional_Lang_G2_exceptional_map_regularity L Φ hΦ
    obtain ⟨-, -, hpow⟩ := hall Frc hFrc
    obtain ⟨-, hD⟩ := hpow a
    have hFrc' : ∀ φ, realizedPointEquiv Tag.G2 L (pointMap Frc φ) =
        Fr (realizedPointEquiv Tag.G2 L φ) := fun φ => Subtype.ext (by rw [hFrc, hFr])
    obtain ⟨h, hh⟩ := exceptional_Lang_connected_twisted_orbit_surjectivity (Frc ^ a * σ)
      (m := 2) (by norm_num) (fun D hDT => by rw [sq]; exact hD D hDT)
      ((realizedPointEquiv Tag.G2 L).symm x)
    refine ⟨realizedPointEquiv Tag.G2 L h, ?_⟩
    have hx := congrArg (realizedPointEquiv Tag.G2 L) hh
    rw [MulEquiv.apply_symm_apply, map_mul, map_inv] at hx
    rw [hx, pointMap_mul, hσ, realizedPointEquiv_pointMap_pow Frc Fr hFrc', MulAut.mul_apply]

end CFSG.LieType.AlgebraicGroups
