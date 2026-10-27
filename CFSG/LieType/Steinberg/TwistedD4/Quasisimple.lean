module

public import CFSG.LieType.Steinberg.TwistedD4.Bruhat
public import CFSG.LieType.Steinberg.TwistedD4.Generation
public import CFSG.LieType.Chevalley.TwistMapFixed
public import CFSG.LieType.TitsSimplicity.Simplicity

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.TitsSimplicity

variable {K : Type} [Field K]

theorem isIndecomposable_cartan_G2 : IsIndecomposable (Tag.cartan .G2) := by
  decide +kernel

section Quasisimple

variable {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem twistedGroup_nontrivial :
    Nontrivial (twistedGroup σ) := by
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (twistedRootGroup_ne_bot hσ (β := Pi.single (ng 0) 1) (IsRoot.basis _))
  exact nontrivial_of_ne (x : twistedGroup σ) 1 fun h => hx (Subtype.ext h)

theorem twistedGroup_isQuasisimple
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K)) :
    IsQuasisimple (twistedGroup σ) := by
  have := twistedGroup_nontrivial hσ
  exact TitsSimplicity.isQuasisimple (twistedDatum_isCTGroupDatum σ hσ)
    (twistedDatum_steinbergExtras σ hσ) (twistedDatum_bruhatExtras σ)
    (twistedDatum_rootGroupCommutators σ) isIndecomposable_cartan_G2
    (twistedGroup_isPerfect hσ hSL)

end Quasisimple

theorem twistedGroup_isQuasisimple_of_card
    [Finite K] {σ : K →+* K} {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) : IsQuasisimple (twistedGroup σ) :=
  twistedGroup_isQuasisimple (sigma_three_of_card hK hσq)
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K
      (hK ▸ four_le_pow_three hq))

section Derived

variable [Finite K] (σ : K →+* K)

theorem commutator_twistedFixedGroup_eq_map
    {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) :
    ⁅twistedFixedGroup .D4 K σ, twistedFixedGroup .D4 K σ⁆ =
      (twistedGroup σ).map (adjointGroup d4 K).subtype := by
  rw [twistedGroup_eq_commutator σ hq hK hσq, Subgroup.map_commutator,
    twistedFixedGroup_eq_map]
  rfl

@[expose] def twistedGroupEquivDerived
    {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) :
    twistedGroup σ ≃* ↥⁅twistedFixedGroup .D4 K σ, twistedFixedGroup .D4 K σ⁆ :=
  (Subgroup.equivMapOfInjective (twistedGroup σ) (adjointGroup d4 K).subtype
    Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (commutator_twistedFixedGroup_eq_map σ hq hK hσq).symm)

theorem coe_twistedGroupEquivDerived
    {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) (g : twistedGroup σ) :
    ((twistedGroupEquivDerived σ hq hK hσq g :
        ↥⁅twistedFixedGroup .D4 K σ, twistedFixedGroup .D4 K σ⁆) : ModGL d4 K) =
      ((g : adjointGroup d4 K) : ModGL d4 K) :=
  rfl

theorem isQuasisimple_derived_twistedFixedGroup_D4
    {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    IsQuasisimple ↥⁅twistedFixedGroup .D4 K σ, twistedFixedGroup .D4 K σ⁆ := by
  have hQ := twistedGroup_isQuasisimple_of_card hq hK hσq
  have := twistedGroup_nontrivial (sigma_three_of_card hK hσq)
  obtain ⟨x, hx⟩ := exists_ne (1 : twistedGroup σ)
  set e := twistedGroupEquivDerived σ hq hK hσq
  exact CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := e.toMonoidHom) hQ e.surjective
    ⟨x, fun h => hx (e.injective (h.trans (map_one e).symm))⟩

end Derived

end CFSG.LieType.Steinberg.TwistedD4
