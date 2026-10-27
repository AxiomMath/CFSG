module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13aAb
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_ncard_modEq_fixed {T : Set G} {r : G} (hr : r ^ 3 = 1)
    (hT : ∀ u ∈ T, r * u * r⁻¹ ∈ T) :
    T.ncard ≡ (T ∩ {u : G | r * u * r⁻¹ = u}).ncard [MOD 3] := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥T := Finite.of_injective (Subtype.val : ↥T → G) Subtype.val_injective
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  let f : Function.End ↥T := fun u => ⟨r * (u : G) * r⁻¹, hT u u.2⟩
  have hf : f ^ 3 = 1 := by
    funext u
    apply Subtype.ext
    show r * (r * (r * (u : G) * r⁻¹) * r⁻¹) * r⁻¹ = (u : G)
    have hr3 : r * r * r = 1 := by simpa only [pow_three'] using hr
    calc r * (r * (r * (u : G) * r⁻¹) * r⁻¹) * r⁻¹
        = (r * r * r) * (u : G) * (r * r * r)⁻¹ := by group
      _ = (u : G) := by rw [hr3]; group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥T) (f := f) (p := 3) (n := 1) hf
  have himg : (Subtype.val '' f.fixedPoints) = T ∩ {u : G | r * u * r⁻¹ = u} := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, congrArg Subtype.val hv⟩
    · rintro ⟨huT, hufix⟩
      exact ⟨⟨u, huT⟩, Subtype.ext hufix, rfl⟩
  have hcardT : Fintype.card ↥T = T.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcardF : Fintype.card f.fixedPoints = (Subtype.val '' f.fixedPoints).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [← himg, ← hcardT, ← hcardF]
  exact hmod

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
