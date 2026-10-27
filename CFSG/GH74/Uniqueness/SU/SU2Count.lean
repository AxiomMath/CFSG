module

public import CFSG.GH74.Uniqueness.SU.SU2Defs
public import CFSG.GH74.Uniqueness.SU.SU2Sem
public import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints

public section

open Subgroup Pointwise CFSG.ShultStronglyClosedTI.CyclicSemiregular

namespace CFSG.GH74.Uniqueness.SU.SU2

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V]

namespace GOPair

variable {Y : Subgroup X}

theorem shapeK_mul_card [Finite X] [Finite V] (hGO : GOPair V Y) {Z : Subgroup X} [Z.Normal]
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZodd : Odd (Nat.card Z))
    (hZfix : ∀ v : V, (∀ z ∈ Z, z • v = v) → v = 1)
    (hfpf : ∀ y ∈ Y, y ≠ 1 → ∀ z ∈ Z, y * z = z * y → z = 1) :
    shapeK V Y * Nat.card Y = shapeN V := by
  let _ : CommGroup V := hGO.commGroup
  let _ : Module (ZMod 2) (Additive V) := Sem.zmodModule2 hGO.exp_two
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : Representation (ZMod 2) X (Additive V) :=
    (Units.coeHom (Module.End (ZMod 2) (Additive V))).comp
      ((mulAutGL 2 V).comp (MulDistribMulAction.toMulAut X V))
  have hρ : ∀ (x : X) (v : Additive V), ρ x v = Additive.ofMul (x • v.toMul) := fun _ _ => rfl
  have : FiniteDimensional (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hK : IsMulCommutative Z := ⟨⟨fun a b => Subtype.ext (hZc a.1 a.2 b.1 b.2)⟩⟩
  have hBK : Y ≤ Subgroup.normalizer (Z : Set X) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hchar : ¬ ringChar (ZMod 2) ∣ Nat.card Z := by
    rw [ZMod.ringChar_zmod_n, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hZodd
  have hfix : Representation.invariants (ρ.comp Z.subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have h1 : u.toMul = 1 := by
      apply hZfix
      intro z hz
      have := hu ⟨z, hz⟩
      rw [Representation.mem_invariants] at hu
      exact congrArg Additive.toMul (this)
    have : u = 0 := Additive.toMul.injective (by rw [h1, toMul_zero])
    rw [this]
    exact Submodule.zero_mem _
  have key := CFSG.ABGLocalTools.finrank_invariants_mul_card_of_fixedPointFree ρ hK hBK hfpf hchar
    hfix
  have hdimY : Module.finrank (ZMod 2) (Representation.invariants (ρ.comp Y.subtype)) =
      shapeK V Y := by
    have hc : Nat.card (Representation.invariants (ρ.comp Y.subtype)) =
        Nat.card (fixSub V Y) := by
      refine (Nat.card_congr (Equiv.subtypeEquiv (Additive.ofMul : V ≃ Additive V) ?_)).symm
      intro v
      rw [Representation.mem_invariants]
      constructor
      · intro hv y
        exact congrArg Additive.ofMul (hv y y.2)
      · intro hv y hy
        exact congrArg Additive.toMul (hv ⟨y, hy⟩)
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Representation.invariants (ρ.comp Y.subtype))
    rw [hc, hGO.card_fixSub, Nat.card_zmod] at h2
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  have hdimV : Module.finrank (ZMod 2) (Additive V) = shapeN V := by
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have h3 : Nat.card (Additive V) = Nat.card V := rfl
    rw [h3, hGO.card_V, Nat.card_zmod] at h2
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  rw [hdimY, hdimV] at key
  exact key

end GOPair

end CFSG.GH74.Uniqueness.SU.SU2
