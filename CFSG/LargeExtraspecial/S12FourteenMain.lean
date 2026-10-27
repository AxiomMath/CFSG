module

public import CFSG.LargeExtraspecial.S12FourteenB
public import CFSG.LargeExtraspecial.S12DWSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

@[expose] def s12SpIsometries {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (b : LinearMap.BilinForm (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ x y, b (g x) (g y) = b x y}
  mul_mem' {g h} hg hh x y := (hg (h x) (h y)).trans (hh x y)
  one_mem' _ _ := rfl
  inv_mem' {g} hg x y := by
    have h := hg (g⁻¹ x) (g⁻¹ y)
    rw [← LinearEquiv.mul_apply, mul_inv_cancel, ← LinearEquiv.mul_apply, mul_inv_cancel] at h
    exact h.symm

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

structure S12Case2 (g : G) (t : S.O) : Prop where
  data : S.S12Case2Data g t
  model : ∃ m : ℕ, 3 ≤ m ∧
    ((∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2), (∀ x, b x x = 0) ∧
        (∀ x, (∀ y, b x y = 0) → x = 0) ∧ Nonempty (S.Xbar12 g ≃* s12SpIsometries b) ∧
        Nat.card (S.Lbar g) = 2 ^ (2 * m - 1)) ∨
      (∃ q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2), timmesfeldNondegenerate q ∧
        Nonempty (S.Xbar12 g ≃* timmesfeldOmega q) ∧ Nat.card (S.Lbar g) = 2 ^ (2 * m - 2)))

@[expose] def S12OmegaPlusEight : Prop :=
  S.width = 4 ∧
    (∃ W : Submodule (ZMod 2) S.Qt, 2 * finrank (ZMod 2) W = finrank (ZMod 2) S.Qt ∧
      ∀ v ∈ W, S.q v = 0) ∧
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q

end Setting

@[expose] def Timmesfeld36Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), 4 ≤ S.width →
    (∃ q : QuadraticForm (ZMod 2) (Fin (2 * S.width) → ZMod 2), timmesfeldNondegenerate q ∧
      (Nonempty (S.Mbar ≃* timmesfeldOmega q) ∨ Nonempty (S.Mbar ≃* timmesfeldIsometries q))) →
    S.S12OmegaPlusEight

namespace Setting

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G}

theorem timmesfeld_12_14 (h36 : Timmesfeld36Input) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) {t : S.O}
    (hS : S.S12Standing g t) (hC : S.S12Case2 g t) :
    S.IsReducible12 ∨ S.S12OmegaPlusEight := by
  by_cases hirr : S.IsReducible12
  · exact Or.inl hirr
  right
  have hcard := card_Lbar_of_case2 haQ hne (by omega) hS hC.data hirr
  obtain ⟨m, hm, hSp | hOm⟩ := hC.model
  · exfalso
    obtain ⟨-, -, -, -, hL⟩ := hSp
    rw [hL] at hcard
    have := Nat.pow_right_injective (le_refl 2) hcard
    omega
  · obtain ⟨q, hq, ⟨φ⟩, hL⟩ := hOm
    rw [hL] at hcard
    have hmn : m = S.width := by
      have := Nat.pow_right_injective (le_refl 2) hcard
      omega
    subst hmn
    exact h36 G S hn ⟨q, hq, mbar_equiv_omega_or_isometries (by omega) hq φ⟩

end Setting

end CFSG.LargeExtraspecial
