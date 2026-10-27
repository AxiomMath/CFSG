module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Cent
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2SL3

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution
open scoped commutatorElement MatrixGroups

theorem two_ne_zero_of_three {F : Type} [Field F] (h3 : (3 : F) = 0) : (2 : F) ≠ 0 :=
  fun h => one_ne_zero (by linear_combination h3 - h)

namespace CentShape

variable {Y : Type} [Group Y] {C : Subgroup Y} {t : Y} {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {h3 : (3 : F₂) = 0} (P : CentShape Y C t F₁ F₂ h3)

section Card

variable [Finite F₂] (hF₂ : Nat.card F₂ = 3)
include hF₂

theorem B_mul_ne_mul {h s : Y} (hh : h ∈ P.B) (hs : s ∈ P.B) (h3' : h ^ 3 = 1) (h1 : h ≠ 1)
    (s4 : s ^ 4 = 1) (s2 : s ^ 2 ≠ 1) : h * s ≠ s * h := fun hc =>
  SL3.mul_ne_mul_of_three_four hF₂ P.eB (h := ⟨h, hh⟩) (s := ⟨s, hs⟩) (Subtype.ext h3')
    (fun h' => h1 (congrArg Subtype.val h')) (Subtype.ext s4)
    (fun h' => s2 (congrArg Subtype.val h')) (Subtype.ext hc)

theorem B_exists_conj {s q : Y} (hs : s ∈ P.B) (hq : q ∈ P.B) (s4 : s ^ 4 = 1) (s2 : s ^ 2 ≠ 1)
    (q4 : q ^ 4 = 1) (q2 : q ^ 2 ≠ 1) : ∃ g ∈ P.B, q * g = g * s := by
  obtain ⟨g, hg⟩ := SL3.exists_conj_of_four hF₂ P.eB (s := ⟨s, hs⟩) (q := ⟨q, hq⟩)
    (Subtype.ext s4) (fun h' => s2 (congrArg Subtype.val h')) (Subtype.ext q4)
    (fun h' => q2 (congrArg Subtype.val h'))
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

theorem B_exists_commutator {h : Y} (hh : h ∈ P.B) (h3' : h ^ 3 = 1) (h1 : h ≠ 1) :
    ∃ g ∈ P.B, (h * g * h⁻¹ * g⁻¹) ^ 4 = 1 ∧ h * g * h⁻¹ * g⁻¹ ≠ 1 := by
  obtain ⟨g, hg4, hg1⟩ := SL3.exists_commutator_of_three hF₂ P.eB (h := ⟨h, hh⟩)
    (Subtype.ext h3') (fun h' => h1 (congrArg Subtype.val h'))
  exact ⟨g, g.2, congrArg Subtype.val hg4, fun h' => hg1 (Subtype.ext h')⟩

theorem B_pow_four {m : Y} (hm : m ∈ P.B) (h4 : m ^ 4 ≠ 1) : (m ^ 4) ^ 3 = 1 :=
  congrArg Subtype.val (SL3.pow_four_pow_three hF₂ P.eB (m := ⟨m, hm⟩)
    (fun h' => h4 (congrArg Subtype.val h')))

end Card

@[expose] noncomputable def i : Y := (P.eB.symm (SL3.i₀ F₂) : Y)

@[expose] noncomputable def j : Y := (P.eB.symm (SL3.j₀ h3) : Y)

@[expose] noncomputable def x : Y := (P.eB.symm (SL3.x₀ F₂) : Y)

theorem pow_four_symm {Z : SL(2, F₂)} (hZ : Z ^ 2 = -1) : (P.eB.symm Z : Y) ^ 4 = 1 := by
  rw [← Subgroup.coe_pow, ← map_pow, SL3.pow_four_of_sq hZ, map_one, Subgroup.coe_one]

theorem pow_two_symm_ne {Z : SL(2, F₂)} (hZ : Z ^ 2 = -1) : (P.eB.symm Z : Y) ^ 2 ≠ 1 := by
  intro h
  apply SL3.neg_one_ne_one (two_ne_zero_of_three h3)
  have h' : P.eB.symm (Z ^ 2) = 1 := Subtype.ext (by simpa [map_pow] using h)
  rw [← hZ, ← P.eB.apply_symm_apply (Z ^ 2), h', map_one]

theorem x_pow_three : P.x ^ 3 = 1 := by
  rw [x, ← Subgroup.coe_pow, ← map_pow, SL3.x₀_pow_three h3, map_one, Subgroup.coe_one]

theorem x_ne_one : P.x ≠ 1 := by
  rw [x, Ne, ← Subgroup.coe_one, Subtype.val_inj, MulEquiv.symm_apply_eq, map_one]
  exact SL3.x₀_ne_one

theorem eq_one_or_eq_t {u : Y} (hu : u ∈ P.B) (hi : u * P.i = P.i * u) (hj : u * P.j = P.j * u) :
    u = 1 ∨ u = t := by
  have key : ∀ Z : SL(2, F₂), u * (P.eB.symm Z : Y) = (P.eB.symm Z : Y) * u →
      P.eB ⟨u, hu⟩ * Z = Z * P.eB ⟨u, hu⟩ := fun Z hZ => by
    rw [← P.eB.apply_symm_apply Z, ← map_mul, ← map_mul]
    exact congrArg P.eB (Subtype.ext hZ)
  rcases SL3.eq_one_or_eq_neg_one_of_commute (two_ne_zero_of_three h3) h3 (key _ hi) (key _ hj)
    with h | h
  · exact Or.inl (congrArg Subtype.val (P.eB.injective (h.trans (map_one _).symm)))
  · exact Or.inr (congrArg Subtype.val (P.eB.injective (h.trans P.eB_t.symm)))

end CentShape

end CFSG.ClassicalInvolution.Q3.TA3
