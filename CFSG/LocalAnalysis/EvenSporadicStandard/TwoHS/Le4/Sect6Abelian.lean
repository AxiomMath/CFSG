module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Alperin
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

section Abstract

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem orderOf_eq_four_of_isConj {f x : G} (hf : orderOf f = 4) (hx : IsConj f x) :
    orderOf x = 4 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  have := MulEquiv.orderOf_eq (MulAut.conj c) f
  rw [hf] at this
  simpa [MulAut.conj_apply] using this

theorem commute_of_isConj_of_centralizer_le {f : G} (hf : orderOf f = 4)
    (hN : ∀ x : G, x * f ^ 2 = f ^ 2 * x → x * f * x⁻¹ ∈ zpowers f) {T : Subgroup G}
    (hT : IsPGroup 2 T) {x y : G} (hx : IsConj f x) (hy : IsConj f y) (hxT : x ∈ T)
    (hyT : y ∈ T) : x * y = y * x := by
  have key : ∀ g l : G, IsConj f l → l = g * f * g⁻¹ → ∀ z : G, z * (l * l) = (l * l) * z →
      z * l * z⁻¹ = l ∨ z * l * z⁻¹ = l⁻¹ := by
    intro g l hl hlg z hz
    have hz' : (g⁻¹ * z * g) * f ^ 2 = f ^ 2 * (g⁻¹ * z * g) := by
      have : z * (g * f ^ 2 * g⁻¹) = (g * f ^ 2 * g⁻¹) * z := by
        have e : l * l = g * f ^ 2 * g⁻¹ := by rw [hlg, pow_two]; group
        rwa [e] at hz
      calc (g⁻¹ * z * g) * f ^ 2 = g⁻¹ * (z * (g * f ^ 2 * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * f ^ 2 * g⁻¹) * z) * g := by rw [this]
        _ = f ^ 2 * (g⁻¹ * z * g) := by group
    have hmem := hN _ hz'
    have h4 : orderOf ((g⁻¹ * z * g) * f * (g⁻¹ * z * g)⁻¹) = 4 :=
      orderOf_eq_four_of_isConj hf (isConj_iff.2 ⟨g⁻¹ * z * g, rfl⟩)
    have hcases := eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four hf hmem h4
    have hconj : z * l * z⁻¹ = g * ((g⁻¹ * z * g) * f * (g⁻¹ * z * g)⁻¹) * g⁻¹ := by
      rw [hlg]; group
    rcases hcases with h | h
    · left; rw [hconj, h, hlg]
    · right; rw [hconj, h, hlg]; group
  set Λ : Set G := {l | l ∈ T ∧ IsConj f l} with hΛ
  have hΛ4 : ∀ l ∈ Λ, l ∈ T ∧ orderOf l = 4 := fun l hl =>
    ⟨hl.1, orderOf_eq_four_of_isConj hf hl.2⟩
  have hΛinv : ∀ l ∈ Λ, ∀ t ∈ T, t * l * t⁻¹ ∈ Λ := fun l hl t ht =>
    ⟨T.mul_mem (T.mul_mem ht hl.1) (T.inv_mem ht), hl.2.trans (isConj_iff.2 ⟨t, rfl⟩)⟩
  have hΛ3 : ∀ l ∈ Λ, ∀ m ∈ Λ, l * l = m * m → m = l ∨ m = l⁻¹ := by
    intro l hl m hm hlm
    obtain ⟨g, hg⟩ := isConj_iff.1 hl.2
    obtain ⟨h, hh⟩ := isConj_iff.1 hm.2
    have hcomm : (h⁻¹ * g) * f ^ 2 = f ^ 2 * (h⁻¹ * g) := by
      have e1 : l * l = g * f ^ 2 * g⁻¹ := by rw [← hg, pow_two]; group
      have e2 : m * m = h * f ^ 2 * h⁻¹ := by rw [← hh, pow_two]; group
      have : g * f ^ 2 * g⁻¹ = h * f ^ 2 * h⁻¹ := by rw [← e1, ← e2, hlm]
      calc (h⁻¹ * g) * f ^ 2 = h⁻¹ * (g * f ^ 2 * g⁻¹) * g := by group
        _ = h⁻¹ * (h * f ^ 2 * h⁻¹) * g := by rw [this]
        _ = f ^ 2 * (h⁻¹ * g) := by group
    have hmem := hN _ hcomm
    have h4 : orderOf ((h⁻¹ * g) * f * (h⁻¹ * g)⁻¹) = 4 :=
      orderOf_eq_four_of_isConj hf (isConj_iff.2 ⟨h⁻¹ * g, rfl⟩)
    have hl' : l = h * ((h⁻¹ * g) * f * (h⁻¹ * g)⁻¹) * h⁻¹ := by rw [← hg]; group
    rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four hf hmem h4 with h' | h'
    · left; rw [hl', h', hh]
    · right; rw [hl', h', ← hh]; group
  have hΛ4' : ∀ l ∈ Λ, ∀ z ∈ T, z * (l * l) = (l * l) * z →
      z * l * z⁻¹ = l ∨ z * l * z⁻¹ = l⁻¹ := fun l hl z _ hz => by
    obtain ⟨g, hg⟩ := isConj_iff.1 hl.2
    exact key g l hl.2 hg.symm z hz
  exact alperin_aux (Nat.card T) T Λ rfl hT hΛ4 hΛinv hΛ3 hΛ4' x ⟨hxT, hx⟩ y ⟨hyT, hy⟩

end Abstract

end CFSG.EvenSporadicStandard.TwoHS
