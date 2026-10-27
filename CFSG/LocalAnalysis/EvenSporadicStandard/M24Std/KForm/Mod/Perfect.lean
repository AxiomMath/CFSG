module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Setting
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup

variable {G : Type*} [Group G] {B : Type*} [Group B] {t : G} {B₀ : Subgroup B}
  {ψ : ↥(centralizer ({t} : Set G)) →* Multiplicative (ZMod 2) × B}

theorem even_natCard_of_isPerfect [Finite G] {X : Subgroup G} (hX : ⁅X, X⁆ = X) (hX1 : X ≠ ⊥) :
    Even (Nat.card X) := by
  by_contra h
  haveI : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hX1
  haveI : Group.IsPerfect X := Subgroup.isPerfect_iff.2 hX
  exact Group.IsPerfect.not_isSolvable X
    (CFSG.Milestones.odd_order_solvable (G := X) (Nat.not_even_iff_odd.mp h))

namespace ModData

theorem imgOf_ne_bot_of_perfect [Finite G] (h : ModData t B₀ ψ) {X : Subgroup G}
    (hX : ⁅X, X⁆ = X) (hX1 : X ≠ ⊥) (hXt : ∀ x ∈ X, t * x * t⁻¹ ∈ X) :
    imgOf ψ (X ⊓ centralizer ({t} : Set G)) ≠ ⊥ := by
  by_contra hbot
  have hnot4 : ¬ 4 ∣ Nat.card ↥(X ⊓ centralizer ({t} : Set G)) :=
    h.not_four_dvd_natCard hbot inf_le_right
  by_cases htX : t ∈ X
  · exact hnot4 (four_dvd_natCard_inf_centralizer_of_isPerfect hX htX h.t_sq h.t_ne)
  · have hev : Even (Nat.card X) := even_natCard_of_isPerfect hX hX1
    have hevY : Even (Nat.card ↥(X ⊓ centralizer ({t} : Set G))) :=
      even_natCard_inf_centralizer h.t_sq hXt hev
    obtain ⟨u, huY, hu2, hu1⟩ := exists_involution_of_even hevY
    obtain ⟨huX, huC⟩ := Subgroup.mem_inf.mp huY
    have hφ : phi ψ ⟨u, huC⟩ = 1 := (imgOf_eq_bot_iff.mp hbot) u huY huC
    have hupow : u ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hu2
    rcases h.eq_one_or_eq_t huC hφ hupow with h1 | ht
    · exact hu1 h1
    · exact htX (ht ▸ huX)

theorem le_imgOf_of_perfect [Finite G] (h : ModData t B₀ ψ) {X : Subgroup G}
    (hX : ⁅X, X⁆ = X) (hX1 : X ≠ ⊥)
    (hXC : ∀ c ∈ centralizer ({t} : Set G), ∀ x ∈ X, c * x * c⁻¹ ∈ X) :
    B₀ ≤ imgOf ψ (X ⊓ centralizer ({t} : Set G)) := by
  have hXt : ∀ x ∈ X, t * x * t⁻¹ ∈ X :=
    hXC t (mem_centralizer_singleton_iff.2 rfl)
  have hY : ∀ c ∈ centralizer ({t} : Set G), ∀ y ∈ X ⊓ centralizer ({t} : Set G),
      c * y * c⁻¹ ∈ X ⊓ centralizer ({t} : Set G) := by
    intro c hc y hy
    have hcy : c * y * c⁻¹ ∈ centralizer ({t} : Set G) :=
      mul_mem (mul_mem hc hy.2) (inv_mem hc)
    exact ⟨hXC c hc y hy.1, hcy⟩
  rcases h.imgOf_eq_bot_or_le (Y := X ⊓ centralizer ({t} : Set G)) hY with hbot | hle
  · exact absurd hbot (imgOf_ne_bot_of_perfect h hX hX1 hXt)
  · exact hle

end ModData

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
