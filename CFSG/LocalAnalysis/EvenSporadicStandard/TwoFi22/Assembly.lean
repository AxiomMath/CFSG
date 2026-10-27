module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.AssemblyLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.AssemblySylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.HiiMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameCondMain

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer CFSG.Fischer
  CFSG.EvenSmallLie.ThreeTransposition

variable {G : Type} [Group G] {t : G}

theorem isThreeTranspositionSet_t
    [Finite G] [IsSimpleGroup G] (M : Model G t) (hF : SquareFacts) (hFrame : FrameFact)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (ht : orderOf t = 2) :
    (commGraph {g : G | IsConj t g}).Connected ∧ IsThreeTranspositionSet {g : G | IsConj t g} := by
  obtain ⟨ε, hε⟩ := Dt_eq_starSet M hF hnonab ht
  have hclass : ∃ d₀ : G, {g : G | IsConj t g} = {g | IsConj d₀ g} := ⟨t, rfl⟩
  have hD2 : ∀ x ∈ {g : G | IsConj t g}, orderOf x = 2 := fun x hx =>
    orderOf_eq_two_of_isConj ht hx
  have hD2' : ∀ x ∈ {g : G | IsConj t g}, x * x = 1 := fun x hx =>
    mul_self_of_orderOf_two (hD2 x hx)
  have hinv : ∀ g : G, ∀ x ∈ {g : G | IsConj t g}, g * x * g⁻¹ ∈ {g : G | IsConj t g} :=
    fun g x hx => IsConj.trans hx (isConj_iff.2 ⟨g, rfl⟩)
  obtain ⟨Lj⟩ := nonempty_localPoints_J
  have hloc := nonempty_localPoints M hε Lj
  have hii := hii_of_localPoints hinv hD2' hloc t (IsConj.refl t)
  obtain ⟨T, F, hΩ⟩ := exists_sylow_frame M hF hnonab ht hFrame
  obtain ⟨hiii, hiv, hv, h1, h2, h3⟩ := sylow_conditions_of_frame hclass hD2 T F hΩ
  exact connected_isThreeTranspositionSet_of_orders hclass hD2 (IsConj.refl t)
    (orderOf_mul_mem M hε) hii T hiii hiv hv h1 h2 h3

theorem orderOf_mul_mem_class
    [Finite G] [IsSimpleGroup G] (M : Model G t) (hF : SquareFacts) (hFrame : FrameFact)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (ht : orderOf t = 2) (x y : G) (hx : IsConj t x)
    (hy : IsConj t y) : orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) :=
  (isThreeTranspositionSet_t M hF hFrame hnonab ht).2.2.2 x hx y hy

end CFSG.EvenSporadicStandard.TwoFi22
