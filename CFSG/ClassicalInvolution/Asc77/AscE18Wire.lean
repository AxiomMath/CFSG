module

public import CFSG.ClassicalInvolution.Asc77.AscE187Main
public import CFSG.ClassicalInvolution.Asc77.AscE186Final
public import CFSG.ClassicalInvolution.Asc77.AscE184Four

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem e18_6_proved : E18_6 p f :=
  AscE186.e18_6_of_wfree p f (fun _ _ _ _ _ _ _ _ _ c => c.hyp.cent)
    (fun _ _ _ _ _ _ _ _ _ c Gb _ _ hlt Ωb Kb Sb Rb Wb Hb hst ht hcn =>
      c.minimal Gb hlt Ωb Kb Sb Rb Wb Hb hst ⟨ht, hcn⟩)

theorem e18_7_proved (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) : E18_7 p f :=
  e18_7 p f ⟨l6_7_proved p f, l6_9_proved p f, l6_11_proved p f, e18_6_proved p f⟩
    (e18_4C p f (l6_9_proved p f) (l6_11_proved p f) h3s)

theorem e18_8z_proved (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) : E18_8z p f :=
  e18_8z_of_e18_7 p f (e18_7_proved p f h3s)

@[expose] def E18_endS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      (∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
        Subgroup.centralizer (F : Set G) = ⊥) →
      ∀ z : G, IsUniqueInvolution K z →
        IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
          (Subgroup.centralizer ({z} : Set G)) →
        FixesUniqueCoset z H →
        (∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) → h⁻¹ * z * h ≠ z →
          z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z → FixesUniqueCoset (z * (h⁻¹ * z * h)) H) →
        False

theorem minCexFalse_of_steps' (h6 : E18_6 p f) (h8 : E18_8z p f) (h9 : E18_9 p f)
    (hend : E18_endS p f) : MinCexFalse p f := by
  intro G _ _ Ω K S R W H c
  obtain ⟨z, hz1, -⟩ := c.exists_centralizer_le p f
  obtain ⟨S', W', c', hSyl⟩ := c.exists_config_sylow_centralizer hz1
  obtain ⟨-, hF⟩ := h6 G Ω K S' R W' H c'
  have hzc : FixesUniqueCoset z H := h8 G Ω K S' R W' H c' z hz1
  exact hend G Ω K S' R W' H c' hF z hz1 hSyl hzc fun h h1 h2 h3 =>
    h9 G Ω K S' R W' H c' z hz1 h h1 h2 h3

end CFSG.ClassicalInvolution.Asc77
