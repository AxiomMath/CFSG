module

public import CFSG.Adapters.Involutions

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace T8R

section ZStar

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_sylow_ne [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : Sylow 2 G) {a : G} (haS : a ∈ (S : Subgroup G))
    (hcomm : ∀ s ∈ (S : Subgroup G), s * a = a * s) (ha2 : orderOf a = 2) :
    ∃ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) ∧ g⁻¹ * a * g ≠ a := by
  by_contra hcon
  push Not at hcon
  have hzZ : (⟨a, haS⟩ : ↥(S : Subgroup G)) ∈ Subgroup.center ↥(S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hcomm s s.2)
  have hz : orderOf (⟨a, haS⟩ : ↥(S : Subgroup G)) = 2 := (Subgroup.orderOf_mk a haS).trans ha2
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar S ⟨a, haS⟩ hzZ hz (fun g hg => hcon g hg)
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  rcases Subgroup.Normal.eq_bot_or_eq_top (CFSG.oddCore G) with h | h
  · have hac : ∀ g : G, g * a = a * g := by
      intro g
      have h1 := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk g)
      have h2 : (QuotientGroup.mk (g * a) : G ⧸ CFSG.oddCore G) = QuotientGroup.mk (a * g) :=
        h1
      rw [QuotientGroup.eq, h] at h2
      have h3 : (g * a)⁻¹ * (a * g) = 1 := Subgroup.mem_bot.mp h2
      calc g * a = (g * a) * ((g * a)⁻¹ * (a * g)) := by rw [h3, mul_one]
        _ = a * g := by group
    have hcz : a ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr hac
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h' | h'
    · exact ha1 (by simpa [h'] using hcz)
    · obtain ⟨x, y, hxy⟩ := hnab
      have hx : x ∈ Subgroup.center G := by rw [h']; exact Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)
  · exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two ha2 (by rw [h]; exact Subgroup.mem_top a)

end ZStar

end T8R

end CFSG.ClassicalInvolution.Asc77
