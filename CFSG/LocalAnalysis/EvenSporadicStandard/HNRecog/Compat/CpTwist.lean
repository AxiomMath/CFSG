module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Fam

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

theorem cp_conj_pair {p q w g : G} (hg : g ∈ Gx a) (h1 : IsConj p w) (h2 : IsConj q (a * w)) :
    IsConj p (g * w * g⁻¹) ∧ IsConj q (a * (g * w * g⁻¹)) := by
  have hga : g * a * g⁻¹ = a := by
    rw [← mem_Gx.1 hg, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨h1.trans (isConj_iff.2 ⟨g, rfl⟩), ?_⟩
  have e : a * (g * w * g⁻¹) = g * (a * w) * g⁻¹ := by
    calc a * (g * w * g⁻¹) = (g * a * g⁻¹) * (g * w * g⁻¹) := by rw [hga]
      _ = g * (a * w) * g⁻¹ := by group
  rw [e]
  exact h2.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem cp_orb2B_conj {g t : G} (hg : g ∈ Gx a) (ht : t ∈ orb2B a z a) :
    g * t * g⁻¹ ∈ orb2B a z a :=
  cp_conj_pair hg ht.1 ht.2

theorem cp_orb2AB_conj {g t : G} (hg : g ∈ Gx a) (ht : t ∈ orb2AB a z a) :
    g * t * g⁻¹ ∈ orb2AB a z a :=
  cp_conj_pair hg ht.1 ht.2

theorem cp_orb2BB_conj {g t : G} (hg : g ∈ Gx a) (ht : t ∈ orb2BB a z a) :
    g * t * g⁻¹ ∈ orb2BB a z a :=
  cp_conj_pair hg ht.1 ht.2

theorem cp_twist_class (F : Fam a α) {C : Set G} (hC : ∀ g ∈ Gx a, ∀ t ∈ C, g * t * g⁻¹ ∈ C)
    {x t₁ t₂ : G} (ht₁C : t₁ ∉ C) (ht₂C : t₂ ∈ C)
    (hpair : F.app t₁ x = F.app t₂ x ∨ F.app t₁ x = F.app t₂ (a * x * a⁻¹)) :
    ∃ F' : Fam a α, F'.app t₁ x = F'.app t₂ x ∧ ∀ t ∉ C, ∀ y, F'.app t y = F.app t y := by
  by_cases hh : F.app t₁ x = F.app t₂ x
  · exact ⟨F, hh, fun _ _ _ => rfl⟩
  · refine ⟨F.twist C hC, ?_, fun t ht y => F.twist_app_of_not_mem hC ht y⟩
    rw [F.twist_app_of_not_mem hC ht₁C, F.twist_app_of_mem hC ht₂C]
    exact hpair.resolve_left hh

end CFSG.EvenSporadicStandard.HNRecog.Section4
