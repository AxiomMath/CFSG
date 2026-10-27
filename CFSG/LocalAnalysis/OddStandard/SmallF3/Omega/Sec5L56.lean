module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Step56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec5Ctx G t L S z →
    ∀ g₀ : G, g₀⁻¹ * t * g₀ = t * z →
      ∃ b : G, IsI4PlusIn L b ∧
        ∃ β : ℤˣ, InducesTypeSome (CFSG.conjugate L g₀) (t * b) 6 (-1) 1 β

theorem asc82Lemma56_of (h52b : Asc82Lemma52b) (h55 : Asc82Lemma55) (tab : Asc82Tab5)
    (hstep : Asc82Step56) : Asc82Lemma56 := by
  intro G _ _ t L S z h
  obtain ⟨g₁, hC, hne⟩ :=
    sec7_zstar h.toSec3Setting.simple (sec4_nonabelian h.toSec3Setting) h.involution
  rcases h55 G t L S z h with ⟨g₀, hg₀⟩ | hall
  · obtain ⟨b, hbP, β, hβ⟩ := hstep G t L S z h g₀ hg₀
    obtain ⟨a, haL, hb⟩ := sec5_pocket_class h52b tab h hbP
    have hat : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp (h.component.le haL)
    refine ⟨g₀ * (t * b) * g₀⁻¹, ⟨g₀ * a⁻¹ * g₀⁻¹, ?_⟩, β, ?_⟩
    · have htb : t * b = a * (g₀⁻¹ * t * g₀) * a⁻¹ := by
        rw [hg₀, hb]
        calc t * (a * z * a⁻¹) = (t * a) * z * a⁻¹ := by group
          _ = (a * t) * z * a⁻¹ := by rw [hat.symm]
          _ = a * (t * z) * a⁻¹ := by group
      rw [htb]
      group
    · have := inducesTypeSome_conjugate hβ g₀⁻¹
      rwa [conjugate_conjugate_inv, inv_inv] at this
  · exact ⟨g₁⁻¹ * t * g₁, ⟨g₁, rfl⟩, hall g₁ hC hne⟩

end CFSG.OddStandard.SmallF3.Omega
