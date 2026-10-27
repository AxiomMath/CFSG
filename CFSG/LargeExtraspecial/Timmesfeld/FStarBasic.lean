module

public import CFSG.LargeExtraspecial.Timmesfeld.FStar
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LargeExtraspecial.Timmesfeld

open CFSG

variable {G : Type} [Group G]

theorem fStar_le (M : Subgroup G) : fStar M ≤ M := by
  rintro x ⟨y, _, rfl⟩
  exact y.2

theorem fStar_normal [Finite G] {M : Subgroup G} {g x : G} (hg : g ∈ M) (hx : x ∈ fStar M) :
    g * x * g⁻¹ ∈ fStar M := by
  obtain ⟨f, hf, rfl⟩ := hx
  haveI : (CFSG.generalizedFitting ↥M).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥M)).2
  exact ⟨⟨g, hg⟩ * f * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance f hf ⟨g, hg⟩, rfl⟩

theorem fStar_cent [Finite G] {M : Subgroup G} {y : G} (hy : y ∈ M)
    (h : ∀ q ∈ fStar M, y * q = q * y) : y ∈ fStar M := by
  have := CFSG.centralizer_generalizedFitting_le (↥M) (x := (⟨y, hy⟩ : ↥M))
  have hh : (⟨y, hy⟩ : ↥M) ∈
      Subgroup.centralizer ((CFSG.generalizedFitting ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' := h (g : G) ⟨g, hg, rfl⟩
    exact Subtype.ext hg'.symm
  exact ⟨_, this hh, rfl⟩

theorem fStar_subgroupOf_normal [Finite G] (M : Subgroup G) :
    ((fStar M).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff (fStar_le M)).mpr fun _ _ hx hy => fStar_normal hy hx

end CFSG.LargeExtraspecial.Timmesfeld
