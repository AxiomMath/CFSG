module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Z8Strong

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5z8_quotient_of_strong {G : Type} [Group G] {S T : Subgroup G} {z : G} (hzS : z ∈ S)
    (hSC : ∀ x ∈ T, ∀ g ∈ centralizer ({z} : Set G), g * x * g⁻¹ ∈ S → g * x * g⁻¹ ∈ T)
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X) (hπ : Function.Surjective π)
    (hker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G))) :
    ∀ c ∈ (T.subgroupOf (centralizer ({z} : Set G))).map π,
      ∀ g : X, g⁻¹ * c * g ∈ (S.subgroupOf (centralizer ({z} : Set G))).map π →
        g⁻¹ * c * g ∈ (T.subgroupOf (centralizer ({z} : Set G))).map π := by
  intro c hc g hg
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  obtain ⟨g₀, rfl⟩ := hπ g
  obtain ⟨s₀, hs₀, hs₀eq⟩ := hg
  have hk : s₀⁻¹ * (g₀⁻¹ * c₀ * g₀) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hs₀eq]
    group
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have hzS : zpowers z ≤ S := Subgroup.zpowers_le.mpr hzS
  have hS : (g₀⁻¹ * c₀ * g₀ : ↥(centralizer ({z} : Set G))) ∈ S.subgroupOf
      (centralizer ({z} : Set G)) := by
    rw [Subgroup.mem_subgroupOf]
    have e : ((g₀⁻¹ * c₀ * g₀ : ↥(centralizer ({z} : Set G))) : G) =
        (s₀ : G) * ((s₀⁻¹ * (g₀⁻¹ * c₀ * g₀) : ↥(centralizer ({z} : Set G))) : G) := by
      push_cast
      group
    rw [e]
    exact mul_mem (Subgroup.mem_subgroupOf.mp hs₀) (hzS hk)
  have hxg : (g₀ : G)⁻¹ * (c₀ : G) * ((g₀ : G)⁻¹)⁻¹ ∈ S := by
    have := Subgroup.mem_subgroupOf.mp hS
    push_cast at this
    simpa using this
  have hT := hSC (c₀ : G) (Subgroup.mem_subgroupOf.mp hc₀) ((g₀ : G)⁻¹) (inv_mem g₀.2) hxg
  refine ⟨g₀⁻¹ * c₀ * g₀, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
  push_cast
  simpa using hT

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

theorem sec5z8_strongly_closed_quotient (hy : Sec5B59Hyp) (h55 : Asc82Lemma55)
    (h58d : Asc82Lemma58d) (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6)
    (hU : Asc82FactPocketsUniq6) (hSq : Asc82FactSqReflQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hTR : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) =
      sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X) (hπ : Function.Surjective π)
    (hker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G))) :
    ∀ c ∈ ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
        (centralizer ({z} : Set G))).map π,
      ∀ g : X, g⁻¹ * c * g ∈ (S.subgroupOf (centralizer ({z} : Set G))).map π →
        g⁻¹ * c * g ∈ ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
          (centralizer ({z} : Set G))).map π := by
  exact sec5z8_quotient_of_strong (S := S)
    (T := sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))) h.mem_S
    (fun x hx g hg hxg => sec5z8_strongly_closed hy h55 h58d hFB h4 hU hSq h hs hTR hx hg hxg)
    π hπ hker

end CFSG.OddStandard.SmallF3.Omega
