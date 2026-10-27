module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

theorem sec5z_strongly_closed (hy : Sec5B59Hyp) (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d)
    (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hTE : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) = sec5p510_E t a b)
    {x g : G} (hx : x ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)))
    (hg : g ∈ centralizer ({z} : Set G)) (hxg : g * x * g⁻¹ ∈ S) :
    g * x * g⁻¹ ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) := by
  have hzz : z * z = 1 := sec5p510_A_sq h (sec5p510_z_mem_A h)
  have hzS : z ∈ S := h.mem_S
  have hzT : z ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) := by
    rw [hTE]
    exact sec5p510_z_mem_E h hs.ab
  have hgz : g * z * g⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg]
    group
  by_cases hxz : x ∈ zpowers z
  · have hgx : g * x * g⁻¹ = x := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
      have hgk : Commute g (z ^ k) :=
        Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hg) k
      rw [hgk.eq]
      group
    rw [hgx]
    exact hx
  · have hxE : x ∈ sec5p510_E t a b := by
      rw [← hTE]
      exact hx
    have hx2 : x * x = 1 := sec5p510_A_sq h (sec5p510_E_le_A h hs.ab hxE)
    obtain ⟨y, hyH, hxy⟩ := hs.T_invol x hx (by rw [hx2]; exact one_mem _) hxz
    have hgy : g * y * g⁻¹ ∈ conjClassIn (centralizer ({z} : Set G)) t :=
      sec5p510_conj_mem_conj hyH hg
    rcases hxy with rfl | rfl
    · exact sec5z_conj_inter_S_le_T hy h55 h58d hFB h4 h.toSec5Ctx h.nconj hs.pk.q hgy hxg
    · have hgx : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * z := by
        calc g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
          _ = (g * y * g⁻¹) * z := by rw [hgz]
      have hgyS : g * y * g⁻¹ ∈ S := by
        have e : g * y * g⁻¹ = (g * (y * z) * g⁻¹) * z := by
          rw [hgx, mul_assoc (g * y * g⁻¹) z z, hzz, mul_one]
        rw [e]
        exact mul_mem hxg hzS
      have hT := sec5z_conj_inter_S_le_T hy h55 h58d hFB h4 h.toSec5Ctx h.nconj hs.pk.q hgy hgyS
      rw [hgx]
      exact mul_mem hT hzT

theorem sec5z_strongly_closed_quotient (hy : Sec5B59Hyp) (h55 : Asc82Lemma55)
    (h58d : Asc82Lemma58d) (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hTE : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) = sec5p510_E t a b)
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X) (hπ : Function.Surjective π)
    (hker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G))) :
    ∀ c ∈ ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
        (centralizer ({z} : Set G))).map π,
      ∀ g : X, g⁻¹ * c * g ∈ (S.subgroupOf (centralizer ({z} : Set G))).map π →
        g⁻¹ * c * g ∈ ((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
          (centralizer ({z} : Set G))).map π := by
  intro c hc g hg
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  obtain ⟨g₀, rfl⟩ := hπ g
  obtain ⟨s₀, hs₀, hs₀eq⟩ := hg
  have hk : s₀⁻¹ * (g₀⁻¹ * c₀ * g₀) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hs₀eq]
    group
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have hzS : zpowers z ≤ S := Subgroup.zpowers_le.mpr h.mem_S
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
  have hT := sec5z_strongly_closed hy h55 h58d hFB h4 h hs hTE (x := (c₀ : G))
    (g := (g₀ : G)⁻¹) (Subgroup.mem_subgroupOf.mp hc₀) (inv_mem g₀.2) hxg
  refine ⟨g₀⁻¹ * c₀ * g₀, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
  push_cast
  simpa using hT

end CFSG.OddStandard.SmallF3.Omega
