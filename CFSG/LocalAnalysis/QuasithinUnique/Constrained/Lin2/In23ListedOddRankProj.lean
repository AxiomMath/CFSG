module

import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.ClassicalEven Matrix

theorem two_le_pRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : Commute x y) (hx1 : x ≠ 1)
    (hy1 : ∀ n : ℕ, x ^ n ≠ y) : 2 ≤ pRank p (⊤ : Subgroup G) :=
  CFSG.SectionRank.two_le_pRank_top_of_commute hx hy hxy hx1 hy1

theorem two_le_pRank_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {p : ℕ} [hp : Fact p.Prime] {x y : GL ι K}
    (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : Commute x y)
    (hx1 : x ∉ StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y) :
    2 ≤ pRank p (⊤ : Subgroup (StatedProj H)) := by
  let N := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H), a ^ p = 1 → π ⟨a, ha⟩ ^ p = 1 := fun a ha h => by
    rw [← map_pow]
    have : (⟨a, ha⟩ : H) ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
    rw [this, map_one]
  have hcomm : ∀ (a b : GL ι K) (ha : a ∈ H) (hb : b ∈ H), Commute a b →
      Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := fun a b ha hb h =>
    Commute.map (show Commute (⟨a, ha⟩ : H) ⟨b, hb⟩ from Subtype.ext h.eq) π
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa using h
  refine two_le_pRank_of_gens (hpow x hxH hx) (hpow y hyH hy) (hcomm _ _ _ _ hxy)
    (fun h => hx1 ?_) (fun n h => ?_)
  · have := hmem _ _ (h.trans (map_one π).symm)
    simpa using this
  · rw [← map_pow] at h
    have := hmem _ _ h
    simp only [SubgroupClass.coe_pow] at this
    exact hy1 n _ this (mul_inv_cancel_left _ _)

section Transport

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_equiv {K : Subgroup G} {X : Type} [Group X] [Finite X] (e : ↥K ≃* X)
    {p k : ℕ} (hp : 1 < p) (h : k ≤ pRank p (⊤ : Subgroup X)) : k ≤ pRank p K := by
  have h1 : pRank p (⊤ : Subgroup ↥K) = pRank p (⊤ : Subgroup X) :=
    pRank_top_eq_of_mulEquiv hp e
  have h2 := pRank_le_map hp K.subtype K.subtype_injective (⊤ : Subgroup ↥K)
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h.trans (h1 ▸ h2)

end Transport

end CFSG.QuasithinUnique.Lin2.OddRank
