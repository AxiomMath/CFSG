module

public import CFSG.GH74.Generic.Front.Props

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner perfect_action_inner)

theorem mem_of_conjNormal_inner {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hcent : Subgroup.centralizer (K : Set X) ≤ K) {g : X} {k : ↥K}
    (h : (MulAut.conjNormal g : MulAut ↥K) = MulAut.conj k) : g ∈ K := by
  have hc : (k : X)⁻¹ * g ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := congrArg (fun σ : MulAut ↥K => ((σ ⟨n, hn⟩ : ↥K) : X)) h
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      at h1
    have h2 : (k : X)⁻¹ * g * n = n * ((k : X)⁻¹ * g) := by
      calc (k : X)⁻¹ * g * n = (k : X)⁻¹ * (g * n * g⁻¹) * g := by group
        _ = (k : X)⁻¹ * ((k : X) * n * (k : X)⁻¹) * g := by rw [h1]
        _ = n * ((k : X)⁻¹ * g) := by group
    exact h2.symm
  have : (k : X) * ((k : X)⁻¹ * g) ∈ K := K.mul_mem k.2 (hcent hc)
  simpa using this

theorem goodSub_le_of_outer {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hcent : Subgroup.centralizer (K : Set X) ≤ K) {T : Prop}
    (hsolv : Group.IsSolvable (Outer ↥K))
    (hodd : T → ∀ o : Outer ↥K, Odd (orderOf o) → o = 1) :
    ∀ P : Subgroup X, GoodSub T P → P ≤ K := by
  intro P hP
  let act : ↥P →* MulAut ↥K := (MulAut.conjNormal : X →* MulAut ↥K).comp P.subtype
  rcases hP with hperf | ⟨hgen, hT⟩
  · have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
    intro p hp
    obtain ⟨k, hk⟩ := perfect_action_inner act ⟨p, hp⟩
    exact mem_of_conjNormal_inner hcent hk
  · rw [← hgen]
    refine (Subgroup.closure_le K).2 ?_
    rintro g ⟨hgP, hgodd⟩
    have hmem : (QuotientGroup.mk' (inner ↥K)) (act ⟨g, hgP⟩) = 1 := by
      apply hodd hT
      have h1 := orderOf_map_dvd (QuotientGroup.mk' (inner ↥K)) (act ⟨g, hgP⟩)
      have h2 := orderOf_map_dvd act (⟨g, hgP⟩ : ↥P)
      rw [Subgroup.orderOf_mk] at h2
      exact Odd.of_dvd_nat hgodd (h1.trans h2)
    obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff _).1 hmem
    exact mem_of_conjNormal_inner hcent (by simpa [act] using hk.symm)

theorem goodSub_le_of_outerStatement (hO : OuterStatement) {X : Type} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (hK : ShapeModel ↥K)
    (hcent : Subgroup.centralizer (K : Set X) ≤ K) :
    ∀ P : Subgroup X, GoodSub (ThreeModel ↥K) P → P ≤ K := by
  exact goodSub_le_of_outer hcent (hO.1 ↥K hK) (hO.2 ↥K hK)

end CFSG.GH74.Generic
