module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Fuse
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1QS

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.excl_graph_core
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hk : c.kinds = {Kind.graph}) : False := by
  have hk' : ∀ k', (c.rep k').isSome → k' = Kind.graph := by
    intro k' hk'
    have hmem : k' ∈ c.kinds := hk'
    rw [hk] at hmem
    exact hmem
  obtain ⟨yκ, hyκ⟩ : ∃ y, c.rep Kind.graph = some y := by
    have hmem : Kind.graph ∈ c.kinds := by rw [hk]; rfl
    exact Option.isSome_iff_exists.1 hmem
  obtain ⟨hyX, hyQS, hyact⟩ := c.rep_mem Kind.graph yκ hyκ
  have hnc : ¬ IsConj d.q c.pi := fun hfus => by
    refine c.false_of_acts_through_S hα h hP hQ hS2 hc hg hact (fun x hx => ?_) hfus
    by_cases hxQS : x ∈ d.QS
    · obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hxQS
      exact ⟨s, hs, fun v hv => d.conj_QS_on_S hu hs (c.V_le_S h hv)⟩
    · obtain ⟨y, hy, u', hu', rfl⟩ := c.exists_rep_of_kinds hk' hx hxQS
      obtain rfl : yκ = y := Option.some_injective _ (hyκ.symm.trans hy)
      obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hu'
      refine ⟨s, hs, fun v hv => ?_⟩
      have hfix : yκ⁻¹ * v * yκ = v := c.graph_fixes_V hα h hP hQ hyact v hv
      have e : yκ * v * yκ⁻¹ = v := by
        calc yκ * v * yκ⁻¹ = yκ * (yκ⁻¹ * v * yκ) * yκ⁻¹ := by rw [hfix]
          _ = v := by group
      calc u * s * yκ * v * (u * s * yκ)⁻¹ = (u * s) * (yκ * v * yκ⁻¹) * (u * s)⁻¹ := by group
        _ = (u * s) * v * (u * s)⁻¹ := by rw [e]
        _ = s * v * s⁻¹ := d.conj_QS_on_S hu hs (c.V_le_S h hv)
  obtain ⟨z, hzX, hzQS, hz2, hzq, hzact⟩ := c.exists_z hα h hP hQ hS2 hc hk' hnc
  have hα0 : α = 0 := by
    by_contra hne
    have hα1 : α = 1 := by omega
    subst hα1
    have hzt : cj c.t z = c.t := by
      simp only [Kind.Act] at hzact
      simp at hzact
      exact hzact.1
    have hcomm : z * c.t = c.t * z := by
      unfold cj at hzt
      calc z * c.t = z * (z⁻¹ * c.t * z) := by rw [hzt]
        _ = c.t * z := by group
    exact hnc (c.fuse_of_commutes hα h hP hQ hc hzQS hzq hcomm)
  subst hα0
  have hzt : cj c.t z = c.t⁻¹ := by
    simp only [Kind.Act] at hzact
    simp at hzact
    exact hzact.1
  have hconj := c.coset_conj_graph hα h hP hQ hzact hz2 hzt
  have hVz : ∀ v ∈ c.V, z * v = v * z := fun v hv => by
    have := c.graph_fixes_V hα h hP hQ hzact v hv
    calc z * v = z * (z⁻¹ * v * z) := by rw [this]
      _ = v * z := by group
  have hπV : c.pi ∈ c.V := subset_closure (by simp)
  have hqV : d.q ∈ c.V := subset_closure (by simp)
  have hconj' : ∀ v ∈ c.V, IsConj z (z * v) := fun v hv => by
    obtain ⟨s, hs, hsz⟩ := hconj v hv
    refine isConj_iff.2 ⟨s⁻¹, ?_⟩
    have : s⁻¹ * z * s = v * z := hsz
    calc s⁻¹ * z * s⁻¹⁻¹ = s⁻¹ * z * s := by group
      _ = v * z := this
      _ = z * v := (hVz v hv).symm
  exact c.false_of_fuse_z hα h hP hQ hc hnc
    (fun a ha haQS b hb hbQS => c.mul_mem_QS_of_kinds hα h hP hQ hk' ha haQS hb hbQS)
    hzX hzQS hzq (hVz c.pi hπV) (hconj' c.pi hπV) (hconj' _ (mul_mem hqV hπV))

end CFSG.OddStandard.ChengHeld
