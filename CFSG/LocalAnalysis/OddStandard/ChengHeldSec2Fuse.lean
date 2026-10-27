module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2UniqW
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Conj

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.normalizes_of_conj_le_X
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ w ∈ c.W, g * w * g⁻¹ ∈ d.X) :
    (∀ w, w ∈ c.W ↔ g * w * g⁻¹ ∈ c.W) ∧ (∀ v, v ∈ c.V ↔ g * v * g⁻¹ ∈ c.V) := by
  set W' : Subgroup G := c.W.map (MulAut.conj g).toMonoidHom with hW'
  have hmemW' : ∀ x, x ∈ W' ↔ ∃ w ∈ c.W, g * w * g⁻¹ = x := fun x => by
    simp [hW', Subgroup.mem_map]
  have hW'X : W' ≤ d.X := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (hmemW' x).1 hx
    exact hg w hw
  have hiso : Nonempty (↥W' ≃* ↥c.W) :=
    ⟨((MulAut.conj g).subgroupMap c.W).symm⟩
  have hWeq : W' = c.W := c.unique_W hα h hP hQ hS2 hc hW'X hiso
  have hmem : ∀ w, w ∈ c.W ↔ g * w * g⁻¹ ∈ c.W := fun w => by
    constructor
    · intro hw
      rw [← hWeq]
      exact (hmemW' _).2 ⟨w, hw, rfl⟩
    · intro hw
      rw [← hWeq] at hw
      obtain ⟨w', hw', he⟩ := (hmemW' _).1 hw
      have : w' = w := mul_left_cancel (mul_right_cancel he)
      rwa [← this]
  have hS := c.sFacts hα h hP hQ
  refine ⟨hmem, fun v => ?_⟩
  have hVW : c.V ≤ c.W := fun v hv =>
    c.mem_W_of_comm (c.V_le_S h hv) fun v' hv' => hS.V_comm v hv v' hv'
  have hsqg : ∀ v, g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := fun v => by group
  constructor
  · intro hv
    refine hS.W_invol _ ((hmem v).1 (hVW hv)) ?_
    rw [hsqg, hS.V_sq v hv]
    group
  · intro hv
    have hvW : v ∈ c.W := (hmem v).2 (hVW hv)
    refine hS.W_invol v hvW ?_
    have h1 := hS.V_sq _ hv
    rw [hsqg] at h1
    have h2 : g * (v * v) * g⁻¹ = g * 1 * g⁻¹ := by rw [h1]; group
    exact mul_left_cancel (mul_right_cancel h2)

theorem Chart4.X_normalizes
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {x : G}
    (hx : x ∈ d.X) :
    (∀ w, w ∈ c.W ↔ x * w * x⁻¹ ∈ c.W) ∧ (∀ v, v ∈ c.V ↔ x * v * x⁻¹ ∈ c.V) :=
  c.normalizes_of_conj_le_X hα h hP hQ hS2 hc fun _ hw =>
    d.X.mul_mem (d.X.mul_mem hx (d.S_le_X hw.1)) (d.X.inv_mem hx)

theorem Chart4.fuse_in_normalizer
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (hfus : IsConj d.q c.pi) :
    ∃ g : G, g⁻¹ * d.q * g = c.pi ∧ (∀ w, w ∈ c.W ↔ g * w * g⁻¹ ∈ c.W) ∧
      (∀ v, v ∈ c.V ↔ g * v * g⁻¹ ∈ c.V) := by
  obtain ⟨g, hg, hgX⟩ := d.exists_conj_config h hfus
  have hpiV : c.pi ∈ c.V := Subgroup.subset_closure (by simp)
  obtain ⟨hW, hV⟩ := c.normalizes_of_conj_le_X hα h hP hQ hS2 hc fun w hw =>
    hgX w (d.S_le_X hw.1) (c.W_comm_V hw hpiV)
  exact ⟨g, hg, hW, hV⟩

theorem Chart4.fuse_in_normalizer'
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (hfus : IsConj d.q c.pi) :
    ∃ n ∈ normalizer (c.V : Set G), cj d.q n = c.pi := by
  obtain ⟨g, hg, -, hV⟩ := c.fuse_in_normalizer hα h hP hQ hS2 hc hfus
  exact ⟨g, mem_normalizer_iff.2 fun v => by rw [← SetLike.mem_coe] at *; exact hV v, hg⟩

theorem Chart4.fuse_of_commutes
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {z : G}
    (hzQS : z ∉ d.QS) (hzq : IsConj d.q z) (hzt : z * c.t = c.t * z) : IsConj d.q c.pi := by
  obtain ⟨g, hg, hgX⟩ := d.exists_conj_config h hzq
  have htX : c.t ∈ d.X := d.S_le_X c.t_mem.2
  have ht₁ : g * c.t * g⁻¹ ∈ d.X := hgX c.t htX hzt.symm
  have hqq : d.q * d.q = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])
  have hq' : g * d.q * g⁻¹ = (g * c.t * g⁻¹) * (g * c.t * g⁻¹) := by
    rw [c.q_eq, pow_two]; group
  have hq'QS : g * d.q * g⁻¹ ∈ d.QS := by
    rw [hq']; exact c.sq_mem_QS hα h hP hQ ht₁
  have hq'2 : (g * d.q * g⁻¹) * (g * d.q * g⁻¹) = 1 := by
    calc (g * d.q * g⁻¹) * (g * d.q * g⁻¹) = g * (d.q * d.q) * g⁻¹ := by group
      _ = 1 := by rw [hqq]; group
  have hq'S : g * d.q * g⁻¹ ∈ d.S := c.involutions_in_S' hα h hP hQ hc hq'QS hq'2
  have hq'1 : g * d.q * g⁻¹ ≠ 1 := fun h1 => by
    have hq1 : d.q = 1 := by
      have h2 : g * d.q * g⁻¹ = g * 1 * g⁻¹ := by rw [h1]; group
      exact mul_left_cancel (mul_right_cancel h2)
    have hord := d.q_ord
    rw [hq1, orderOf_one] at hord
    omega
  have hq'q : g * d.q * g⁻¹ ≠ d.q := fun h1 => by
    apply hzQS
    have h2 : g * d.q = d.q * g := by
      calc g * d.q = g * d.q * g⁻¹ * g := by group
        _ = d.q * g := by rw [h1]
    have h3 : g⁻¹ * d.q * g = d.q := by
      calc g⁻¹ * d.q * g = g⁻¹ * (d.q * g) := by group
        _ = g⁻¹ * (g * d.q) := by rw [h2]
        _ = d.q := by group
    have hzq' : z = d.q := by rw [← hg, h3]
    rw [hzq']
    exact mem_sup_left (d.q_mem_Q h)
  obtain ⟨a, haA, ha⟩ := c.involution_conj_pi h hc hq'S hq'2 hq'1 hq'q
  refine isConj_iff.2 ⟨(a⁻¹ * g), ?_⟩
  have : cj (g * d.q * g⁻¹) a = (a⁻¹ * g) * d.q * (a⁻¹ * g)⁻¹ := by unfold cj; group
  rw [← this]
  exact ha

end CFSG.OddStandard.ChengHeld
