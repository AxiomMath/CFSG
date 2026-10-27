module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitInvol
public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitQ
public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitFuse
public import Certificates.Certificate6137
public import Certificates.Certificate6138
public import Certificates.Certificate6139

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.unitary_structure_full
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hk : c.kinds = {Kind.unitary}) :
    α = 0 ∧ d.Q = zpowers c.t ∧ ∃ z ∈ d.X, z * z = 1 ∧
      Kind.unitary.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi z ∧
      d.X = Subgroup.closure ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi, z} : Set G) ∧
      Nat.card d.X = 512 := by
  have hfus := c.isConj_q_pi_unitary hα h hP hQ hS2 hc hk
  have hα0 := c.alpha_eq_zero_of_isConj hα h hP hQ hS2 hc hfus
  have hQle := c.Q_le_zpowers_t_of_isConj hα h hP hQ hS2 hc hk hfus
  have hStle : zpowers c.t ≤ d.S := zpowers_le.2 c.t_mem.2
  have hQS : d.Q ≤ d.S := hQle.trans hStle
  have hQSeq : d.QS = d.S := sup_eq_right.2 hQS
  have hS := c.sFacts hα h hP hQ
  obtain ⟨-, -, y, hy⟩ := c.rep_of_kinds_unitary hk
  obtain ⟨hyX, hyQS, hyact⟩ := c.rep_mem Kind.unitary y hy
  obtain ⟨x, hx, hxinv⟩ := c.exists_involution_unitary hα hα0 h hP hQ hS2 hc hg hact hk hfus hy
  have hxS : x ∈ d.S := hQS hx
  have hzX : y * x ∈ d.X := d.X.mul_mem hyX (d.Q_le_X hx)
  have hzact := c.act_mul_Q Kind.unitary hx hyact
  refine ⟨hα0, le_antisymm hQle (zpowers_le.2 c.t_mem.1), y * x, hzX, hxinv, hzact, ?_, ?_⟩
  ·
    have hSCl : d.S ≤ Subgroup.closure ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi, y * x} :
        Set G) := by
      rw [← c.gen]
      exact Subgroup.closure_mono (by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with h | h | h | h | h | h | h <;> simp [h])
    have hzCl : y * x ∈ Subgroup.closure ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi, y * x} :
        Set G) :=
      Subgroup.subset_closure (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true])
    have hyCl : y ∈ Subgroup.closure ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi, y * x} :
        Set G) := by
      have := Subgroup.mul_mem _ hzCl (Subgroup.inv_mem _ (hSCl hxS))
      simpa using this
    refine le_antisymm (fun x' hx' => ?_) ((Subgroup.closure_le _).2 ?_)
    · by_cases hx'S : x' ∈ d.S
      · exact hSCl hx'S
      · have hx'QS : x' ∉ d.QS := by rwa [hQSeq]
        obtain ⟨u, hu, rfl⟩ := c.cover_unitary hk hy hx' hx'QS
        rw [hQSeq] at hu
        exact Subgroup.mul_mem _ (hSCl hu) hyCl
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact d.S_le_X c.t_mem.2
      · exact d.S_le_X c.mem.1
      · exact d.S_le_X c.mem.2.1
      · exact d.S_le_X c.mem.2.2.1
      · exact d.S_le_X c.mem.2.2.2.1
      · exact d.S_le_X c.mem.2.2.2.2.1
      · exact d.S_le_X c.mem.2.2.2.2.2
      · exact hzX
  ·
    have hSX : d.S ≤ d.X := d.S_le_X
    have hyyS : y * y ∈ d.S := hQS (c.sq_mem_Q hα h hP hQ Kind.unitary hyX hyact)
    have hidx : (d.S.subgroupOf d.X).index = 2 := by
      refine Subgroup.index_eq_two_iff.2 ⟨⟨y, hyX⟩, fun b => ?_⟩
      have hbX : (b : G) ∈ d.X := b.2
      show Xor ((b : G) * y ∈ d.S) ((b : G) ∈ d.S)
      by_cases hbS : (b : G) ∈ d.S
      · refine Or.inr ⟨hbS, fun hby => hyQS ?_⟩
        have h1 : y ∈ d.S := by simpa using d.S.mul_mem (d.S.inv_mem hbS) hby
        rw [hQSeq]
        exact h1
      · refine Or.inl ⟨?_, hbS⟩
        have hbQS : (b : G) ∉ d.QS := by rwa [hQSeq]
        obtain ⟨u, hu, hbu⟩ := c.cover_unitary hk hy hbX hbQS
        rw [hQSeq] at hu
        rw [hbu, mul_assoc]
        exact d.S.mul_mem hu hyyS
    have hmul := Subgroup.relIndex_mul_card d.S d.X
    rw [inf_eq_left.2 hSX] at hmul
    rw [← hmul]
    have h2 : d.S.relIndex d.X = 2 := hidx
    rw [h2, hS.card_S]

theorem Chart4.unitary_structure
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hk : c.kinds = {Kind.unitary}) :
    α = 0 ∧ ∃ z ∈ d.X, z * z = 1 ∧ Kind.unitary.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi z ∧
      d.X = Subgroup.closure ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi, z} : Set G) ∧
      Nat.card d.X = 512 := by
  obtain ⟨hα0, -, hz⟩ := c.unitary_structure_full hα h hP hQ hS2 hc hg hact hk
  exact ⟨hα0, hz⟩

theorem Chart4.unitary_structure_cert
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hk : c.kinds = {Kind.unitary}) :
    α = 0 ∧ ∃ z ∈ d.X, z * z = 1 ∧ Kind.unitary.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi z ∧
      d.X = Subgroup.closure ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi, z} : Set G) ∧
      Nat.card d.X = 512 :=
  c.unitary_structure hα h Certificates.certificate6137 Certificates.certificate6138
    Certificates.certificate6139 hc hg hact hk

end CFSG.OddStandard.ChengHeld
