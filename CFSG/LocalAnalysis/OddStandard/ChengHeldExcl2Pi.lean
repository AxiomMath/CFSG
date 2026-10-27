module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Basic

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

namespace Cfg

variable (K : Cfg d 0)

include K

theorem isConj_q_pi_of_field {z : G} (hzQS : z ∉ d.QS) (hzq : IsConj d.q z)
    (hact : Kind.field.Act 0 K.c.t K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi z) :
    IsConj d.q K.c.pi := by
  have hzt : cj K.c.t z = K.c.t := by
    simp only [Kind.Act, ↓reduceIte] at hact
    exact hact.1
  have hcomm : z * K.c.t = K.c.t * z := by
    unfold cj at hzt
    calc z * K.c.t = z * (z⁻¹ * K.c.t * z) := by rw [hzt]
      _ = K.c.t * z := by group
  exact K.c.fuse_of_commutes K.hα K.h K.hP K.hQ K.hc hzQS hzq hcomm

theorem isConj_q_pi_of_graph {z : G} (hzX : z ∈ d.X) (hzQS : z ∉ d.QS) (hz2 : z * z = 1)
    (hzq : IsConj d.q z)
    (hact : Kind.graph.Act 0 K.c.t K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi z) :
    IsConj d.q K.c.pi := by
  obtain ⟨g₀, hg₀, hgX⟩ := d.exists_conj_config K.h hzq
  have hVfix := K.c.graph_fixes_V K.hα K.h K.hP K.hQ hact
  have hVS : K.c.V ≤ d.S := K.c.V_le_S K.h
  have hVz : ∀ v ∈ K.c.V, v * z = z * v := by
    intro v hv
    have h1 := hVfix v hv
    calc v * z = z * (z⁻¹ * v * z) := by group
      _ = z * v := by rw [h1]
  have hVX : ∀ v ∈ K.c.V, g₀ * v * g₀⁻¹ ∈ d.X := fun v hv =>
    hgX v (d.S_le_X (hVS hv)) (hVz v hv)
  obtain ⟨x, hxV, hx1, hxQS⟩ := K.exists_conj_mem_QS (E := K.c.V)
    (by rw [K.sf.card_V]; norm_num) hVX
  have hxS : x ∈ d.S := hVS hxV
  obtain ⟨-, hπ2⟩ := K.fuse_aux hzX hzQS hg₀ hgX (d.S_le_X hxS) (mem_sup_right hxS) (hVz x hxV)
    (K.sf.V_sq x hxV) hx1 hxQS
  have hzt : cj K.c.t z = K.c.t⁻¹ := by
    simp only [Kind.Act, ↓reduceIte] at hact
    exact hact.1
  obtain ⟨s, hs, hsz⟩ := K.c.coset_conj_graph K.hα K.h K.hP K.hQ hact hz2 hzt x hxV
  have hzzx : IsConj z (z * x) := by
    rw [← hVz x hxV]
    exact isConj_of_cj_eq hsz
  exact hzq.trans (hzzx.trans hπ2.symm)

end Cfg

namespace Cfg

variable {α : ℕ} (K : Cfg d α)

include K

theorem isConj_q_pi_of_unitary {z : G} (hzX : z ∈ d.X) (hzQS : z ∉ d.QS) (hz2 : z * z = 1)
    (hzq : IsConj d.q z)
    (hact : Kind.unitary.Act α K.c.t K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi z) :
    IsConj d.q K.c.pi := by
  obtain ⟨g₀, hg₀, hgX⟩ := d.exists_conj_config K.h hzq
  obtain ⟨s, hsS, hsz, hs2⟩ := K.c.unitary_sq_witness K.hα K.h K.hP K.hQ K.hS2 hzX hact
  have hsz' : s * z = z * s := by
    calc s * z = z * (z⁻¹ * s * z) := by group
      _ = z * s := by rw [hsz]
  obtain ⟨x, hx, hxs⟩ : ∃ x, (x = K.c.pi ∨ x = K.c.pi * d.q) ∧ s * s = x := ⟨s * s, hs2, rfl⟩
  have hpi2 : K.c.pi * K.c.pi = 1 := by simpa [pow_two] using K.c.frame.pi2
  have hqq : d.q * d.q = 1 := Sec1.q_mul_self d
  have hpiq : K.c.pi * d.q = d.q * K.c.pi := d.comm_Q_S K.q_mem_Q K.c.mem.1
  have hxS : x ∈ d.S := hxs ▸ mul_mem hsS hsS
  have hxz : x * z = z * x := by
    rw [← hxs]
    calc s * s * z = s * (s * z) := by group
      _ = s * (z * s) := by rw [hsz']
      _ = (s * z) * s := by group
      _ = (z * s) * s := by rw [hsz']
      _ = z * (s * s) := by group
  have hx2 : x * x = 1 := by
    rcases hx with rfl | rfl
    · exact hpi2
    · calc K.c.pi * d.q * (K.c.pi * d.q) = K.c.pi * (d.q * K.c.pi) * d.q := by group
        _ = K.c.pi * (K.c.pi * d.q) * d.q := by rw [hpiq]
        _ = (K.c.pi * K.c.pi) * (d.q * d.q) := by group
        _ = 1 := by rw [hpi2, hqq, mul_one]
  have hx1 : x ≠ 1 := by
    rcases hx with rfl | rfl
    · exact K.c.pi_ne_one
    · intro h1
      apply K.c.pi_ne_q K.hα K.h K.hP K.hQ
      rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hqq]
  have hx' : g₀ * x * g₀⁻¹ ∈ d.QS := by
    have hsX : g₀ * s * g₀⁻¹ ∈ d.X := hgX s (d.S_le_X hsS) hsz'
    have e : g₀ * x * g₀⁻¹ = (g₀ * s * g₀⁻¹) * (g₀ * s * g₀⁻¹) := by rw [← hxs]; group
    rw [e]
    exact K.c.sq_mem_QS K.hα K.h K.hP K.hQ hsX
  obtain ⟨-, hπ2⟩ := K.fuse_aux hzX hzQS hg₀ hgX (d.S_le_X hxS) (mem_sup_right hxS) hxz hx2 hx1 hx'
  have hzxz : z * x = x * z := hxz.symm
  have hzx2 : (z * x) * (z * x) = 1 := by
    calc z * x * (z * x) = z * (x * z) * x := by group
      _ = z * (z * x) * x := by rw [hxz]
      _ = (z * z) * (x * x) := by group
      _ = 1 := by rw [hz2, hx2, mul_one]
  obtain ⟨s', hs', hs'z⟩ := K.c.coset_conj_unitary K.hα K.h K.hP K.hQ hzX hact hz2
    (a := z) ⟨1, one_mem _, by simp⟩ hz2 (b := z * x) ⟨x, hxS, hzxz⟩ hzx2
  exact hzq.trans ((isConj_of_cj_eq hs'z).trans hπ2.symm)

end Cfg

namespace Cfg

variable (K : Cfg d 0)

include K

theorem isConj_q_pi_zero : IsConj d.q K.c.pi := by
  by_contra hnc
  obtain ⟨k, y, x, hrep, hxQ, hzq, hz2⟩ := K.exists_pure_involution hnc
  obtain ⟨hyX, hyQS, hact⟩ := K.c.rep_mem k y hrep
  have hzX : y * x ∈ d.X := d.X.mul_mem hyX (d.Q_le_X hxQ)
  have hzQS : y * x ∉ d.QS := fun h => hyQS (by
    have := mul_mem h (d.QS.inv_mem (mem_sup_left hxQ))
    simpa using this)
  have hact' := K.act_mul_Q hyX hxQ hact
  cases k
  · exact hnc (K.isConj_q_pi_of_field hzQS hzq hact')
  · exact hnc (K.isConj_q_pi_of_graph hzX hzQS hz2 hzq hact')
  · exact hnc (K.isConj_q_pi_of_unitary hzX hzQS hz2 hzq hact')

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
