module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Pure

public section

namespace CFSG.OddStandard.ChengHeld.Sec1

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.Model (kind0)
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem eq_sixteen_of_dvd {a : ℕ} (h : a ∣ 16) (h8 : 8 < a) : a = 16 := by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases a <;> omega

namespace Cfg

variable {d : Datum A} (K : Cfg d)

include K

theorem fixed_iff {k : Kind} {y : G} (hy : y ∈ d.X)
    (hact : k.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi y) {s : G} (hs : s ∈ d.S) :
    cj s y = s ↔ s ∈ fixedSubG (kind0 k) K.c.famG :=
  (K.c.autFactsG K.h K.hP K.hQ k hy hact).fixed_eq rfl s hs

theorem fixedSub_le_S (k : Kind) : fixedSubG (kind0 k) K.c.famG ≤ d.S := by
  have hm : ∀ j : Fin 7, K.c.famG j ∈ d.S := fun j => by
    rw [← K.c.subtype_fam j]; exact (K.c.fam j).2
  cases k
  · simp only [fixedSubG, kind0, ite_true]
    rw [closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact hm 0
    · exact hm 1
    · exact d.S.mul_mem (hm 3) (hm 4)
    · exact hm 6
  · simp only [fixedSubG, kind0, show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true]
    rw [closure_le]
    rintro x (rfl | rfl | rfl)
    · exact hm 0
    · exact hm 1
    · exact hm 2
  · simp only [fixedSubG, kind0, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ite_false]
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact hm 0
    · exact d.S.mul_mem (d.S.mul_mem (d.S.mul_mem (hm 3) (hm 4)) (hm 6)) (hm 2)

theorem card_fixedSub {k : Kind} {y : G} (hy : y ∈ d.X)
    (hact : k.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi y) :
    Nat.card ↥(fixedSubG (kind0 k) K.c.famG) = (autData 2 (kind0 k)).1 := by
  have hA := K.c.autFactsG K.h K.hP K.hQ k hy hact
  have hset : {s : G | s ∈ d.S ∧ y⁻¹ * s * y = s} = (fixedSubG (kind0 k) K.c.famG : Set G) := by
    ext s
    constructor
    · rintro ⟨hs, h⟩
      exact (K.fixed_iff hy hact hs).1 h
    · intro h
      exact ⟨K.fixedSub_le_S k h, (K.fixed_iff hy hact (K.fixedSub_le_S k h)).2 h⟩
  have := hA.fixed_card
  rw [hset] at this
  rw [← this]
  exact Nat.card_coe_set_eq _

theorem mulam_mem_fixedSub : K.c.mu * K.c.lam ∈ fixedSubG (kind0 Kind.field) K.c.famG := by
  unfold fixedSubG kind0
  simp only [ite_true]
  exact subset_closure (by simp [Chart2.famG])

theorem xi_mem_fixedSub : K.c.xi ∈ fixedSubG (kind0 Kind.field) K.c.famG := by
  unfold fixedSubG kind0
  simp only [ite_true]
  exact subset_closure (by simp [Chart2.famG])

theorem c0_mem_fixedSub :
    K.c.mu * K.c.lam * K.c.xi * K.c.tau ∈ fixedSubG (kind0 Kind.unitary) K.c.famG := by
  unfold fixedSubG kind0
  simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ite_false]
  exact subset_closure (by simp [Chart2.famG])

local macro "dnorm " K:term : tactic =>
  `(tactic| simp only [mul_assoc, ($K).sort_pq, ($K).sort_tq, ($K).sort_tp, canc_q,
    ($K).canc_p, ($K).canc_t, ($K).pi_q, ($K).tau_q, ($K).tau_pi, q_mul_self,
    ($K).pi_sq, ($K).tau_sq, one_mul, mul_one])

theorem comm_mulam_xi : ⁅K.c.mu * K.c.lam, K.c.xi⁆ = K.c.pi := by
  rw [K.comm_mul_left K.mu_mem_S K.lam_mem_S K.xi_mem_S, K.comm_mu_xi, K.comm_lam_xi]
  dnorm K

theorem elemAb_bound {k : Kind} {w p : G} (hw : w ∈ d.X) (hp : p ∈ d.S)
    (hact : k.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi (cj w p))
    {F : Subgroup G} (hF : F ≤ d.S) (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hsq : ∀ x ∈ F, x * x = 1) (hcent : ∀ x ∈ F, w * x = x * w) :
    Nat.card F ≤ 8 ∧ (k = Kind.unitary → Nat.card F < 8) := by
  set w' : G := cj w p with hw'
  have hw'X : w' ∈ d.X := cj_mem_X d hw hp
  set F' : Subgroup G := F.map (MulAut.conj p⁻¹).toMonoidHom with hF'
  have hcardF' : Nat.card F' = Nat.card F :=
    Subgroup.card_map_of_injective (MulAut.conj p⁻¹).injective
  have hmemF' : ∀ x ∈ F', ∃ x₀ ∈ F, x = cj x₀ p := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    exact ⟨x₀, hx₀, by simp [cj]⟩
  have hF'S : F' ≤ d.S := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemF' x hx
    exact cj_mem_S d (d.S_le_X hp) (hF hx₀)
  have hF'comm : ∀ x ∈ F', ∀ y ∈ F', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hmemF' x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hmemF' y hy
    have := hcomm x₀ hx₀ y₀ hy₀
    unfold cj
    calc p⁻¹ * x₀ * p * (p⁻¹ * y₀ * p) = p⁻¹ * (x₀ * y₀) * p := by group
      _ = p⁻¹ * (y₀ * x₀) * p := by rw [this]
      _ = p⁻¹ * y₀ * p * (p⁻¹ * x₀ * p) := by group
  have hF'sq : ∀ x ∈ F', x * x = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemF' x hx
    unfold cj
    calc p⁻¹ * x₀ * p * (p⁻¹ * x₀ * p) = p⁻¹ * (x₀ * x₀) * p := by group
      _ = 1 := by rw [hsq x₀ hx₀]; group
  have hF'fix : ∀ x ∈ F', cj x w' = x := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemF' x hx
    have h1 : cj x₀ w = x₀ := cj_of_commute (show Commute x₀ w from (hcent x₀ hx₀).symm)
    have h2 : cj (cj x₀ p) (cj w p) = cj (cj x₀ w) p := by unfold cj; group
    rw [hw', h2, h1]
  have hF'C : F' ≤ fixedSubG (kind0 k) K.c.famG := fun x hx =>
    (K.fixed_iff hw'X hact (hF'S hx)).1 (hF'fix x hx)
  have hC : Nat.card ↥(fixedSubG (kind0 k) K.c.famG) = (autData 2 (kind0 k)).1 :=
    K.card_fixedSub hw'X hact
  have hdvd : Nat.card F' ∣ Nat.card ↥(fixedSubG (kind0 k) K.c.famG) :=
    Subgroup.card_dvd_of_le hF'C
  rw [← hcardF']
  cases k
  ·
    have hC16 : Nat.card ↥(fixedSubG (kind0 Kind.field) K.c.famG) = 16 := by rw [hC]; decide
    rw [hC16] at hdvd
    refine ⟨?_, fun h => nomatch h⟩
    by_contra hgt
    have h16 : Nat.card F' = 16 := eq_sixteen_of_dvd hdvd (by omega)
    have heq : F' = fixedSubG (kind0 Kind.field) K.c.famG :=
      Subgroup.eq_of_le_of_card_ge hF'C (by rw [hC16, h16])
    have hm1 : K.c.mu * K.c.lam ∈ F' := by rw [heq]; exact K.mulam_mem_fixedSub
    have hm2 : K.c.xi ∈ F' := by rw [heq]; exact K.xi_mem_fixedSub
    have hc := hF'comm _ hm1 _ hm2
    have h1 : ⁅K.c.mu * K.c.lam, K.c.xi⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc
    rw [K.comm_mulam_xi] at h1
    exact K.pi_ne_one h1
  ·
    have hC8 : Nat.card ↥(fixedSubG (kind0 Kind.graph) K.c.famG) = 8 := by rw [hC]; decide
    refine ⟨?_, fun h => nomatch h⟩
    have := Subgroup.card_le_of_le hF'C
    omega
  ·
    have hC8 : Nat.card ↥(fixedSubG (kind0 Kind.unitary) K.c.famG) = 8 := by rw [hC]; decide
    rw [hC8] at hdvd
    have hle : Nat.card F' ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have hlt : Nat.card F' < 8 := by
      refine lt_of_le_of_ne hle fun h8 => ?_
      have heq : F' = fixedSubG (kind0 Kind.unitary) K.c.famG :=
        Subgroup.eq_of_le_of_card_ge hF'C (by rw [hC8, h8])
      have hm : K.c.mu * K.c.lam * K.c.xi * K.c.tau ∈ F' := by rw [heq]; exact K.c0_mem_fixedSub
      have h1 := hF'sq _ hm
      have h2 := K.c.sq_mlxt K.h K.hP K.hQ
      rw [pow_two] at h2
      rw [h2] at h1
      exact K.pi_ne_one h1
    exact ⟨hlt.le, fun _ => hlt⟩

end Cfg

end CFSG.OddStandard.ChengHeld.Sec1
