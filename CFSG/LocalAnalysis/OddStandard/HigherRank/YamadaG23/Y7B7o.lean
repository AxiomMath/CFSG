module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7n

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7b_comm_X7_N_le_X7 (c : Ctx7 G L) (hb : B5Std c) :
    ⁅X7 c.s, normIn c.s.H c.s.fr.B⁆ ≤ X7 c.s := by
  rw [Subgroup.commutator_le]
  intro x hx n hn
  have h1 : n * x⁻¹ * n⁻¹ ∈ X7 c.s :=
    y7b_X7_normal c hb n (y7b_N_le_X c hb hn) x⁻¹ ((X7 c.s).inv_mem hx)
  have h2 : x * (n * x⁻¹ * n⁻¹) ∈ X7 c.s := (X7 c.s).mul_mem hx h1
  rw [show ⁅x, n⁆ = x * (n * x⁻¹ * n⁻¹) by rw [commutatorElement_def]; group]
  exact h2

theorem y7b_C7_eq (c : Ctx7 G L) (hb : B5Std c) :
    C7 c.s = ⁅X7 c.s, normIn c.s.H c.s.fr.B⁆ ⊔ y7bW c.s := by
  have hpc : pCoreOf 2 ⁅X7 c.s, normIn c.s.H c.s.fr.B⁆ =
      ⁅X7 c.s, normIn c.s.H c.s.fr.B⁆ :=
    y7b_pCoreOf_eq_self ((y7b_X7_isPGroup c hb).to_le (y7b_comm_X7_N_le_X7 c hb))
  unfold C7
  rw [hpc]

theorem y7b_C7_le_X7 (c : Ctx7 G L) (hb : B5Std c) : C7 c.s ≤ X7 c.s := by
  rw [y7b_C7_eq c hb]
  exact sup_le (y7b_comm_X7_N_le_X7 c hb)
    ((y7b_W_le_X0 c hb).trans (y7b_X0_le_X7 c hb))

theorem y7b_W_le_C7 (c : Ctx7 G L) (hb : B5Std c) : y7bW c.s ≤ C7 c.s := by
  rw [y7b_C7_eq c hb]
  exact le_sup_right

theorem y7b_C7_normal (c : Ctx7 G L) (hb : B5Std c) :
    (∀ y ∈ X7 c.s, ∀ x ∈ C7 c.s, y * x * y⁻¹ ∈ C7 c.s) ∧
      ∀ n ∈ normIn c.s.H c.s.fr.B, ∀ x ∈ C7 c.s, n * x * n⁻¹ ∈ C7 c.s := by
  rw [y7b_C7_eq c hb]
  exact ext_normal (y7b_extCtx1 c hb)

theorem y7b_hfix1 (c : Ctx7 G L) (hb : B5Std c) {k : G} (hkN : k ∈ normIn L c.s.fr.B)
    (hfp : ∀ u ∈ y7bBM c.s, u⁻¹ * (k * u * k⁻¹) ∈ M3 c.s → u ∈ M3 c.s) :
    ∀ y ∈ X7 c.s, y⁻¹ * (k * y * k⁻¹) ∈ y7bX0 c.s → y ∈ y7bX0 c.s := by
  haveI := y7b_M3_normal_BM c hb
  obtain ⟨θ, hθ, hθeq⟩ := y7b_exists_theta c hb
  have hkNH : k ∈ normIn c.s.H c.s.fr.B :=
    ⟨s3_L_le_H c.s hb.hH.hS hkN.1, hkN.2⟩
  have hkX : k ∈ y7bX c.s := y7b_N_le_X c hb hkNH
  intro y hy hyX0
  have hy' : k * y * k⁻¹ ∈ X7 c.s := y7b_X7_normal c hb k hkX y hy
  have huBM : ⁅y, c.s.t⁆ ∈ y7bBM c.s := y7b_comm_t_mem_BM c hb y (y7b_X7_le_X c hy)
  have hu'BM : k * ⁅y, c.s.t⁆ * k⁻¹ ∈ y7bBM c.s :=
    y7b_X_norm_BM c hb k hkX ⁅y, c.s.t⁆ huBM
  let u : ↥(y7bBM c.s) := ⟨⁅y, c.s.t⁆, huBM⟩
  let u' : ↥(y7bBM c.s) := ⟨k * ⁅y, c.s.t⁆ * k⁻¹, hu'BM⟩
  have hθy : θ ⟨y, hy⟩ = QuotientGroup.mk u := by
    refine (hθ _ u).mpr ?_
    dsimp only [u]
    rw [inv_mul_cancel]
    exact (M3 c.s).one_mem
  have hθy' : θ ⟨k * y * k⁻¹, hy'⟩ = QuotientGroup.mk u' :=
    hθeq k hkNH ⟨y, hy⟩ ⟨k * y * k⁻¹, hy'⟩ rfl u u' rfl hθy
  have haX7 : y⁻¹ * (k * y * k⁻¹) ∈ X7 c.s :=
    (X7 c.s).mul_mem ((X7 c.s).inv_mem hy) hy'
  have hcommM3 : ⁅y⁻¹ * (k * y * k⁻¹), c.s.t⁆ ∈ M3 c.s :=
    (y7b_X0_iff c hb haX7).mp hyX0
  have hθa : θ ⟨y⁻¹ * (k * y * k⁻¹), haX7⟩ = 1 := by
    refine (hθ _ (1 : ↥(y7bBM c.s))).mpr ?_
    simpa using hcommM3
  have hprod : θ ⟨y⁻¹ * (k * y * k⁻¹), haX7⟩ =
      (θ ⟨y, hy⟩)⁻¹ * θ ⟨k * y * k⁻¹, hy'⟩ := by
    have heq : (⟨y⁻¹ * (k * y * k⁻¹), haX7⟩ : ↥(X7 c.s)) =
        ⟨y, hy⟩⁻¹ * ⟨k * y * k⁻¹, hy'⟩ := by
      ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [heq, map_mul, map_inv]
  have heqθ : θ ⟨y, hy⟩ = θ ⟨k * y * k⁻¹, hy'⟩ :=
    inv_mul_eq_one.mp (hprod.symm.trans hθa)
  have hmemG : (u : G)⁻¹ * (u' : G) ∈ M3 c.s := by
    have h : (u' : G)⁻¹ * (u : G) ∈ M3 c.s :=
      (hθ ⟨y, hy⟩ u').mp (heqθ.trans hθy')
    simpa only [mul_inv_rev, inv_inv] using (M3 c.s).inv_mem h
  have huM3 : (u : G) ∈ M3 c.s := hfp (u : G) u.2 (by simpa only [u, u'] using hmemG)
  exact (y7b_X0_iff c hb hy).mpr (by simpa only [u] using huM3)

theorem y7b_C7_inf_X0 (c : Ctx7 G L) (hb : B5Std c) : C7 c.s ⊓ y7bX0 c.s = y7bW c.s := by
  obtain ⟨k, hkN, hk3, hk1, htrans, hfp, hknorm⟩ := y7b_exists_k c hb
  have hf3P_le_W : f3P c.s ≤ y7bW c.s :=
    sup_le le_sup_left (Subgroup.zpowers_le.mpr (y7b_t_mem_W c hb))
  have hkNH : k ∈ normIn c.s.H c.s.fr.B :=
    ⟨s3_L_le_H c.s hb.hH.hS hkN.1, hkN.2⟩
  have hkn : ∀ n ∈ normIn c.s.H c.s.fr.B, ∃ p ∈ y7bW c.s,
      n * k * n⁻¹ = k * p ∨ n * k * n⁻¹ = k⁻¹ * p := by
    intro n hn
    obtain ⟨p, hp, hpk⟩ := f3_N_conj_k hb.hH hkN hknorm n hn
    exact ⟨p, hf3P_le_W hp, hpk⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨hxC7, hxX0⟩ := Subgroup.mem_inf.mp hx
    rw [y7b_C7_eq c hb] at hxC7
    exact ext_nu (y7b_extCtx1 c hb) (y7b_X7_sq_mem_W c hb) hkNH
      (by rw [hk3]; exact (y7bW c.s).one_mem) hkn (y7b_hfix1 c hb hkN hfp) x hxX0 hxC7
  · exact le_inf (y7b_W_le_C7 c hb) (y7b_W_le_X0 c hb)

theorem y7b_theta_onto_X7 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ u ∈ y7bBM c.s, ∃ y ∈ X7 c.s, u⁻¹ * ⁅y, c.s.t⁆ ∈ M3 c.s := by
  intro u huBM
  by_cases huM3 : u ∈ M3 c.s
  · refine ⟨1, (X7 c.s).one_mem, ?_⟩
    simpa [commutatorElement_one_left] using (M3 c.s).inv_mem huM3
  · obtain ⟨m₀, hm₀M4, hm₀sq, hm₀tE, hm₀tNM3⟩ := y7b_exists_seed c hb
    have hm₀X7 : m₀ ∈ X7 c.s := y7b_M4_le_X7 c hb hm₀M4
    have hu₁BM : ⁅m₀, c.s.t⁆ ∈ y7bBM c.s :=
      Subgroup.mem_sup_left (y56_E_le_B hb.hH hm₀tE)
    obtain ⟨k, hkN, hk3, hk1, htrans, hfp, hknorm⟩ := y7b_exists_k c hb
    obtain ⟨i, hi⟩ := htrans ⁅m₀, c.s.t⁆ hu₁BM hm₀tNM3 u huBM huM3
    have hkiN : k ^ i ∈ normIn L c.s.fr.B := Subgroup.pow_mem (normIn L c.s.fr.B) hkN i
    have hkiH : k ^ i ∈ c.s.H := s3_L_le_H c.s hb.hH.hS hkiN.1
    have hkiX : k ^ i ∈ y7bX c.s := y7b_N_le_X c hb ⟨hkiH, hkiN.2⟩
    have hyX7 : k ^ i * m₀ * (k ^ i)⁻¹ ∈ X7 c.s :=
      y7b_X7_normal c hb (k ^ i) hkiX m₀ hm₀X7
    refine ⟨k ^ i * m₀ * (k ^ i)⁻¹, hyX7, ?_⟩
    rw [y7b_comm_conj_of_mem_H c hkiH m₀]
    exact hi

end CFSG.OddStandard.HigherRank.YamadaG23
