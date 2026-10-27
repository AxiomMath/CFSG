module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Mb

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma mem_zpowers_eq_one_or {z v : G} (hz2 : z ^ 2 = 1)
    (hv : v ∈ Subgroup.zpowers z) : v = 1 ∨ v = z := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have h2 : z ^ (2 : ℤ) = 1 := by simpa using hz2
  rw [zpow_eq_zpow_emod m h2]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

private lemma phi_inv {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {y : G}
    (hy : y ∈ e4Y s) : f3phi s y⁻¹ = (f3phi s y)⁻¹ := by
  have h1 : f3phi s (y * y⁻¹) = f3phi s y * f3phi s y⁻¹ :=
    y56_phi_mul hH y hy y⁻¹ ((e4Y s).inv_mem hy)
  rw [mul_inv_cancel] at h1
  have h2 : f3phi s (1 : G) = 1 := by simp [f3phi]
  rw [h2] at h1
  calc f3phi s y⁻¹ = 1 * f3phi s y⁻¹ := by rw [one_mul]
    _ = ((f3phi s y)⁻¹ * f3phi s y) * f3phi s y⁻¹ := by rw [inv_mul_cancel]
    _ = (f3phi s y)⁻¹ * (f3phi s y * f3phi s y⁻¹) := by group
    _ = (f3phi s y)⁻¹ * 1 := by rw [← h1]
    _ = (f3phi s y)⁻¹ := by rw [mul_one]

private lemma e4Q_le_sup_C0 (c : Ctx5 G L) : e4Q c.s ≤ c.s.fr.E ⊔ C0 c.e := by
  refine sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_)
  exact Subgroup.mem_sup_right (by rw [c.intro5.gen]; exact Subgroup.subset_closure (by simp))

theorem y56_C0_le_C4 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : C0 c.e ≤ C4 c.s := by
  have htC4 : c.s.t ∈ C4 c.s :=
    (y56_C4_cand c hH).1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t))
  have hdC4 : c.d ∈ C4 c.s := (y56_C4_cand c hH).2.2.2.2.2
  rw [c.intro5.gen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact htC4
  · exact hdC4

theorem y56_C4_phi_Z (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ w ∈ C4 c.s, f3phi c.s w ∈ c.s.fr.Z → w ∈ c.s.fr.E ⊔ C0 c.e := by
  have hcand := y56_C4_cand c hH
  have hC4Y : C4 c.s ≤ e4Y c.s := hcand.2.1
  have hC4X0 : C4 c.s ⊓ e4X0 c.s = e4Q c.s := hcand.2.2.2.1
  have hdq : e4Q c.s ≤ c.s.fr.E ⊔ C0 c.e := e4Q_le_sup_C0 c
  have hdC4 : c.d ∈ C4 c.s := hcand.2.2.2.2.2
  have hdY : c.d ∈ e4Y c.s := hC4Y hdC4
  have hz2 : c.s.fr.z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one c.s.fr.z
    rwa [(lfactsA_of_setting hH.hS hH.hZ c.s).z_order] at h
  intro w hw hwZ
  have hwY : w ∈ e4Y c.s := hC4Y hw
  rw [SFrame.Z] at hwZ
  by_cases hw1 : f3phi c.s w = 1
  · have hwX0 : w ∈ e4X0 c.s := (y56_phi_eq_one hH w hwY).mp hw1
    have hmem : w ∈ C4 c.s ⊓ e4X0 c.s := Subgroup.mem_inf.mpr ⟨hw, hwX0⟩
    rw [hC4X0] at hmem
    exact hdq hmem
  · have hwz : f3phi c.s w = c.s.fr.z := by
      rcases mem_zpowers_eq_one_or hz2 hwZ with h | h
      · exact absurd h hw1
      · exact h
    have hdwC4 : c.d⁻¹ * w ∈ C4 c.s := (C4 c.s).mul_mem ((C4 c.s).inv_mem hdC4) hw
    have hdwY : c.d⁻¹ * w ∈ e4Y c.s := (e4Y c.s).mul_mem ((e4Y c.s).inv_mem hdY) hwY
    have hphi_dw : f3phi c.s (c.d⁻¹ * w) = 1 := by
      rw [y56_phi_mul hH c.d⁻¹ ((e4Y c.s).inv_mem hdY) w hwY, phi_inv hH hdY,
        y56_phi_d (c := c) hH, hwz, inv_mul_cancel]
    have hdwX0 : c.d⁻¹ * w ∈ e4X0 c.s := (y56_phi_eq_one hH (c.d⁻¹ * w) hdwY).mp hphi_dw
    have hmem : c.d⁻¹ * w ∈ C4 c.s ⊓ e4X0 c.s := Subgroup.mem_inf.mpr ⟨hdwC4, hdwX0⟩
    rw [hC4X0] at hmem
    have hw_eq : w = c.d * (c.d⁻¹ * w) := by group
    rw [hw_eq]
    exact (c.s.fr.E ⊔ C0 c.e).mul_mem (Subgroup.mem_sup_right c.d_mem) (hdq hmem)

theorem y56_comm_A_C4 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ a ∈ c.s.fr.A, ∀ w ∈ C4 c.s, ⁅a, w⁆ ∈ c.s.fr.E ⊔ C0 c.e := by
  intro a ha w hw
  have hAN : a ∈ normIn L c.s.fr.E := y56_A_le_NE hH ha
  have hN : a ∈ e4N c.s := y56_NL_le_N hH hAN
  have hwY : w ∈ e4Y c.s := (y56_C4_cand c hH).2.1 hw
  have hC4n : a * w * a⁻¹ ∈ C4 c.s := (y56_C4_cand c hH).2.2.1 a hAN w hw
  have hcommC4 : ⁅a, w⁆ ∈ C4 c.s := by
    rw [commutatorElement_def]
    exact (C4 c.s).mul_mem hC4n ((C4 c.s).inv_mem hw)
  have hYconj : a * w * a⁻¹ ∈ e4Y c.s := y56_N_norm_Y hH a hN w hwY
  have hphi : f3phi c.s ⁅a, w⁆ = ⁅a, f3phi c.s w⁆ := by
    rw [commutatorElement_def,
      y56_phi_mul hH (a * w * a⁻¹) hYconj w⁻¹ ((e4Y c.s).inv_mem hwY),
      y56_phi_conj hH a hN w, phi_inv hH hwY, commutatorElement_def]
  have hZ : f3phi c.s ⁅a, w⁆ ∈ c.s.fr.Z := by
    rw [hphi]
    exact (lfactsA_of_setting hH.hS hH.hZ c.s).comm_A a ha (f3phi c.s w)
      (s3_E_le_A c.s (y56_phi_mem hH w hwY))
  exact y56_C4_phi_Z c hH ⁅a, w⁆ hcommC4 hZ

theorem y56_comm_C1_C4 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ⁅C1 c.e, C4 c.s⁆ ≤ c.s.fr.E ⊔ C0 c.e := by
  rw [Subgroup.commutator_le]
  intro u hu w hw
  change u ∈ c.s.fr.A ⊔ C0 c.e at hu
  have hwY : w ∈ e4Y c.s := (y56_C4_cand c hH).2.1 hw
  have hAnormC0 : ∀ x ∈ c.s.fr.A, ∀ d0 ∈ C0 c.e, x * d0 * x⁻¹ ∈ C0 c.e := by
    intro x hx d0 hd0
    have hcomm : x * d0 = d0 * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd0).2 x hx
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hd0
  obtain ⟨a, ha, d0, hd0, rfl⟩ :=
    mem_sup_of_normalizes (T := c.s.fr.A) (C := C0 c.e) hAnormC0 u hu
  have hd0C4 : d0 ∈ C4 c.s := y56_C0_le_C4 c hH hd0
  have hcomm_d0 : ⁅d0, w⁆ ∈ e4Q c.s :=
    y56_Y_comm c hH d0 ((y56_C4_cand c hH).2.1 hd0C4) w hwY
  have hcomm_a : ⁅a, w⁆ ∈ c.s.fr.E ⊔ C0 c.e := y56_comm_A_C4 c hH a ha w hw
  have hN : a ∈ e4N c.s := y56_NL_le_N hH (y56_A_le_NE hH ha)
  have haq : a * ⁅d0, w⁆ * a⁻¹ ∈ c.s.fr.E ⊔ C0 c.e :=
    e4Q_le_sup_C0 c (y56_N_norm_Q hH a hN ⁅d0, w⁆ hcomm_d0)
  have hid : ⁅a * d0, w⁆ = a * ⁅d0, w⁆ * a⁻¹ * ⁅a, w⁆ := by
    simp only [commutatorElement_def]; group
  rw [hid]
  exact (c.s.fr.E ⊔ C0 c.e).mul_mem haq hcomm_a

end CFSG.OddStandard.HigherRank.YamadaG23
