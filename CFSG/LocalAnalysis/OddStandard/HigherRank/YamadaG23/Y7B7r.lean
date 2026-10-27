module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7q

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_theta_onto_M7 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ u ∈ y7bBM c.s, ∃ y ∈ M7 c.s, u⁻¹ * ⁅y, c.s.t⁆ ∈ M3 c.s := by
  obtain ⟨k, hkN, -, -, -, hfp, -⟩ := y7b_exists_k c hb
  have hkNH : k ∈ normIn c.s.H c.s.fr.B := ⟨s3_L_le_H c.s hb.hH.hS hkN.1, hkN.2⟩
  have hkY : ∀ y ∈ C7 c.s, k * y * k⁻¹ ∈ C7 c.s := (y7b_C7_normal c hb).2 k hkNH
  intro u hu
  obtain ⟨z, hzC7, hzmem⟩ :=
    y7b_theta_comm_onto (Y := C7 c.s) c hb hkN hfp (y7b_C7_le_X7 c hb) hkY
      (y7b_theta_onto_C7 c hb) u hu
  refine ⟨⁅z, k⁆, ?_, hzmem⟩
  rw [M7]
  exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hzC7 hkN)

theorem y7b_C7_cases_M7_t (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ C7 c.s, y ∈ M7 c.s ∨ ∃ m ∈ M7 c.s, y = m * c.s.t := by
  intro y hy
  have hyX7 : y ∈ X7 c.s := y7b_C7_le_X7 c hb hy
  have huBM : ⁅y, c.s.t⁆ ∈ y7bBM c.s :=
    y7b_comm_t_mem_BM c hb y (y7b_X7_le_X c hyX7)
  obtain ⟨x, hxM7, hxmem⟩ := y7b_theta_onto_M7 c hb ⁅y, c.s.t⁆ huBM
  have hxC7 : x ∈ C7 c.s := y7b_M7_le_C7 c hb hxM7
  have hxX7 : x ∈ X7 c.s := y7b_C7_le_X7 c hb hxC7
  have hmemX0 : x⁻¹ * y ∈ y7bX0 c.s :=
    y7b_inv_mul_mem_X0 (x := y) (m := x) c hb hyX7 hxX7 hxmem
  have hmemC7 : x⁻¹ * y ∈ C7 c.s :=
    (C7 c.s).mul_mem ((C7 c.s).inv_mem hxC7) hy
  have hmemW : x⁻¹ * y ∈ y7bW c.s := by
    rw [← y7b_C7_inf_X0 c hb]
    exact Subgroup.mem_inf.mpr ⟨hmemC7, hmemX0⟩
  obtain ⟨w, hwBM, hw | hw⟩ := (y7b_mem_W c hb).mp hmemW
  · refine Or.inl ?_
    have hxy : y = x * w := by
      calc y = x * (x⁻¹ * y) := by group
        _ = x * w := by rw [hw]
    rw [hxy]
    exact (M7 c.s).mul_mem hxM7 (y7b_BM_le_M7 c hb hwBM)
  · refine Or.inr ⟨x * w, (M7 c.s).mul_mem hxM7 (y7b_BM_le_M7 c hb hwBM), ?_⟩
    calc y = x * (x⁻¹ * y) := by group
      _ = x * (w * c.s.t) := by rw [hw]
      _ = (x * w) * c.s.t := by group

theorem y7b_C7_eq_M7_t (c : Ctx7 G L) (hb : B5Std c) :
    C7 c.s = M7 c.s ⊔ zpowers c.s.t := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rcases y7b_C7_cases_M7_t c hb y hy with hyM7 | ⟨m, hmM7, rfl⟩
    · exact Subgroup.mem_sup_left hyM7
    · exact Subgroup.mul_mem_sup hmM7 (Subgroup.mem_zpowers c.s.t)
  · exact sup_le (y7b_M7_le_C7 c hb)
      (Subgroup.zpowers_le.mpr (y7b_W_le_C7 c hb (y7b_t_mem_W c hb)))

theorem y7b_exists_V2_not_comm_t (c : Ctx7 G L) (hb : B5Std c) :
    ∃ v ∈ V2 c.e, ⁅v, c.s.t⁆ ≠ 1 := by
  by_contra h
  push Not at h
  have hbot : cen c.s.fr.B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro f hf
    obtain ⟨v, hv, hvf⟩ := y7b_phi_V2 c hb f hf
    rw [← hvf]
    exact h v hv
  have hcard := y7b_card_V hb.hH
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem y7b_BM_cent_V2 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ x ∈ y7bBM c.s, ∀ v ∈ V2 c.e, x * v = v * x := by
  intro x hx v hv
  obtain ⟨b, hbB, m, hmM3, rfl⟩ := (y7b_mem_BM c hb).mp hx
  have hbv : b * v = v * b := hb.h72.1.2.1 b hbB v hv
  have hmv : m * v = v * m :=
    congrArg Subtype.val
      ((y7b_M3_elem c hb).1.is_comm.comm ⟨m, hmM3⟩ ⟨v, (Subgroup.mem_inf.mp hv).1⟩)
  calc b * m * v = b * (m * v) := by group
    _ = b * (v * m) := by rw [hmv]
    _ = (b * v) * m := by group
    _ = (v * b) * m := by rw [hbv]
    _ = v * (b * m) := by group

theorem y7b_comm_W_NL (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ y7bW c.s, ∀ n ∈ normIn L c.s.fr.B, ⁅y, n⁆ ∈ y7bBM c.s := by
  intro y hy n hn
  have hXn : n ∈ y7bX c.s :=
    y7b_N_le_X c hb ⟨s3_L_le_H c.s hb.hH.hS hn.1, hn.2⟩
  have hnt : c.s.t * n = n * c.s.t :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (s3_L_le_H c.s hb.hH.hS hn.1)).symm
  have ht2 : c.s.t * c.s.t = 1 := by
    rw [← pow_two, ← c.s.t_order]
    exact pow_orderOf_eq_one c.s.t
  have hwmem : ∀ w ∈ y7bBM c.s, ⁅w, n⁆ ∈ y7bBM c.s := by
    intro w hw
    have hmem : n * w⁻¹ * n⁻¹ ∈ y7bBM c.s :=
      y7b_X_norm_BM c hb n hXn w⁻¹ ((y7bBM c.s).inv_mem hw)
    have hrew : ⁅w, n⁆ = w * (n * w⁻¹ * n⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hrew]
    exact (y7bBM c.s).mul_mem hw hmem
  obtain ⟨w, hw, hyw | hyw⟩ := (y7b_mem_W c hb).mp hy
  · rw [hyw]
    exact hwmem w hw
  · rw [hyw]
    have htinv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht2
    have hconj : c.s.t * n * c.s.t = n := by
      rw [hnt, mul_assoc, ht2, mul_one]
    have heq : ⁅w * c.s.t, n⁆ = ⁅w, n⁆ := by
      simp only [commutatorElement_def]
      rw [mul_inv_rev, htinv]
      calc (w * c.s.t) * n * (c.s.t * w⁻¹) * n⁻¹
          = w * (c.s.t * n * c.s.t) * w⁻¹ * n⁻¹ := by group
        _ = w * n * w⁻¹ * n⁻¹ := by rw [hconj]
    rw [heq]
    exact hwmem w hw

theorem y7b_M7_le_cent_V2 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ x ∈ M7 c.s, ∀ v ∈ V2 c.e, x * v = v * x := by
  obtain ⟨u, huC7, hut, -, huV2, -⟩ := y7b_exists_seed2 c hb
  have hBcent : c.s.fr.B ≤ Subgroup.centralizer (V2 c.e : Set G) := by
    intro b hbB
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hb.h72.1.2.1 b hbB v hv).symm
  have hM3cent : M3 c.s ≤ Subgroup.centralizer (V2 c.e : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvM3 : v ∈ M3 c.s := (Subgroup.mem_inf.mp hv).1
    exact (congrArg Subtype.val
      ((y7b_M3_elem c hb).1.is_comm.comm ⟨m, hm⟩ ⟨v, hvM3⟩)).symm
  have hBMcent : y7bBM c.s ≤ Subgroup.centralizer (V2 c.e : Set G) :=
    sup_le hBcent hM3cent
  have hconj : ∀ m ∈ normIn L c.s.fr.B, ∀ p ∈ Subgroup.centralizer (V2 c.e : Set G),
      m * p * m⁻¹ ∈ Subgroup.centralizer (V2 c.e : Set G) := by
    intro m hm p hp
    have hmN : m ∈ normalizer (V2 c.e : Set G) :=
      y7b_NH_le_NV2 c hb ⟨s3_L_le_H c.s hb.hH.hS hm.1, hm.2⟩
    have hminv : m⁻¹ ∈ normalizer (V2 c.e : Set G) :=
      (Subgroup.normalizer (V2 c.e : Set G)).inv_mem hmN
    rw [Subgroup.mem_centralizer_iff] at hp ⊢
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V2 c.e := by
      have h := (Subgroup.mem_normalizer_iff.mp hminv v).mp hv
      simpa using h
    have hpv := hp (m⁻¹ * v * m) hv'
    have hmain : (m * p * m⁻¹) * v = v * (m * p * m⁻¹) := by
      calc (m * p * m⁻¹) * v = m * p * (m⁻¹ * v * m) * m⁻¹ := by group
        _ = m * (p * (m⁻¹ * v * m)) * m⁻¹ := by group
        _ = m * ((m⁻¹ * v * m) * p) * m⁻¹ := by rw [hpv]
        _ = v * (m * p * m⁻¹) := by group
    exact hmain.symm
  have huCent : u ∈ Subgroup.centralizer (V2 c.e : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun v hv => (huV2 v hv).symm)
  have hcomm : ⁅C7 c.s, normIn L c.s.fr.B⁆ ≤ Subgroup.centralizer (V2 c.e : Set G) := by
    rw [Subgroup.commutator_le]
    intro y hy n hn
    rcases y7b_cover2 c hb huC7 hut y hy with hyW | ⟨m, hm, a, haW, rfl⟩
    · exact hBMcent (y7b_comm_W_NL c hb y hyW n hn)
    · have hp : m * u * m⁻¹ ∈ Subgroup.centralizer (V2 c.e : Set G) :=
        hconj m hm u huCent
      have hq : ⁅a, n⁆ ∈ Subgroup.centralizer (V2 c.e : Set G) :=
        hBMcent (y7b_comm_W_NL c hb a haW n hn)
      have hr : n * (m * u * m⁻¹) * n⁻¹ ∈ Subgroup.centralizer (V2 c.e : Set G) :=
        hconj n hn (m * u * m⁻¹) hp
      have hform : ⁅(m * u * m⁻¹) * a, n⁆ =
          (m * u * m⁻¹) * ⁅a, n⁆ * (n * (m * u * m⁻¹) * n⁻¹)⁻¹ := by
        rw [commutatorElement_mul_left_eq_conj_mul]
        simp only [commutatorElement_def]
        group
      rw [hform]
      exact (Subgroup.centralizer (V2 c.e : Set G)).mul_mem
        ((Subgroup.centralizer (V2 c.e : Set G)).mul_mem hp hq)
        ((Subgroup.centralizer (V2 c.e : Set G)).inv_mem hr)
  have hM7cent : M7 c.s ≤ Subgroup.centralizer (V2 c.e : Set G) := by
    rw [M7]
    exact sup_le hcomm hBMcent
  intro x hx v hv
  exact (Subgroup.mem_centralizer_iff.mp (hM7cent hx) v hv).symm

theorem y7b_V2_le_cen_M7 (c : Ctx7 G L) (hb : B5Std c) : V2 c.e ≤ cen (M7 c.s) := by
  intro v hv
  have hvM3 : v ∈ M3 c.s := (Subgroup.mem_inf.mp hv).1
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact y7b_BM_le_M7 c hb (Subgroup.mem_sup_right hvM3)
  · exact Subgroup.mem_centralizer_iff.mpr
      (fun x hx => y7b_M7_le_cent_V2 c hb x hx v hv)

end CFSG.OddStandard.HigherRank.YamadaG23
