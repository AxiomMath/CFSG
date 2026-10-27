module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K3

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
    (hy : y ∈ f4Y s) : f3phi s y⁻¹ = (f3phi s y)⁻¹ := by
  have h1 : f3phi s (y * y⁻¹) = f3phi s y * f3phi s y⁻¹ :=
    y54_phi_mul hH y hy y⁻¹ ((f4Y s).inv_mem hy)
  rw [mul_inv_cancel] at h1
  have h2 : f3phi s (1 : G) = 1 := by simp [f3phi]
  rw [h2] at h1
  calc f3phi s y⁻¹ = 1 * f3phi s y⁻¹ := by rw [one_mul]
    _ = ((f3phi s y)⁻¹ * f3phi s y) * f3phi s y⁻¹ := by rw [inv_mul_cancel]
    _ = (f3phi s y)⁻¹ * (f3phi s y * f3phi s y⁻¹) := by group
    _ = (f3phi s y)⁻¹ * 1 := by rw [← h1]
    _ = (f3phi s y)⁻¹ := by rw [mul_one]

private theorem c3_le_Y (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : C3 c.s ≤ f4Y c.s := by
  rw [y54_C3_eq_M3 c hH]
  refine sup_le (y54_M3_cand c hH).2.1 ?_
  exact Subgroup.zpowers_le.mpr
    (y54_X0_le_Y hH (y54_P_le_X0 hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t))))

theorem y54_d_mem_C2 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.d ∈ c.s.C₂ :=
  (y52_fact (c := c) hH).2.2.1 c.d_mem

theorem y54_d_mem_C3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.d ∈ C3 c.s := by
  have hdcent : c.d ∈ Subgroup.centralizer (c.s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp (y54_d_mem_Y (c := c) hH)).2
  rw [y54_C3_eq_M3 c hH]
  obtain h | ⟨m, hmM2, hdm⟩ := y54_C2_cases c hH c.d (y54_d_mem_C2 c hH)
  · exact Subgroup.mem_sup_left (y54_K_le_M3 c hH (Subgroup.mem_inf.mpr ⟨h, hdcent⟩))
  · have hmcent : m ∈ Subgroup.centralizer (c.s.fr.F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hdf : c.d * f = f * c.d := by
        have h := y54_d_cent_F c f hf
        calc c.d * f = (c.d * f * c.d⁻¹) * c.d := by group
          _ = f * c.d := by rw [h]
      have htf : f * c.s.t⁻¹ = c.s.t⁻¹ * f := by
        calc f * c.s.t⁻¹ = (c.s.t * f⁻¹)⁻¹ := by group
          _ = (f⁻¹ * c.s.t)⁻¹ := by rw [← y54_t_comm_F c.s f⁻¹ ((c.s.fr.F).inv_mem hf)]
          _ = c.s.t⁻¹ * f := by group
      have hm_eq : m = c.d * c.s.t⁻¹ := by rw [hdm]; group
      rw [hm_eq]
      calc f * (c.d * c.s.t⁻¹) = (f * c.d) * c.s.t⁻¹ := by group
        _ = (c.d * f) * c.s.t⁻¹ := by rw [hdf]
        _ = c.d * (f * c.s.t⁻¹) := by group
        _ = c.d * (c.s.t⁻¹ * f) := by rw [htf]
        _ = (c.d * c.s.t⁻¹) * f := by group
    have hmK : m ∈ centIn (M2 c.s) c.s.fr.F := Subgroup.mem_inf.mpr ⟨hmM2, hmcent⟩
    rw [hdm]
    exact Subgroup.mul_mem_sup (y54_K_le_M3 c hH hmK) (Subgroup.mem_zpowers c.s.t)

theorem y54_C0_le_C3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : C0 c.e ≤ C3 c.s := by
  have htC3 : c.s.t ∈ C3 c.s := by
    rw [y54_C3_eq_M3 c hH]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
  rw [c.intro5.gen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact htC3
  · exact y54_d_mem_C3 c hH

theorem y54_A_le_N {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.A ≤ normIn L s.fr.F := by
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  refine le_inf (s3_A_le_L s) ?_
  intro a ha
  change a ∈ Subgroup.normalizer (s.fr.F : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · intro hf
    have hcomm : ⁅a, f⁆ ∈ s.fr.Z := hA.comm_A a ha f (s3_F_le_A s hf)
    have heq : a * f * a⁻¹ = ⁅a, f⁆ * f := by rw [commutatorElement_def]; group
    rw [heq]
    exact s.fr.F.mul_mem (s3_Z_le_F s hcomm) hf
  · intro hf
    have hcomm : ⁅a⁻¹, a * f * a⁻¹⁆ ∈ s.fr.Z :=
      hA.comm_A a⁻¹ (s.fr.A.inv_mem ha) (a * f * a⁻¹) (s3_F_le_A s hf)
    have heq : a⁻¹ * (a * f * a⁻¹) * a = ⁅a⁻¹, a * f * a⁻¹⁆ * (a * f * a⁻¹) := by
      rw [commutatorElement_def]; group
    have hfeq : f = a⁻¹ * (a * f * a⁻¹) * a := by group
    rw [hfeq, heq]
    exact s.fr.F.mul_mem (s3_Z_le_F s hcomm) hf

theorem y54_C3_phi_Z (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ w ∈ C3 c.s, f3phi c.s w ∈ c.s.fr.Z → w ∈ c.s.fr.F ⊔ C0 c.e := by
  have htY : c.s.t ∈ f4Y c.s :=
    y54_X0_le_Y hH (y54_P_le_X0 hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)))
  have htC0 : c.s.t ∈ C0 c.e := by
    rw [c.intro5.gen]; exact Subgroup.subset_closure (by simp)
  have htnorm : c.s.t ∈ Subgroup.normalizer (M3 c.s : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    exact ⟨fun hm => y54_M_normal (c := c) hH (y54_M3_cand c hH) c.s.t htY m hm,
      fun hm => by
        have h2 : m = c.s.t⁻¹ * (c.s.t * m * c.s.t⁻¹) * c.s.t := by group
        rw [h2]
        simpa using y54_M_normal (c := c) hH (y54_M3_cand c hH) c.s.t⁻¹
          ((f4Y c.s).inv_mem htY) (c.s.t * m * c.s.t⁻¹) hm⟩
  have hnorm_t : ∀ x ∈ zpowers c.s.t, ∀ m ∈ M3 c.s, x * m * x⁻¹ ∈ M3 c.s := by
    intro x hx m hm
    exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr htnorm) hx) m).mp hm
  have hcase1 : ∀ v ∈ C3 c.s, f3phi c.s v = 1 → v ∈ c.s.fr.F ⊔ C0 c.e := by
    intro v hv hv1
    have hvY : v ∈ f4Y c.s := c3_le_Y c hH hv
    have hvX0 : v ∈ f4X0 c.s := (y54_phi_eq_one hH v hvY).mp hv1
    obtain ⟨u, hu, m, hmM3, hvm⟩ := mem_sup_of_normalizes (T := zpowers c.s.t)
      (C := M3 c.s) hnorm_t v (by rw [y54_C3_eq_M3 c hH, sup_comm] at hv; exact hv)
    have huX0 : u ∈ f4X0 c.s := y54_P_le_X0 hH (Subgroup.mem_sup_right hu)
    have hmX0 : m ∈ f4X0 c.s := by
      have h : u⁻¹ * v ∈ f4X0 c.s := (f4X0 c.s).mul_mem ((f4X0 c.s).inv_mem huX0) hvX0
      rw [hvm] at h
      simpa using h
    have hmF : m ∈ c.s.fr.F := by
      have hMF : M3 c.s ⊓ f4X0 c.s = c.s.fr.F := (y54_M3_cand c hH).2.2.2.1
      rw [← hMF]
      exact Subgroup.mem_inf.mpr ⟨hmM3, hmX0⟩
    rw [hvm]
    exact (c.s.fr.F ⊔ C0 c.e).mul_mem
      (Subgroup.mem_sup_right (Subgroup.zpowers_le.mpr htC0 hu)) (Subgroup.mem_sup_left hmF)
  intro w hw hwZ
  have hwY : w ∈ f4Y c.s := c3_le_Y c hH hw
  rw [SFrame.Z] at hwZ
  by_cases hw1 : f3phi c.s w = 1
  · exact hcase1 w hw hw1
  · have hz2 : c.s.fr.z ^ 2 = 1 := by
      have h := pow_orderOf_eq_one c.s.fr.z
      rwa [(lfactsA_of_setting hH.hS hH.hZ c.s).z_order] at h
    have hwz : f3phi c.s w = c.s.fr.z := by
      rcases mem_zpowers_eq_one_or hz2 hwZ with h | h
      · exact absurd h hw1
      · exact h
    have hdwC3 : c.d⁻¹ * w ∈ C3 c.s :=
      (C3 c.s).mul_mem ((C3 c.s).inv_mem (y54_d_mem_C3 c hH)) hw
    have hdwY : c.d⁻¹ * w ∈ f4Y c.s :=
      (f4Y c.s).mul_mem ((f4Y c.s).inv_mem (y54_d_mem_Y (c := c) hH)) hwY
    have hphi_dw : f3phi c.s (c.d⁻¹ * w) = 1 := by
      rw [y54_phi_mul hH c.d⁻¹ ((f4Y c.s).inv_mem (y54_d_mem_Y (c := c) hH)) w hwY,
        phi_inv hH (y54_d_mem_Y (c := c) hH), y54_phi_d (c := c) hH, hwz, inv_mul_cancel]
    have hmem := hcase1 (c.d⁻¹ * w) hdwC3 hphi_dw
    have hw_eq : w = c.d * (c.d⁻¹ * w) := by group
    rw [hw_eq]
    exact (c.s.fr.F ⊔ C0 c.e).mul_mem (Subgroup.mem_sup_right c.d_mem) hmem

theorem y54_comm_A_C3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ a ∈ c.s.fr.A, ∀ w ∈ C3 c.s, ⁅a, w⁆ ∈ c.s.fr.F ⊔ C0 c.e := by
  intro a ha w hw
  have hAN : a ∈ normIn L c.s.fr.F := y54_A_le_N hH ha
  have hN : a ∈ f4N c.s := y54_NL_le_N hH hAN
  have hta : a * c.s.t = c.s.t * a := s3_comm_t_of_mem_L c.s (s3_A_le_L c.s ha)
  have hwY : w ∈ f4Y c.s := c3_le_Y c hH hw
  have hM3norm : a ∈ Subgroup.normalizer (M3 c.s : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    exact ⟨fun hm => (y54_M3_cand c hH).2.2.1 a hAN m hm,
      fun hm => by
        have h2 : m = a⁻¹ * (a * m * a⁻¹) * a := by group
        rw [h2]
        simpa using (y54_M3_cand c hH).2.2.1 a⁻¹ ((normIn L c.s.fr.F).inv_mem hAN)
          (a * m * a⁻¹) hm⟩
  have hZptnorm : a ∈ Subgroup.normalizer (zpowers c.s.t : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hconj : (↑(MulAut.conj a) : G →* G) c.s.t = c.s.t := by
      change a * c.s.t * a⁻¹ = c.s.t
      rw [hta, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
  have hC3norm : a ∈ Subgroup.normalizer (C3 c.s : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, y54_C3_eq_M3 c hH, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hM3norm,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hZptnorm]
  have hC3n : a * w * a⁻¹ ∈ C3 c.s := (Subgroup.mem_normalizer_iff.mp hC3norm w).mp hw
  have hcommC3 : ⁅a, w⁆ ∈ C3 c.s := by
    rw [commutatorElement_def]
    exact (C3 c.s).mul_mem hC3n ((C3 c.s).inv_mem hw)
  have hphi : f3phi c.s ⁅a, w⁆ = ⁅a, f3phi c.s w⁆ := by
    rw [commutatorElement_def,
      y54_phi_mul hH (a * w * a⁻¹) (c3_le_Y c hH hC3n) w⁻¹ ((f4Y c.s).inv_mem hwY),
      y54_phi_conj hH a hN w, phi_inv hH hwY, commutatorElement_def]
  have hZ : f3phi c.s ⁅a, w⁆ ∈ c.s.fr.Z := by
    rw [hphi]
    exact (lfactsA_of_setting hH.hS hH.hZ c.s).comm_A a ha (f3phi c.s w)
      (s3_F_le_A c.s (y54_phi_mem hH w hwY))
  exact y54_C3_phi_Z c hH ⁅a, w⁆ hcommC3 hZ

theorem y54_comm_C1_C3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ⁅C1 c.e, C3 c.s⁆ ≤ c.s.fr.F ⊔ C0 c.e := by
  rw [Subgroup.commutator_le]
  intro u hu w hw
  change u ∈ c.s.fr.A ⊔ C0 c.e at hu
  have hwY : w ∈ f4Y c.s := c3_le_Y c hH hw
  have hAnormC0 : ∀ x ∈ c.s.fr.A, ∀ d0 ∈ C0 c.e, x * d0 * x⁻¹ ∈ C0 c.e := by
    intro x hx d0 hd0
    have hcomm : x * d0 = d0 * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd0).2 x hx
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hd0
  obtain ⟨a, ha, d0, hd0, rfl⟩ :=
    mem_sup_of_normalizes (T := c.s.fr.A) (C := C0 c.e) hAnormC0 u hu
  have hd0C3 : d0 ∈ C3 c.s := y54_C0_le_C3 c hH hd0
  have hcomm_d0 : ⁅d0, w⁆ ∈ c.s.fr.F := y54_Y_comm c hH d0 (c3_le_Y c hH hd0C3) w hwY
  have hcomm_a : ⁅a, w⁆ ∈ c.s.fr.F ⊔ C0 c.e := y54_comm_A_C3 c hH a ha w hw
  have haF : a * ⁅d0, w⁆ * a⁻¹ ∈ c.s.fr.F :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (y54_A_le_N hH ha)).2 ⁅d0, w⁆).mp
      hcomm_d0
  have hid : ⁅a * d0, w⁆ = a * ⁅d0, w⁆ * a⁻¹ * ⁅a, w⁆ := by
    simp only [commutatorElement_def]; group
  rw [hid]
  exact (c.s.fr.F ⊔ C0 c.e).mul_mem (Subgroup.mem_sup_left haF) hcomm_a

end CFSG.OddStandard.HigherRank.YamadaG23
