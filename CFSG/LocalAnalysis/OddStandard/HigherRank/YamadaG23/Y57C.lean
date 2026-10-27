module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54One
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Two

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y57_t_sq (c : Ctx5 G L) : c.s.t * c.s.t = 1 := by
  rw [← pow_two, ← c.s.t_order]
  exact pow_orderOf_eq_one c.s.t

private theorem y57_t_sq_pow (c : Ctx5 G L) : c.s.t ^ 2 = 1 := by
  rw [pow_two]
  exact y57_t_sq c

private theorem y57_zpow_eq_one_or {x y : G} (hy2 : y ^ 2 = 1) (hx : x ∈ zpowers y) :
    x = 1 ∨ x = y := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : y ^ (2 : ℤ) = 1 := by simpa using hy2
  rw [zpow_eq_zpow_emod m h2]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

private theorem y57_tdt (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.s.t * c.d * c.s.t⁻¹ = c.s.fr.z * c.d := by
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  have hz2 : orderOf c.s.fr.z = 2 := s3_z_order c.s hA
  obtain ⟨hord, hu2⟩ := Ctx5pre.u_facts c.toCtx5pre hz2
  have h4 : (c.d * c.s.t) ^ 4 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  exact (d8_rel c.s.t_order c.d_order h4 hu2).2

theorem y57_t_notin_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.s.t ∉ M3 c.s := by
  intro htM
  have htH : c.s.t ∈ c.s.H := by
    rw [Setting3.H]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hmem : c.s.t ∈ c.s.H ⊓ M3 c.s := Subgroup.mem_inf.mpr ⟨htH, htM⟩
  rw [y54_H_inf_M3 c hH] at hmem
  exact s3_t_not_mem_L c.s hH.h31 (y54_F_le_L c.s hmem)

theorem y57_d_or_td (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.d ∈ M3 c.s ∨ c.s.t * c.d ∈ M3 c.s := by
  have hdC3 : c.d ∈ M3 c.s ⊔ zpowers c.s.t := by
    rw [← y54_C3_eq_M3 c hH]
    exact y54_d_mem_C3 c hH
  have htY : c.s.t ∈ f4Y c.s :=
    (y54_X0_le_Y hH) ((y54_P_le_X0 hH) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)))
  have hnorm : ∀ x ∈ zpowers c.s.t, ∀ m ∈ M3 c.s, x * m * x⁻¹ ∈ M3 c.s := by
    intro x hx m hm
    exact y54_M_normal (c := c) hH (y54_M3_cand c hH) x
      (Subgroup.zpowers_le.mpr htY hx) m hm
  obtain ⟨u, hu, m, hm, hdu⟩ :=
    mem_sup_of_normalizes hnorm c.d (by rw [sup_comm]; exact hdC3)
  rcases y57_zpow_eq_one_or (y57_t_sq_pow c) hu with rfl | rfl
  · left
    rw [hdu]
    simpa using hm
  · right
    rw [hdu, show c.s.t * (c.s.t * m) = m by rw [← mul_assoc, y57_t_sq c, one_mul]]
    exact hm

theorem y57_d_dichotomy_M2 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    (c.d ∈ M2 c.s ∨ c.d * c.s.t ∈ M2 c.s) ∧ (c.d ∈ M2 c.s → c.d ∈ M3 c.s) ∧
      (c.d * c.s.t ∈ M2 c.s → c.d * c.s.t ∈ M3 c.s) := by
  have hdCentF : c.d ∈ Subgroup.centralizer (c.s.fr.F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    calc f * c.d = (c.d * f * c.d⁻¹) * c.d := by rw [y54_d_cent_F c f hf]
      _ = c.d * f := by group
  have htCentF : c.s.t ∈ Subgroup.centralizer (c.s.fr.F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact y54_t_comm_F c.s f hf
  refine ⟨?_, ?_, ?_⟩
  · rcases y54_C2_cases c hH c.d (y54_d_mem_C2 c hH) with h | ⟨m, hm, hdm⟩
    · exact Or.inl h
    · refine Or.inr ?_
      rw [hdm]
      rwa [mul_assoc, y57_t_sq c, mul_one]
  · intro hdM2
    exact y54_K_le_M3 c hH (Subgroup.mem_inf.mpr ⟨hdM2, hdCentF⟩)
  · intro hdtM2
    exact y54_K_le_M3 c hH
      (Subgroup.mem_inf.mpr ⟨hdtM2,
        (Subgroup.centralizer (c.s.fr.F : Set G)).mul_mem hdCentF htCentF⟩)

private theorem y57_inf_C0_le {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {Q : Subgroup G}
    (hQleC0 : Q ≤ C0 c.e) (hQleM3 : Q ≤ M3 c.s) (hgen : c.d ∈ Q ⊔ zpowers c.s.t)
    (hnorm : ∀ u ∈ zpowers c.s.t, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q) :
    C0 c.e ⊓ M3 c.s ≤ Q := by
  have ht2 : c.s.t ^ 2 = 1 := y57_t_sq_pow c
  have htC0 : c.s.t ∈ C0 c.e := by
    rw [c.intro5.gen]
    exact Subgroup.subset_closure (by simp)
  have hC0le : C0 c.e ≤ Q ⊔ zpowers c.s.t := by
    rw [c.intro5.gen, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
    · exact hgen
  have hC0eq : C0 c.e = Q ⊔ zpowers c.s.t :=
    le_antisymm hC0le (sup_le hQleC0 (Subgroup.zpowers_le.mpr htC0))
  intro x hx
  obtain ⟨hxC0, hxM3⟩ := Subgroup.mem_inf.mp hx
  rw [hC0eq] at hxC0
  obtain ⟨u, hu, q, hq, rfl⟩ :=
    mem_sup_of_normalizes hnorm x (by rw [sup_comm]; exact hxC0)
  rcases y57_zpow_eq_one_or ht2 hu with rfl | rfl
  · simpa using hq
  · exfalso
    refine y57_t_notin_M3 c hH ?_
    have heq : c.s.t = (c.s.t * q) * q⁻¹ := by group
    rw [heq]
    exact (M3 c.s).mul_mem hxM3 ((M3 c.s).inv_mem (hQleM3 hq))

theorem y57_V1_A (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hd : c.d ∈ M3 c.s) :
    V1 c.e = closure {c.s.fr.z, c.d} ∧ V1 c.e ≤ M2 c.s := by
  set Q : Subgroup G := closure {c.s.fr.z, c.d} with hQ
  have hzC0 : c.s.fr.z ∈ C0 c.e := y5_z_mem_C0 hH
  have hzM3 : c.s.fr.z ∈ M3 c.s := (y54_M3_cand c hH).1 (y54_z_mem_F c.s)
  have hQleC0 : Q ≤ C0 c.e := by
    rw [hQ, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hzC0
    · exact c.d_mem
  have hQleM3 : Q ≤ M3 c.s := by
    rw [hQ, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hzM3
    · exact hd
  have hgen : c.d ∈ Q ⊔ zpowers c.s.t :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have htQ : ∀ q ∈ Q, c.s.t * q * c.s.t⁻¹ ∈ Q := by
    intro q hq
    rw [hQ] at hq ⊢
    refine Subgroup.closure_induction
      (p := fun q _ => c.s.t * q * c.s.t⁻¹ ∈ closure {c.s.fr.z, c.d}) ?_ ?_ ?_ ?_ hq
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · have hz : c.s.t * c.s.fr.z * c.s.t⁻¹ = c.s.fr.z := by
          rw [← s3_comm_t_of_mem_L c.s (s3_z_mem_L c.s)]
          group
        rw [hz]
        exact Subgroup.subset_closure (by simp)
      · rw [y57_tdt c hH]
        exact (Subgroup.closure {c.s.fr.z, c.d}).mul_mem
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · intro y z _ _ hy hz
      rw [show c.s.t * (y * z) * c.s.t⁻¹
          = (c.s.t * y * c.s.t⁻¹) * (c.s.t * z * c.s.t⁻¹) by group]
      exact (Subgroup.closure {c.s.fr.z, c.d}).mul_mem hy hz
    · intro y _ hy
      rw [show c.s.t * y⁻¹ * c.s.t⁻¹ = (c.s.t * y * c.s.t⁻¹)⁻¹ by group]
      exact (Subgroup.closure {c.s.fr.z, c.d}).inv_mem hy
  have hnormQ : ∀ u ∈ zpowers c.s.t, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q := by
    intro u hu q hq
    rcases y57_zpow_eq_one_or (y57_t_sq_pow c) hu with rfl | rfl
    · simpa using hq
    · exact htQ q hq
  have hV1 : V1 c.e = Q :=
    le_antisymm (y57_inf_C0_le (c := c) hH hQleC0 hQleM3 hgen hnormQ)
      (le_inf hQleC0 hQleM3)
  have hM2Q : Q ≤ M2 c.s := by
    rw [hQ, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact y54_B_le_M2 c.s (y54_F_le_B hH (y54_z_mem_F c.s))
    · by_contra hdM2
      have hdtM2 : c.d * c.s.t ∈ M2 c.s :=
        (y57_d_dichotomy_M2 c hH).1.resolve_left hdM2
      have hdtM3 : c.d * c.s.t ∈ M3 c.s := (y57_d_dichotomy_M2 c hH).2.2 hdtM2
      exact y57_t_notin_M3 c hH (by
        have : c.s.t = c.d⁻¹ * (c.d * c.s.t) := by group
        rw [this]
        exact (M3 c.s).mul_mem ((M3 c.s).inv_mem hd) hdtM3)
  exact ⟨hV1.trans hQ, by rw [hV1]; exact hM2Q⟩

theorem y57_V1_B (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (htd : c.s.t * c.d ∈ M3 c.s) :
    V1 c.e = zpowers (c.d * c.s.t) ∧ V1 c.e ≤ M2 c.s := by
  have hd2 : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c
  have hdt_eq : c.d * c.s.t = (c.s.t * c.d)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hd2, inv_eq_of_mul_eq_one_right (y57_t_sq c)]
  have hdtM3 : c.d * c.s.t ∈ M3 c.s := by
    rw [hdt_eq]
    exact (M3 c.s).inv_mem htd
  set Q : Subgroup G := zpowers (c.d * c.s.t) with hQ
  have htC0 : c.s.t ∈ C0 c.e := by
    rw [c.intro5.gen]
    exact Subgroup.subset_closure (by simp)
  have hdtC0 : c.d * c.s.t ∈ C0 c.e := (C0 c.e).mul_mem c.d_mem htC0
  have hQleC0 : Q ≤ C0 c.e := by rw [hQ]; exact Subgroup.zpowers_le.mpr hdtC0
  have hQleM3 : Q ≤ M3 c.s := by rw [hQ]; exact Subgroup.zpowers_le.mpr hdtM3
  have hgen : c.d ∈ Q ⊔ zpowers c.s.t := by
    rw [hQ]
    have h : (c.d * c.s.t) * c.s.t ∈ zpowers (c.d * c.s.t) ⊔ zpowers c.s.t :=
      Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
    rwa [mul_assoc, y57_t_sq c, mul_one] at h
  have htu : c.s.t * (c.d * c.s.t) * c.s.t⁻¹ = (c.d * c.s.t)⁻¹ := by
    have h1 : c.s.t * (c.d * c.s.t) * c.s.t⁻¹ = c.s.t * c.d := by
      rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : (c.d * c.s.t)⁻¹ = c.s.t * c.d := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (y57_t_sq c),
        inv_eq_of_mul_eq_one_right hd2]
    rw [h1, h2]
  have htQ : ∀ q ∈ Q, c.s.t * q * c.s.t⁻¹ ∈ Q := by
    intro q hq
    rw [hQ] at hq ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hconj : c.s.t * (c.d * c.s.t) ^ k * c.s.t⁻¹ = ((c.d * c.s.t) ^ k)⁻¹ := by
      rw [← conj_zpow, htu, inv_zpow]
    rw [hconj]
    exact (Subgroup.zpowers (c.d * c.s.t)).inv_mem
      (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  have hnormQ : ∀ u ∈ zpowers c.s.t, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q := by
    intro u hu q hq
    rcases y57_zpow_eq_one_or (y57_t_sq_pow c) hu with rfl | rfl
    · simpa using hq
    · exact htQ q hq
  have hV1 : V1 c.e = Q :=
    le_antisymm (y57_inf_C0_le (c := c) hH hQleC0 hQleM3 hgen hnormQ)
      (le_inf hQleC0 hQleM3)
  have hM2Q : Q ≤ M2 c.s := by
    rw [hQ]
    refine Subgroup.zpowers_le.mpr ?_
    by_contra hdtM2
    have hdM2 : c.d ∈ M2 c.s := (y57_d_dichotomy_M2 c hH).1.resolve_right hdtM2
    have hdM3 : c.d ∈ M3 c.s := (y57_d_dichotomy_M2 c hH).2.1 hdM2
    exact y57_t_notin_M3 c hH (by
      have : c.s.t = (c.s.t * c.d) * c.d⁻¹ := by group
      rw [this]
      exact (M3 c.s).mul_mem htd ((M3 c.s).inv_mem hdM3))
  exact ⟨hV1.trans hQ, by rw [hV1]; exact hM2Q⟩

end CFSG.OddStandard.HigherRank.YamadaG23
