module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Two

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y55_g_comm_NL (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ n ∈ normIn L c.s.fr.F, ⁅c.g, n⁆ ∈ c.s.fr.F := by
  intro n hn
  have hspec := c.g_spec hRT
  have hmem : ⁅c.g, n⁆ ∈ c.s.fr.F ⊔ zL L :=
    (hH.hLF.fact110 c.g hspec.2.2.2.1 hspec.2.2.1).2.2 n hn
  rwa [f3_zL_eq_bot hH, sup_bot_eq] at hmem

theorem y55_g_cent_C0 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ x ∈ C0 c.e, c.g * x * c.g⁻¹ = x := by
  obtain ⟨hgT, -, -, -, hgd⟩ := c.g_spec hRT
  have hgH : c.g ∈ c.s.H := by
    rw [Setting3.H]
    exact c.s.sylow_T.1 hgT
  have hgt : c.g * c.s.t * c.g⁻¹ = c.s.t := by
    have hcomm : c.s.t * c.g = c.g * c.s.t :=
      (Subgroup.mem_centralizer_iff.mp hgH) c.s.t (by simp)
    rw [← hcomm]
    group
  intro x hx
  rw [c.intro5.gen] at hx
  refine Subgroup.closure_induction (p := fun x _ => c.g * x * c.g⁻¹ = x) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hgt
    · exact hgd
  · group
  · intro y z _ _ hy hz
    rw [show c.g * (y * z) * c.g⁻¹
        = (c.g * y * c.g⁻¹) * (c.g * z * c.g⁻¹) from by group, hy, hz]
  · intro y _ hy
    rw [show c.g * y⁻¹ * c.g⁻¹ = (c.g * y * c.g⁻¹)⁻¹ from by group, hy]

theorem y55_exists_x (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∃ x ∈ C0 c.e, x ∈ M3 c.s ∧ x ∉ c.s.H := by
  have hdC3 : c.d ∈ M3 c.s ⊔ zpowers c.s.t := by
    rw [← y54_C3_eq_M3 c hH]
    exact y54_d_mem_C3 c hH
  have htY : c.s.t ∈ f4Y c.s :=
    (y54_X0_le_Y hH) ((y54_P_le_X0 hH) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)))
  have hTC : ∀ x ∈ zpowers c.s.t, ∀ y ∈ M3 c.s, x * y * x⁻¹ ∈ M3 c.s := by
    intro x hx y hy
    exact y54_M_normal (c := c) hH (y54_M3_cand c hH) x
      (Subgroup.zpowers_le.mpr htY hx) y hy
  have hdC3' : c.d ∈ zpowers c.s.t ⊔ M3 c.s := by rwa [sup_comm] at hdC3
  obtain ⟨u, hu, m, hmM, hdu⟩ := mem_sup_of_normalizes hTC c.d hdC3'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
  have ht2 : c.s.t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← c.s.t_order]
    exact pow_orderOf_eq_one c.s.t
  have hzk : c.s.t ^ k = 1 ∨ c.s.t ^ k = c.s.t := by
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
    · left
      rw [hj, zpow_mul, ht2, one_zpow]
    · right
      rw [hj, zpow_add, zpow_one, zpow_mul, ht2, one_zpow, one_mul]
  have hd_notH : c.d ∉ c.s.H := by
    intro hdH
    apply y5_d_not_mem_T hH
    have hmem : c.d ∈ c.e.T₁ ⊓ c.s.H := Subgroup.mem_inf.mpr ⟨y5_d_mem_T1 c, hdH⟩
    rwa [s3_inf_H_T1 c.s c.e] at hmem
  have htH : c.s.t ∈ c.s.H := by
    rw [Setting3.H]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htd_notH : c.s.t * c.d ∉ c.s.H := by
    intro h
    apply hd_notH
    have hmem : c.s.t⁻¹ * (c.s.t * c.d) ∈ c.s.H := c.s.H.mul_mem (c.s.H.inv_mem htH) h
    simpa using hmem
  have htC0 : c.s.t ∈ C0 c.e := by
    simp only [C0, centIn, Subgroup.mem_inf]
    exact ⟨c.e.T_le (s3_t_mem_T c.s),
      Subgroup.mem_centralizer_iff.mpr fun a ha => s3_comm_t_of_mem_A c.s ha⟩
  rcases hzk with h1 | ht
  · refine ⟨c.d, c.d_mem, ?_, hd_notH⟩
    have hu1 : u = 1 := by rw [← hk]; exact h1
    rw [hdu, hu1, one_mul]
    exact hmM
  · refine ⟨c.s.t * c.d, Subgroup.mul_mem (C0 c.e) htC0 c.d_mem, ?_, htd_notH⟩
    have hut : u = c.s.t := by rw [← hk]; exact ht
    have ht_mul : c.s.t * c.s.t = 1 := by
      rw [← pow_two, ← c.s.t_order]
      exact pow_orderOf_eq_one c.s.t
    rw [hdu, hut]
    rw [show c.s.t * (c.s.t * m) = (c.s.t * c.s.t) * m from by group, ht_mul, one_mul]
    exact hmM

private abbrev Y55W (c : Ctx5 G L) : Set G :=
  {m : G | m ∈ M3 c.s ∧ c.g * m * c.g⁻¹ = m}

private theorem y55_mem_W {c : Ctx5 G L} {m : G} :
    m ∈ Y55W c ↔ m ∈ M3 c.s ∧ c.g * m * c.g⁻¹ = m := Iff.rfl

private theorem y55_W_conj (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ n ∈ normIn L c.s.fr.F, ∀ w ∈ Y55W c, n * w * n⁻¹ ∈ Y55W c := by
  intro n hn w hw
  rw [y55_mem_W] at hw ⊢
  obtain ⟨hwm, hwg⟩ := hw
  have hnwM : n * w * n⁻¹ ∈ M3 c.s := (y54_M3_cand c hH).2.2.1 n hn w hwm
  have hnwY : n * w * n⁻¹ ∈ f4Y c.s := (y54_M3_cand c hH).2.1 hnwM
  have hcent : n * w * n⁻¹ ∈ Subgroup.centralizer (↑c.s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp hnwY).2
  have hfF : ⁅c.g, n⁆ ∈ c.s.fr.F := y55_g_comm_NL c hH hRT n hn
  have hcomm : ⁅c.g, n⁆ * (n * w * n⁻¹) = (n * w * n⁻¹) * ⁅c.g, n⁆ :=
    (Subgroup.mem_centralizer_iff.mp hcent) ⁅c.g, n⁆ hfF
  have hgn : c.g * n * c.g⁻¹ = ⁅c.g, n⁆ * n := by
    rw [commutatorElement_def]
    group
  refine ⟨hnwM, ?_⟩
  calc c.g * (n * w * n⁻¹) * c.g⁻¹
      = (c.g * n * c.g⁻¹) * (c.g * w * c.g⁻¹) * (c.g * n * c.g⁻¹)⁻¹ := by group
    _ = (⁅c.g, n⁆ * n) * w * (⁅c.g, n⁆ * n)⁻¹ := by rw [hgn, hwg]
    _ = ⁅c.g, n⁆ * (n * w * n⁻¹) * ⁅c.g, n⁆⁻¹ := by group
    _ = n * w * n⁻¹ := by rw [hcomm]; group

private theorem y55_W_phi_surj (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ f ∈ c.s.fr.F, ∃ w ∈ Y55W c, f3phi c.s w = f := by
  intro f hf
  by_cases hf1 : f = 1
  · refine ⟨1, ?_, ?_⟩
    · rw [y55_mem_W]
      exact ⟨(M3 c.s).one_mem, by group⟩
    · simp [f3phi, hf1]
  · obtain ⟨x, hxC0, hxM, hxH⟩ := y55_exists_x c hH
    have hxW : x ∈ Y55W c := by
      rw [y55_mem_W]
      exact ⟨hxM, y55_g_cent_C0 c hH hRT x hxC0⟩
    have hxY : x ∈ f4Y c.s := (y54_M3_cand c hH).2.1 hxM
    have hf0F : f3phi c.s x ∈ c.s.fr.F := y54_phi_mem hH x hxY
    have hf0ne : f3phi c.s x ≠ 1 := by
      intro h
      apply hxH
      exact (Subgroup.mem_inf.mp ((y54_phi_eq_one hH x hxY).mp h)).1
    obtain ⟨n, hnN, hnconj⟩ := y54_trans1 hH (f3phi c.s x) hf0F f hf hf0ne hf1
    refine ⟨n * x * n⁻¹, y55_W_conj c hH hRT n hnN x hxW, ?_⟩
    rw [y54_phi_conj hH n (y54_NL_le_N hH hnN) x, hnconj]

theorem y55_fact (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.Fact55 := by
  intro hRT m hm
  have hspec := c.g_spec hRT
  have hg2 : c.g ^ 2 = 1 := hspec.2.2.2.1
  have hact : ActsAs L c.g c.s.fr'.σ := hspec.2.2.1
  have hmY : m ∈ f4Y c.s := (y54_M3_cand c hH).2.1 hm
  have hmphiF : f3phi c.s m ∈ c.s.fr.F := y54_phi_mem hH m hmY
  obtain ⟨w, hwW, hwphi⟩ := y55_W_phi_surj c hH hRT (f3phi c.s m) hmphiF
  rw [y55_mem_W] at hwW
  obtain ⟨hwm, hwg⟩ := hwW
  have hwY : w ∈ f4Y c.s := (y54_M3_cand c hH).2.1 hwm
  have hw'Y : w⁻¹ ∈ f4Y c.s := (f4Y c.s).inv_mem hwY
  have hphi_inv : f3phi c.s w⁻¹ = (f3phi c.s w)⁻¹ := by
    have hmul := y54_phi_mul hH w hwY w⁻¹ hw'Y
    rw [mul_inv_cancel] at hmul
    rw [show f3phi c.s 1 = 1 by simp [f3phi]] at hmul
    exact eq_inv_of_mul_eq_one_right hmul.symm
  have hm'M : w⁻¹ * m ∈ M3 c.s := (M3 c.s).mul_mem ((M3 c.s).inv_mem hwm) hm
  have hphi_m' : f3phi c.s (w⁻¹ * m) = 1 := by
    rw [y54_phi_mul hH w⁻¹ hw'Y m hmY, hphi_inv, hwphi]
    exact inv_mul_cancel (f3phi c.s m)
  have hm'F : w⁻¹ * m ∈ c.s.fr.F :=
    y54_M_inf_ker (c := c) hH (y54_M3_cand c hH) (w⁻¹ * m) hm'M hphi_m'
  have hgm' : c.g * (w⁻¹ * m) * c.g⁻¹ = w⁻¹ * m :=
    y5_g_cent_F hH hg2 hact (w⁻¹ * m) hm'F
  calc c.g * m * c.g⁻¹ = c.g * (w * (w⁻¹ * m)) * c.g⁻¹ := by group
    _ = (c.g * w * c.g⁻¹) * (c.g * (w⁻¹ * m) * c.g⁻¹) := by group
    _ = w * (w⁻¹ * m) := by rw [hwg, hgm']
    _ = m := by group

end CFSG.OddStandard.HigherRank.YamadaG23
