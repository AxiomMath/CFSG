module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8d
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8e

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_cs3_X7 (c : Ctx7 G L) (hb : B5Std c) {y : G} (hy : y ∈ X7 c.s)
    (hcs : y ∈ y7bCS3 c) : ∃ e ∈ c.s.fr.E, ∃ m ∈ M3 c.s, ⁅y, c.s.t⁆ = e * m := by
  have hdecomp : ⁅y, c.s.t⁆ = y * (c.s.t * y⁻¹ * c.s.t⁻¹) := by
    rw [commutatorElement_def]; group
  have hBM : ⁅y, c.s.t⁆ ∈ y7bBM c.s :=
    y7b_comm_t_mem_BM c hb y (y7b_X7_le_X c hy)
  have hty : c.s.t * y⁻¹ * c.s.t⁻¹ ∈ y7bCS3 c :=
    (Subgroup.mem_normalizer_iff.mp (y7b_t_mem_NCS3 c hb) y⁻¹).mp
      ((y7bCS3 c).inv_mem hcs)
  have hCS3 : ⁅y, c.s.t⁆ ∈ y7bCS3 c := by
    rw [hdecomp]
    exact (y7bCS3 c).mul_mem hcs hty
  exact y7b_cs3_BM c hb hBM hCS3

theorem y7b_exists_u1 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T)
    (hbad : ¬ M4 c.e ≤ M7 c.s) :
    ∃ m ∈ M4 c.e, m * c.g ∈ M7 c.s ∧ m * c.g ∈ y7bCS3 c ∧ ⁅m * c.g, c.s.t⁆ ∉ M3 c.s := by
  obtain ⟨m₀, hm₀M4, hm₀7⟩ := SetLike.not_le_iff_exists.mp hbad
  obtain ⟨m_s, hm_sM4, -, -, hm_sNot⟩ := y7b_exists_seed c hb
  have hm₀NM3 : m₀ ∈ normalizer (M3 c.s : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx =>
      y7b_M6_norm_M3 c hb m₀ (y7b_M4_le_M6 c hb hm₀M4) x hx
  have hstar : ∃ m ∈ M4 c.e, m ∉ M7 c.s ∧ ⁅m, c.s.t⁆ ∉ M3 c.s := by
    by_cases h0 : ⁅m₀, c.s.t⁆ ∈ M3 c.s
    · by_cases hs7 : m_s ∈ M7 c.s
      · refine ⟨m₀ * m_s, (M4 c.e).mul_mem hm₀M4 hm_sM4, ?_, ?_⟩
        · intro hmem
          exact hm₀7 (by simpa using (M7 c.s).mul_mem hmem ((M7 c.s).inv_mem hs7))
        · intro hc
          have hconj : m₀ * ⁅m_s, c.s.t⁆ * m₀⁻¹ ∈ M3 c.s := by
            have h1 : ⁅m₀ * m_s, c.s.t⁆ * ⁅m₀, c.s.t⁆⁻¹ ∈ M3 c.s :=
              (M3 c.s).mul_mem hc ((M3 c.s).inv_mem h0)
            rwa [commutatorElement_mul_left_eq_conj_mul,
              show m₀ * ⁅m_s, c.s.t⁆ * m₀⁻¹ * ⁅m₀, c.s.t⁆ * ⁅m₀, c.s.t⁆⁻¹ =
                m₀ * ⁅m_s, c.s.t⁆ * m₀⁻¹ by group] at h1
          exact hm_sNot ((Subgroup.mem_normalizer_iff.mp hm₀NM3 ⁅m_s, c.s.t⁆).mpr hconj)
      · exact ⟨m_s, hm_sM4, hs7, hm_sNot⟩
    · exact ⟨m₀, hm₀M4, hm₀7, h0⟩
  obtain ⟨m, hmM4, hm7, hmt⟩ := hstar
  have hgCS3 : c.g ∈ y7bCS3 c := y7b_g_mem_CS3 c hb hRT
  have hmCS3 : m ∈ y7bCS3 c := y7b_M6_le_CS3 c hb (y7b_M4_le_M6 c hb hmM4)
  have hgt : ⁅c.g, c.s.t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (s3_comm_t_of_mem_T c.s (c.g_spec hRT).1)
  refine ⟨m, hmM4, ?_, ?_, ?_⟩
  · rcases y7b_M4_cases_M7_g c hb hRT m hmM4 with h | h
    · exact absurd h hm7
    · exact h
  · exact (y7bCS3 c).mul_mem hmCS3 hgCS3
  · intro hc
    have heq : ⁅m * c.g, c.s.t⁆ = ⁅m, c.s.t⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hgt]
      group
    exact hmt (heq ▸ hc)

theorem y7b_exists_x (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∃ x ∈ M7 c.s, x ∈ y7bCS3 c ∧ x ∈ y7bCS5 c ∧ ⁅x, c.s.t⁆ ∉ M3 c.s := by
  obtain ⟨a, haA, u, huBM, hau⟩ := y7b_A_acts_BM c hb
  obtain ⟨m, hmM7, hmu⟩ := y7b_theta_onto_M7 c hb u huBM
  have haL : a ∈ normIn L c.s.fr.B :=
    ⟨s3_S_le_L c.s (s3_A_le_S c.s haA), (y7b_S_le_normIn c hb (s3_A_le_S c.s haA)).2⟩
  have haM6 : a ∈ M6 c.e := y7b_A_le_M6 c hb haA
  have haCS3 : a ∈ y7bCS3 c := y7b_M6_le_CS3 c hb haM6
  have haCS5 : a ∈ y7bCS5 c := y7b_M6_le_CS5 c hb haM6
  have hmCS3 : m ∈ normalizer (y7bCS3 c : Set G) := y7b_M7_mem_NCS3 c hb hmM7
  have hmCS5 : m ∈ normalizer (y7bCS5 c : Set G) := y7b_M7_mem_NCS5 c hb hRT hmM7
  have hxM7 : ⁅a, m⁆ ∈ M7 c.s := by
    have h1 : a * m * a⁻¹ ∈ M7 c.s := (y7b_M7_normal c hb).2 a haL m hmM7
    rw [show ⁅a, m⁆ = a * m * a⁻¹ * m⁻¹ by rw [commutatorElement_def]]
    exact (M7 c.s).mul_mem h1 ((M7 c.s).inv_mem hmM7)
  have hxCS3 : ⁅a, m⁆ ∈ y7bCS3 c := by
    have h2 : m * a⁻¹ * m⁻¹ ∈ y7bCS3 c :=
      (Subgroup.mem_normalizer_iff.mp hmCS3 a⁻¹).mp ((y7bCS3 c).inv_mem haCS3)
    rw [show ⁅a, m⁆ = a * (m * a⁻¹ * m⁻¹) by rw [commutatorElement_def]; group]
    exact (y7bCS3 c).mul_mem haCS3 h2
  have hxCS5 : ⁅a, m⁆ ∈ y7bCS5 c := by
    have h2 : m * a⁻¹ * m⁻¹ ∈ y7bCS5 c :=
      (Subgroup.mem_normalizer_iff.mp hmCS5 a⁻¹).mp ((y7bCS5 c).inv_mem haCS5)
    rw [show ⁅a, m⁆ = a * (m * a⁻¹ * m⁻¹) by rw [commutatorElement_def]; group]
    exact (y7bCS5 c).mul_mem haCS5 h2
  refine ⟨⁅a, m⁆, hxM7, hxCS3, hxCS5, ?_⟩
  intro h
  have hcomm := y7b_theta_comm c hb haL hmM7 huBM hmu
  have h1 : (⁅a, u⁆)⁻¹ ∈ M3 c.s := by
    have h2 : ((⁅a, u⁆)⁻¹ * ⁅⁅a, m⁆, c.s.t⁆) * (⁅⁅a, m⁆, c.s.t⁆)⁻¹ ∈ M3 c.s :=
      (M3 c.s).mul_mem hcomm ((M3 c.s).inv_mem h)
    rw [mul_inv_cancel_right] at h2
    exact h2
  have h1' : ⁅a, u⁆ ∈ M3 c.s := by
    simpa only [inv_inv] using (M3 c.s).inv_mem h1
  exact hau h1'

end CFSG.OddStandard.HigherRank.YamadaG23
