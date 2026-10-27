module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7t

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_M6_le_CS3 (c : Ctx7 G L) (hb : B5Std c) : M6 c.e ≤ y7bCS3 c := by
  intro x hx
  have hV1M6 : V1 c.e ≤ M6 c.e :=
    (y7b_V1_le_M4 c hb).trans
      ((show M4 c.e ≤ M5 c.e from le_sup_right).trans (y7b_M5_le_M6 c hb))
  refine ⟨?_, ?_, ?_⟩
  · exact Subgroup.mem_normalizer_fintype fun n hn => y7b_M6_norm_M3 c hb x hx n hn
  · exact Subgroup.mem_normalizer_fintype fun n hn =>
      y7b_norm_of_V1_le c hb (le_refl (V1 c.e)) hV1M6 x hx n hn
  · intro k hk
    exact (y7b_M6_comm_sq c hb).1 k (hb.h71.2.2.2.1 hk) x hx

theorem y7b_M6_le_CS5 (c : Ctx7 G L) (hb : B5Std c) : M6 c.e ≤ y7bCS5 c := by
  intro x hx
  have hV1M6 : V1 c.e ≤ M6 c.e :=
    (y7b_V1_le_M4 c hb).trans
      ((show M4 c.e ≤ M5 c.e from le_sup_right).trans (y7b_M5_le_M6 c hb))
  refine ⟨?_, ?_, ?_⟩
  · exact Subgroup.mem_normalizer_fintype fun n hn => y7b_M6_norm_M5 c hb x hx n hn
  · exact Subgroup.mem_normalizer_fintype fun n hn =>
      y7b_norm_of_V1_le c hb (le_refl (V1 c.e)) hV1M6 x hx n hn
  · intro k hk
    exact (y7b_M6_comm_sq c hb).1 k (y7b_M5_le_M6 c hb hk) x hx

theorem y7b_g_mem_CS3 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    c.g ∈ y7bCS3 c := by
  refine ⟨?_, ?_, ?_⟩
  · exact Subgroup.mem_normalizer_fintype fun n hn => by
      rw [y7b_g_cent_M3 c hb hRT n hn]
      exact hn
  · exact Subgroup.mem_normalizer_fintype fun n hn => by
      rw [y7b_g_cent_V2 c hb hRT n (y7b_V1_le_V2 c hb hn)]
      exact hn
  · intro k hk
    have hcomm : ⁅k, c.g⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      calc k * c.g = (c.g * k * c.g⁻¹) * c.g := by rw [y7b_g_cent_M3 c hb hRT k hk]
        _ = c.g * k := by group
    rw [hcomm]
    exact (V1 c.e).one_mem

theorem y7b_t_mem_NCS3 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.t ∈ normalizer (y7bCS3 c : Set G) := by
  exact mem_normalizer_centralizerSection (y7b_R_le_NM3 hb.hH (s3_t_mem_R c.s))
    (y7b_R_le_NV1 c hb (s3_t_mem_R c.s))

theorem y7b_M7_comm_mem_M3 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ m ∈ M7 c.s, ∀ n ∈ M7 c.s, ⁅m, n⁆ ∈ M3 c.s := by
  refine y7b_comm_mem_of_sq_mem ?_ ?_ (y7b_M7_sq_mem_M3 c hb)
  · exact (le_sup_right : M3 c.s ≤ y7bBM c.s).trans (y7b_BM_le_M7 c hb)
  · intro v hv n hn
    have hvX : v ∈ y7bX c.s :=
      y7b_X7_le_X c ((y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb) hv)
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hvX).2 n).mp hn

theorem y7b_M7_norm_V1 (c : Ctx7 G L) (hb : B5Std c) :
    M7 c.s ≤ normalizer (V1 c.e : Set G) := by
  intro m hm
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hcomm : m * n = n * m :=
    y7b_M7_le_cent_V2 c hb m hm n (y7b_V1_le_V2 c hb hn)
  rw [show m * n * m⁻¹ = n by rw [hcomm]; group]
  exact hn

theorem y7b_M7_norm_M5 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    M7 c.s ≤ normalizer (M5 c.e : Set G) := by
  intro m hm
  have hmNM3 : m ∈ normalizer (M3 c.s : Set G) :=
    (Subgroup.mem_inf.mp (y7b_X7_le_X c
      ((y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb) hm))).2
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨a, haM3, b, hbM4, rfl⟩ := (y7b_M5_mem c hb).mp hx
  have hmb : ⁅m, b⁆ ∈ M3 c.s := by
    rcases y7b_M4_cases_M7_g c hb hRT b hbM4 with hbM7 | hbgM7
    · exact y7b_M7_comm_mem_M3 c hb m hm b hbM7
    · have hbgNM3 : b * c.g ∈ normalizer (M3 c.s : Set G) := by
        refine Subgroup.mem_normalizer_fintype fun w hw => ?_
        have hgm : c.g * w * c.g⁻¹ = w := y7b_g_cent_M3 c hb hRT w hw
        have hbm : b * w * b⁻¹ ∈ M3 c.s :=
          y7b_M6_norm_M3 c hb b (hb.h71.2.2.2.2 hbM4) w hw
        have he : (b * c.g) * w * (b * c.g)⁻¹ = b * w * b⁻¹ := by
          rw [show (b * c.g) * w * (b * c.g)⁻¹ =
            b * (c.g * w * c.g⁻¹) * b⁻¹ by group, hgm]
        rw [he]
        exact hbm
      have h1 : ⁅m, b * c.g⁆ ∈ M3 c.s :=
        y7b_M7_comm_mem_M3 c hb m hm (b * c.g) hbgM7
      have h2 : ⁅m, c.g⁆ ∈ M3 c.s := by
        rw [← commutatorElement_inv]
        exact (M3 c.s).inv_mem (y7b_g_comm_M7 c hb hRT m hm)
      have h3 : (b * c.g) * ⁅m, c.g⁆ * (b * c.g)⁻¹ ∈ M3 c.s :=
        (Subgroup.mem_normalizer_iff.mp hbgNM3 _).mp h2
      have hb_eq : b = (b * c.g) * c.g := by
        rw [mul_assoc, y7b_g_mul_self c hb hRT, mul_one]
      rw [hb_eq, commutatorElement_mul_right_eq_mul_conj]
      rw [show ⁅m, b * c.g⁆ * (b * c.g) * ⁅m, c.g⁆ * (b * c.g)⁻¹ =
          ⁅m, b * c.g⁆ * ((b * c.g) * ⁅m, c.g⁆ * (b * c.g)⁻¹) by group]
      exact (M3 c.s).mul_mem h1 h3
  have hma : m * a * m⁻¹ ∈ M3 c.s := (Subgroup.mem_normalizer_iff.mp hmNM3 a).mp haM3
  have heq : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (⁅m, b⁆ * b) := by
    rw [commutatorElement_def]; group
  rw [heq]
  change _ ∈ M3 c.s ⊔ M4 c.e
  exact (M3 c.s ⊔ M4 c.e).mul_mem (Subgroup.mem_sup_left hma)
    ((M3 c.s ⊔ M4 c.e).mul_mem (Subgroup.mem_sup_left hmb)
      (Subgroup.mem_sup_right hbM4))

theorem y7b_M7_mem_NCS3 (c : Ctx7 G L) (hb : B5Std c) {m : G} (hm : m ∈ M7 c.s) :
    m ∈ normalizer (y7bCS3 c : Set G) := by
  have hmNM3 : m ∈ normalizer (M3 c.s : Set G) :=
    (Subgroup.mem_inf.mp (y7b_X7_le_X c
      ((y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb) hm))).2
  exact mem_normalizer_centralizerSection hmNM3 (y7b_M7_norm_V1 c hb hm)

theorem y7b_M7_mem_NCS5 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) {m : G}
    (hm : m ∈ M7 c.s) : m ∈ normalizer (y7bCS5 c : Set G) := by
  exact mem_normalizer_centralizerSection (y7b_M7_norm_M5 c hb hRT hm) (y7b_M7_norm_V1 c hb hm)

end CFSG.OddStandard.HigherRank.YamadaG23
