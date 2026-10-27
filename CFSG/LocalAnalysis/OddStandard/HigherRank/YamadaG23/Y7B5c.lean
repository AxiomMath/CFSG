module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B4f
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B5b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_P7_mem (c : Ctx7 G L) (hb : B6Std c) {x : G} :
    x ∈ P7 c.e ↔ ∃ m ∈ M6 c.e, ∃ n ∈ M7 c.s, x = m * n := by
  unfold P7
  rw [sup_comm]
  exact mem_sup_iff_exists_mul_of_le_normalizer' (H := M7 c.s) (K := M6 c.e)
    (y7b_M7_le_NM6 c hb)

theorem y7b_P7_set_eq (c : Ctx7 G L) (hb : B6Std c) :
    (P7 c.e : Set G) = (M6 c.e : Set G) * (M7 c.s : Set G) := by
  ext x
  rw [Set.mem_mul]
  constructor
  · intro hx
    obtain ⟨m, hm, n, hn, hmn⟩ := (y7b_P7_mem c hb).mp hx
    exact ⟨m, hm, n, hn, hmn.symm⟩
  · rintro ⟨m, hm, n, hn, hmn⟩
    exact (y7b_P7_mem c hb).mpr ⟨m, hm, n, hn, hmn.symm⟩

theorem y7b_card_P7 (c : Ctx7 G L) (hb : B6Std c) : Nat.card ↥(P7 c.e) = 2 ^ 12 := by
  have hb5 := hb.toB5Std
  have hcard := card_sup_mul_card_inf_of_le_normalizer (H := M7 c.s) (K := M6 c.e)
    (y7b_M7_le_NM6 c hb)
  rw [show M7 c.s ⊓ M6 c.e = M5 c.e by rw [inf_comm, y7b_M6_inf_M7 c hb],
    y7b_card_M7 c hb, y7b_card_M6 c hb5, y7b_card_M5 c hb5] at hcard
  have hP : P7 c.e = M7 c.s ⊔ M6 c.e := by unfold P7; rw [sup_comm]
  rw [hP]
  apply Nat.eq_of_mul_eq_mul_right (by norm_num : (0 : ℕ) < 2 ^ 8)
  rw [hcard]
  norm_num

theorem y7b_P7_cent_t (c : Ctx7 G L) (hb : B6Std c) :
    centEl (P7 c.e) c.s.t = c.s.fr.S := by
  have hb5 := hb.toB5Std
  apply le_antisymm
  · intro p hp
    rw [centEl] at hp
    obtain ⟨hpP7, hpC⟩ := Subgroup.mem_inf.mp hp
    have htp : c.s.t * p = p * c.s.t :=
      (Subgroup.mem_centralizer_iff.mp hpC) c.s.t (Set.mem_singleton c.s.t)
    obtain ⟨m, hm, n, hn, hp_eq⟩ := (y7b_P7_mem c hb).mp hpP7
    have hpt : p * c.s.t * p⁻¹ * c.s.t⁻¹ = 1 := by rw [htp.symm]; group
    have hmn_t : ⁅m * n, c.s.t⁆ = 1 := by
      have h2 : (m * n) * c.s.t * (m * n)⁻¹ * c.s.t⁻¹ = 1 := by
        rw [← hp_eq]; exact hpt
      rwa [commutatorElement_def]
    have hmX : m ∈ X76 c.e := y7b_M6_le_X76 c hb hm
    have hnX : n ∈ X76 c.e := y7b_M7_le_X76 c hb hn
    have hm_r5 : ⁅m, c.s.t⁆ ∈ R5 c.e :=
      y7b_SM5_le_R5 c (y7b_X76_comm_t c hb m hmX)
    have hn_r5 : ⁅n, c.s.t⁆ ∈ R5 c.e :=
      y7b_SM5_le_R5 c (y7b_X76_comm_t c hb n hnX)
    have htN6 : c.s.t ∈ normalizer (M6 c.e : Set G) := y7b_R_le_NM6 c hb5 (s3_t_mem_R c.s)
    have hm_comm_M6 : ⁅m, c.s.t⁆ ∈ M6 c.e := by
      have h1 : c.s.t * m⁻¹ * c.s.t⁻¹ ∈ M6 c.e :=
        (Subgroup.mem_normalizer_iff.mp htN6 m⁻¹).mp ((M6 c.e).inv_mem hm)
      have he : ⁅m, c.s.t⁆ = m * (c.s.t * m⁻¹ * c.s.t⁻¹) := by
        rw [commutatorElement_def]; group
      rw [he]; exact (M6 c.e).mul_mem hm h1
    have hm_AM5 : ⁅m, c.s.t⁆ ∈ AM5 c.e := by
      rw [← y7b_R5_inf_M6 c hb5]
      exact Subgroup.mem_inf.mpr ⟨hm_r5, hm_comm_M6⟩
    have htN7 : c.s.t ∈ normalizer (M7 c.s : Set G) := y7b_R_le_NM7 hb.hH (s3_t_mem_R c.s)
    have hn_comm_M7 : ⁅n, c.s.t⁆ ∈ M7 c.s := by
      have h1 : c.s.t * n⁻¹ * c.s.t⁻¹ ∈ M7 c.s :=
        (Subgroup.mem_normalizer_iff.mp htN7 n⁻¹).mp ((M7 c.s).inv_mem hn)
      have he : ⁅n, c.s.t⁆ = n * (c.s.t * n⁻¹ * c.s.t⁻¹) := by
        rw [commutatorElement_def]; group
      rw [he]; exact (M7 c.s).mul_mem hn h1
    have hn_BM5 : ⁅n, c.s.t⁆ ∈ BM5 c.e := by
      rw [← y7b_R5_inf_M7 c hb]
      exact Subgroup.mem_inf.mpr ⟨hn_r5, hn_comm_M7⟩
    have hAB : ∀ g ∈ AM5 c.e, g ∈ BM5 c.e → g ∈ M5 c.e := by
      intro g hgA hgB
      rw [← y7b_AM5_inf_BM5 c hb]
      exact Subgroup.mem_inf.mpr ⟨hgA, hgB⟩
    have hxB : ∀ b ∈ BM5 c.e, ⁅m, b⁆ ∈ M5 c.e := fun b hbB =>
      y7b_X76_comm_SM5 c hb m hmX b (y7b_BM5_le_SM5 c hb5 hbB)
    have hxM : ∀ m' ∈ M5 c.e, m⁻¹ * m' * m ∈ M5 c.e := by
      intro m' hm'
      simpa using y7b_M6_norm_M5 c hb5 m⁻¹ ((M6 c.e).inv_mem hm) m' hm'
    obtain ⟨hmt_M5, hnt_M5⟩ := comm_mem_of_comm_mul_eq_one
      (A' := AM5 c.e) (B' := BM5 c.e) (M := M5 c.e)
      (x := m) (y := n) (t := c.s.t)
      (y7b_M5_le_AM5 c) (y7b_M5_le_BM5 c) hAB hxB hxM hm_AM5 hn_BM5 hmn_t
    have hm_AM5' : m ∈ AM5 c.e := y7b_M6_cent_t_le_AM5 c hb m hm hmt_M5
    have hn_BM5' : n ∈ BM5 c.e := y7b_M7_cent_t_le_BM5 c hb n hn hnt_M5
    have hp_SM5 : p ∈ SM5 c.e := by
      rw [hp_eq]
      exact (SM5 c.e).mul_mem (y7b_AM5_le_SM5 c hm_AM5') (y7b_BM5_le_SM5 c hb5 hn_BM5')
    have hp_H : p ∈ c.s.H := by
      show p ∈ Subgroup.centralizer ({c.s.t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact htp
    have hp_inf : p ∈ c.s.H ⊓ SM5 c.e := Subgroup.mem_inf.mpr ⟨hp_H, hp_SM5⟩
    rw [y7b_H_inf_SM5 c hb] at hp_inf
    exact hp_inf
  · intro x hx
    rw [centEl, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · have hSP7 : c.s.fr.S ≤ P7 c.e := by
        rw [y7b_S_eq_sup hb.hH]
        exact sup_le_sup (y7b_A_le_M6 c hb5) (y7b_B_le_M7 c hb)
      exact hSP7 hx
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hxH : x ∈ c.s.H := (s3_L_le_H c.s hb.hH.hS) ((s3_S_le_L c.s) hx)
      exact (Subgroup.mem_centralizer_iff.mp hxH) c.s.t (Set.mem_singleton c.s.t)

theorem y7b_P7_le_NM6 (c : Ctx7 G L) (hb : B6Std c) :
    P7 c.e ≤ normalizer (M6 c.e : Set G) := by
  unfold P7
  exact sup_le Subgroup.le_normalizer (y7b_M7_le_NM6 c hb)

end CFSG.OddStandard.HigherRank.YamadaG23
