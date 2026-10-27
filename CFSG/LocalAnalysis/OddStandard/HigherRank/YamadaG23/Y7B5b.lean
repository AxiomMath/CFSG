module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3f
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B4c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B5a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem commutator_mem_of_mem_normalizer {K : Subgroup G} {x y : G} (hx : x ∈ K)
    (hy : y ∈ normalizer (K : Set G)) : ⁅x, y⁆ ∈ K := by
  have h := (Subgroup.mem_normalizer_iff.mp hy x).mp hx
  have he : ⁅x, y⁆ = x * (y * x * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [he]
  exact K.mul_mem hx (K.inv_mem h)

private theorem comm_t_mem_M5_of_mem_AM5 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ AM5 c.e, ⁅y, c.s.t⁆ ∈ M5 c.e := by
  intro y hy
  have hAnorm : c.s.fr.A ≤ normalizer (M5 c.e : Set G) :=
    (s3_A_le_S c.s).trans (c.s.S_le_R.trans (y7b_R_le_NM5 c hb))
  have htM5 : c.s.t ∈ normalizer (M5 c.e : Set G) :=
    y7b_R_le_NM5 c hb (s3_t_mem_R c.s)
  change y ∈ c.s.fr.A ⊔ M5 c.e at hy
  obtain ⟨a, ha, m, hm, rfl⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hAnorm).mp hy
  have hat : ⁅a, c.s.t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (s3_comm_t_of_mem_A c.s ha)
  have hmc : ⁅m, c.s.t⁆ ∈ M5 c.e := commutator_mem_of_mem_normalizer hm htM5
  rw [commutatorElement_mul_left_eq_conj_mul, hat, mul_one]
  exact (Subgroup.mem_normalizer_iff.mp (hAnorm ha) ⁅m, c.s.t⁆).mp hmc

private theorem comm_t_mem_M5_of_mem_BM5 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ BM5 c.e, ⁅y, c.s.t⁆ ∈ M5 c.e := by
  intro y hy
  have hBnorm : c.s.fr.B ≤ normalizer (M5 c.e : Set G) :=
    (s3_B_le_S c.s).trans (c.s.S_le_R.trans (y7b_R_le_NM5 c hb))
  have htM5 : c.s.t ∈ normalizer (M5 c.e : Set G) :=
    y7b_R_le_NM5 c hb (s3_t_mem_R c.s)
  change y ∈ c.s.fr.B ⊔ M5 c.e at hy
  obtain ⟨b, hbB, m, hm, rfl⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hBnorm).mp hy
  have hbt : ⁅b, c.s.t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (s3_comm_t_of_mem_L c.s (s3_S_le_L c.s (s3_B_le_S c.s hbB)))
  have hmc : ⁅m, c.s.t⁆ ∈ M5 c.e := commutator_mem_of_mem_normalizer hm htM5
  rw [commutatorElement_mul_left_eq_conj_mul, hbt, mul_one]
  exact (Subgroup.mem_normalizer_iff.mp (hBnorm hbB) ⁅m, c.s.t⁆).mp hmc

private theorem comm_t_mul_mem_M5 {c : Ctx7 G L} {x y : G}
    (hxN : x ∈ normalizer (M5 c.e : Set G)) (hx : ⁅x, c.s.t⁆ ∈ M5 c.e)
    (hy : ⁅y, c.s.t⁆ ∈ M5 c.e) : ⁅x * y, c.s.t⁆ ∈ M5 c.e := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact (M5 c.e).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN ⁅y, c.s.t⁆).mp hy) hx

theorem y7b_M6_cent_t_le_AM5 (c : Ctx7 G L) (hb : B6Std c) :
    ∀ x ∈ M6 c.e, ⁅x, c.s.t⁆ ∈ M5 c.e → x ∈ AM5 c.e := by
  intro x hxM6 hx
  by_contra hxAM5
  obtain ⟨k, hkM6, hk⟩ := y7b_exists_M6_comm_not_mem_M5 c hb
  have hxN : x ∈ normalizer (M5 c.e : Set G) :=
    mem_normalizer_of_forall_conj_mem (y7b_M6_norm_M5 c hb.toB5Std x hxM6)
  rcases mem_or_mem_of_relIndex_two (y7b_AM5_le_M6 c hb.toB5Std)
    (y7b_relIndex_AM5_M6 c hb) hxM6 hxAM5 hkM6 with hkAM5 | hxinvk
  · exact hk (comm_t_mem_M5_of_mem_AM5 c hb.toB5Std k hkAM5)
  · have h1 : ⁅x⁻¹ * k, c.s.t⁆ ∈ M5 c.e :=
      comm_t_mem_M5_of_mem_AM5 c hb.toB5Std (x⁻¹ * k) hxinvk
    have hkeq : k = x * (x⁻¹ * k) := by group
    exact hk (by rw [hkeq]; exact comm_t_mul_mem_M5 hxN hx h1)

theorem y7b_M7_cent_t_le_BM5 (c : Ctx7 G L) (hb : B6Std c) :
    ∀ x ∈ M7 c.s, ⁅x, c.s.t⁆ ∈ M5 c.e → x ∈ BM5 c.e := by
  intro x hxM7 hx
  by_contra hxBM5
  obtain ⟨k, hkM7, hk⟩ := y7b_exists_M7_comm_not_mem_M5 c hb
  have hxN : x ∈ normalizer (M5 c.e : Set G) := y7b_M7_le_NM5 c hb hxM7
  rcases mem_or_mem_of_relIndex_two (y7b_BM5_le_M7 c hb)
    (y7b_relIndex_BM5_M7 c hb) hxM7 hxBM5 hkM7 with hkBM5 | hxinvk
  · exact hk (comm_t_mem_M5_of_mem_BM5 c hb.toB5Std k hkBM5)
  · have h1 : ⁅x⁻¹ * k, c.s.t⁆ ∈ M5 c.e :=
      comm_t_mem_M5_of_mem_BM5 c hb.toB5Std (x⁻¹ * k) hxinvk
    have hkeq : k = x * (x⁻¹ * k) := by group
    exact hk (by rw [hkeq]; exact comm_t_mul_mem_M5 hxN hx h1)

theorem y7b_M6_inf_M7 (c : Ctx7 G L) (hb : B6Std c) : M6 c.e ⊓ M7 c.s = M5 c.e := by
  refine le_antisymm ?_ (le_inf (y7b_M5_le_M6 c hb.toB5Std) (y7b_M5_le_M7 c hb))
  intro x hx
  obtain ⟨hxM6, hxM7⟩ := Subgroup.mem_inf.mp hx
  have htR : c.s.t ∈ c.s.R := s3_t_mem_R c.s
  have hxtR5 : ⁅x, c.s.t⁆ ∈ R5 c.e :=
    y7b_SM5_le_R5 c (y7b_X76_comm_t c hb x (y7b_M6_le_X76 c hb hxM6))
  have hxtM6 : ⁅x, c.s.t⁆ ∈ M6 c.e :=
    commutator_mem_of_mem_normalizer hxM6 (y7b_R_le_NM6 c hb.toB5Std htR)
  have hxtM7 : ⁅x, c.s.t⁆ ∈ M7 c.s :=
    commutator_mem_of_mem_normalizer hxM7 (y7b_R_le_NM7 hb.hH htR)
  have hAM5 : ⁅x, c.s.t⁆ ∈ AM5 c.e := by
    rw [← y7b_R5_inf_M6 c hb.toB5Std]
    exact Subgroup.mem_inf.mpr ⟨hxtR5, hxtM6⟩
  have hBM5 : ⁅x, c.s.t⁆ ∈ BM5 c.e := by
    rw [← y7b_R5_inf_M7 c hb]
    exact Subgroup.mem_inf.mpr ⟨hxtR5, hxtM7⟩
  have hM5 : ⁅x, c.s.t⁆ ∈ M5 c.e := by
    rw [← y7b_AM5_inf_BM5 c hb]
    exact Subgroup.mem_inf.mpr ⟨hAM5, hBM5⟩
  have h1 : x ∈ AM5 c.e := y7b_M6_cent_t_le_AM5 c hb x hxM6 hM5
  have h2 : x ∈ BM5 c.e := y7b_M7_cent_t_le_BM5 c hb x hxM7 hM5
  rw [← y7b_AM5_inf_BM5 c hb]
  exact Subgroup.mem_inf.mpr ⟨h1, h2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
