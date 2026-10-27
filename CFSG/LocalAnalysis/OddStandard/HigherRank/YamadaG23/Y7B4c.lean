module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B4b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_X76_comm_SM5 (c : Ctx7 G L) (hb : B6Std c) :
    ∀ x ∈ X76 c.e, ∀ w ∈ SM5 c.e, ⁅x, w⁆ ∈ M5 c.e := by
  have hb5 : B5Std c := hb.toB5Std
  intro x hx w hw
  have hxM5 : x ∈ normalizer (M5 c.e : Set G) := hx.1.1.2
  have hxAM : x ∈ normalizer (AM5 c.e : Set G) := y7b_X76_le_NAM5 c hb hx
  have hxBM : x ∈ normalizer (BM5 c.e : Set G) := y7b_X76_le_NBM5 c hb hx
  have hAM : ∀ a ∈ AM5 c.e, ⁅x, a⁆ ∈ M5 c.e :=
    comm_mem_of_relIndex_two (y7b_M5_le_AM5 c) (y7b_relIndex_M5_AM5 c hb)
      (fun a ha => (Subgroup.mem_normalizer_iff.mp hxAM a).mp ha)
      (fun m hm => (Subgroup.mem_normalizer_iff.mp hxM5 m).mp hm)
  have hBM : ∀ b ∈ BM5 c.e, ⁅x, b⁆ ∈ M5 c.e :=
    comm_mem_of_relIndex_two (y7b_M5_le_BM5 c) (y7b_relIndex_M5_BM5 c hb)
      (fun b hb' => (Subgroup.mem_normalizer_iff.mp hxBM b).mp hb')
      (fun m hm => (Subgroup.mem_normalizer_iff.mp hxM5 m).mp hm)
  have hAnB : AM5 c.e ≤ normalizer (BM5 c.e : Set G) :=
    le_trans (y7b_AM5_le_SM5 c)
      (le_normalizer_of_relIndex_two (y7b_BM5_le_SM5 c hb5) (y7b_relIndex_BM5_SM5 c hb))
  rw [y7b_SM5_eq c hb5] at hw
  obtain ⟨a, ha, b, hbm, rfl⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hAnB).mp hw
  have hxa : ⁅x, a⁆ ∈ M5 c.e := hAM a ha
  have hxb : ⁅x, b⁆ ∈ M5 c.e := hBM b hbm
  have haN : a ∈ normalizer (M5 c.e : Set G) :=
    y7b_SM5_le_NM5 c hb5 (y7b_AM5_le_SM5 c ha)
  have hconj : a * ⁅x, b⁆ * a⁻¹ ∈ M5 c.e :=
    (Subgroup.mem_normalizer_iff.mp haN ⁅x, b⁆).mp hxb
  have hcomm : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [hcomm]
  exact (M5 c.e).mul_mem hxa hconj

theorem y7b_X76_comm_t (c : Ctx7 G L) (hb : B6Std c) :
    ∀ x ∈ X76 c.e, ⁅x, c.s.t⁆ ∈ SM5 c.e := by
  intro x hx
  have hxR5 : x ∈ normalizer (R5 c.e : Set G) := hx.1.1.1
  have hxSM : x ∈ normalizer (SM5 c.e : Set G) := y7b_X76_le_NSM5 c hb hx
  have hcomm : ∀ w ∈ R5 c.e, ⁅x, w⁆ ∈ SM5 c.e :=
    comm_mem_of_relIndex_two (y7b_SM5_le_R5 c) (y7b_relIndex_SM5_R5 c hb)
      (fun w hw => (Subgroup.mem_normalizer_iff.mp hxR5 w).mp hw)
      (fun m hm => (Subgroup.mem_normalizer_iff.mp hxSM m).mp hm)
  exact hcomm c.s.t (Subgroup.mem_sup_left (s3_t_mem_R c.s))

theorem y7b_X76_inf_H_le_T (c : Ctx7 G L) (hb : B6Std c) :
    X76 c.e ⊓ c.s.H ≤ c.s.T := by
  have hb5 : B5Std c := hb.toB5Std
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxX, hxH⟩ := hx
  have hxHn : x ∈ normalizer (c.s.H : Set G) := Subgroup.le_normalizer hxH
  have hxAM : x ∈ normalizer (AM5 c.e : Set G) := y7b_X76_le_NAM5 c hb hxX
  have hxBM : x ∈ normalizer (BM5 c.e : Set G) := y7b_X76_le_NBM5 c hb hxX
  have hxA : x ∈ normalizer (c.s.fr.A : Set G) := by
    have h := mem_normalizer_inf hxHn hxAM
    rwa [y7b_H_inf_AM5 c hb5] at h
  have hxB : x ∈ normalizer (c.s.fr.B : Set G) := by
    have h := mem_normalizer_inf hxHn hxBM
    rwa [y7b_H_inf_BM5 c hb] at h
  have hxS : x ∈ normalizer (c.s.fr.S : Set G) := by
    have h := mem_normalizer_sup hxA hxB
    rwa [← y7b_S_eq_sup hb.hH] at h
  rw [← y7b_NH_S hb.hH]
  simpa only [normIn] using Subgroup.mem_inf.mpr ⟨hxH, hxS⟩

end CFSG.OddStandard.HigherRank.YamadaG23
