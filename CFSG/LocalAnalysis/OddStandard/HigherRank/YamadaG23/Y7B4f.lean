module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3d
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B4e

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_M6_le_U76 (c : Ctx7 G L) (hb : B6Std c) : M6 c.e ≤ U76 c.e := by
  unfold U76
  refine le_inf (y7b_M6_le_X76 c hb) fun m hm => ⟨?_, ?_, ?_⟩
  · exact mem_normalizer_of_forall_conj_mem (y7b_M6_norm_M5 c hb.toB5Std m hm)
  · exact mem_normalizer_of_forall_conj_mem
      (y7b_norm_of_V1_le c hb.toB5Std (N := V1 c.e) le_rfl
        ((y7b_V1_le_M5 c hb.toB5Std).trans (y7b_M5_le_M6 c hb.toB5Std)) m hm)
  · intro k hk
    exact (y7b_M6_comm_sq c hb.toB5Std).1 k (y7b_M5_le_M6 c hb.toB5Std hk) m hm

theorem y7b_U76_le_M6 (c : Ctx7 G L) (hb : B6Std c) : U76 c.e ≤ M6 c.e := by
  by_contra h
  have hle : M6 c.e ≤ U76 c.e := y7b_M6_le_U76 c hb
  have hlt : M6 c.e < U76 c.e := lt_of_le_not_ge hle h
  have ht2 : c.s.t * c.s.t = 1 := by
    rw [← pow_two, ← c.s.t_order]
    exact pow_orderOf_eq_one c.s.t
  have htR : c.s.t ∈ c.s.R := s3_t_mem_R c.s
  have htM : ∀ m ∈ M6 c.e, c.s.t * m * c.s.t⁻¹ ∈ M6 c.e := fun m hm =>
    (Subgroup.mem_normalizer_iff.mp (y7b_R_le_NM6 c hb.toB5Std htR) m).mp hm
  have htN_X : c.s.t ∈ normalizer (X76 c.e : Set G) :=
    Subgroup.le_normalizer (y7b_R_le_X76 c hb.toB5Std htR)
  have htN_cs : c.s.t ∈ normalizer (centralizerSection (M5 c.e) (V1 c.e) : Set G) :=
    mem_normalizer_centralizerSection (y7b_R_le_NM5 c hb.toB5Std htR)
      (y7b_R_le_NV1 c hb.toB5Std htR)
  have htN_U : c.s.t ∈ normalizer (U76 c.e : Set G) := by
    unfold U76
    exact mem_normalizer_inf htN_X htN_cs
  have htU : ∀ u ∈ U76 c.e, c.s.t * u * c.s.t⁻¹ ∈ U76 c.e := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp htN_U u).mp hu
  obtain ⟨u, huU, huM, huNorm, htu⟩ :=
    exists_mem_normalizer_comm_mem (Q := X76 c.e) (U := U76 c.e) (M := M6 c.e)
      (y7b_X76_isPGroup c hb) (by unfold U76; exact inf_le_left) hlt ht2 htU htM
  have hw : ⁅u, c.s.t⁆ ∈ M6 c.e := by
    have h1 : ⁅c.s.t, u⁆⁻¹ ∈ M6 c.e := (M6 c.e).inv_mem htu
    have h2 : ⁅u, c.s.t⁆ = ⁅c.s.t, u⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rwa [h2]
  let f : G →* G := MulAut.conj u
  have hM6map : (M6 c.e).map f ≤ C6 c.e := by
    rw [hb.h71.2.2.1, Subgroup.map_le_iff_le_comap]
    intro m hm
    simpa [f, MulAut.conj_apply] using Subgroup.mem_sup_left (huNorm m hm)
  have hzmap : (zpowers c.s.t).map f ≤ C6 c.e := by
    rw [hb.h71.2.2.1, MonoidHom.map_zpowers, Subgroup.zpowers_le]
    have he : f c.s.t = ⁅u, c.s.t⁆ * c.s.t := by
      show MulAut.conj u c.s.t = ⁅u, c.s.t⁆ * c.s.t
      rw [MulAut.conj_apply, commutatorElement_def]
      group
    rw [he]
    exact Subgroup.mul_mem_sup hw (Subgroup.mem_zpowers c.s.t)
  have hsupmap : (M6 c.e ⊔ zpowers c.s.t).map f ≤ C6 c.e := by
    rw [Subgroup.map_sup]
    exact sup_le hM6map hzmap
  have huN : u ∈ normalizer (C6 c.e : Set G) :=
    mem_normalizer_of_forall_conj_mem fun y hy => by
      rw [hb.h71.2.2.1] at hy
      have h1 := hsupmap (Subgroup.mem_map_of_mem f hy)
      simpa [f, MulAut.conj_apply] using h1
  have huNHA : u ∈ normIn c.s.H c.s.fr.A ⊔ M6 c.e := by
    rw [← hb.h73]
    exact huN
  obtain ⟨n, hn, m, hm, hu_eq⟩ :=
    (mem_sup_iff_exists_mul_of_le_normalizer (y7b_NHA_le_NM6 c hb.toB5Std)).mp huNHA
  have hn_eq : n = u * m⁻¹ := by rw [hu_eq]; group
  have hnU : n ∈ U76 c.e := by
    rw [hn_eq]
    exact (U76 c.e).mul_mem huU ((U76 c.e).inv_mem (y7b_M6_le_U76 c hb hm))
  have hnU' : n ∈ X76 c.e ⊓ centralizerSection (M5 c.e) (V1 c.e) := hnU
  have hnX : n ∈ X76 c.e := (Subgroup.mem_inf.mp hnU').1
  have hncs : n ∈ centralizerSection (M5 c.e) (V1 c.e) := (Subgroup.mem_inf.mp hnU').2
  have hnH : n ∈ c.s.H :=
    (Subgroup.mem_inf.mp (show n ∈ c.s.H ⊓ normalizer (c.s.fr.A : Set G) from hn)).1
  have hnT : n ∈ c.s.T := y7b_X76_inf_H_le_T c hb (Subgroup.mem_inf.mpr ⟨hnX, hnH⟩)
  have hnA : n ∈ c.s.fr.A :=
    y7b_T_inf_cs_le_A c hb.toB5Std (Subgroup.mem_inf.mpr ⟨hnT, hncs⟩)
  have hnM6 : n ∈ M6 c.e := y7b_A_le_M6 c hb.toB5Std hnA
  have huM6 : u ∈ M6 c.e := by
    rw [hu_eq]
    exact (M6 c.e).mul_mem hnM6 hm
  exact huM huM6

theorem y7b_U76_eq_M6 (c : Ctx7 G L) (hb : B6Std c) : U76 c.e = M6 c.e :=
  le_antisymm (y7b_U76_le_M6 c hb) (y7b_M6_le_U76 c hb)

theorem y7b_X76_le_NM6 (c : Ctx7 G L) (hb : B6Std c) :
    X76 c.e ≤ normalizer (M6 c.e : Set G) := by
  intro x hx
  have hxcs : x ∈ normalizer (centralizerSection (M5 c.e) (V1 c.e) : Set G) :=
    mem_normalizer_centralizerSection hx.1.1.2 hx.1.2
  have hxN : x ∈ normalizer (U76 c.e : Set G) := by
    unfold U76
    exact mem_normalizer_inf (Subgroup.le_normalizer hx) hxcs
  rwa [y7b_U76_eq_M6 c hb] at hxN

theorem y7b_M7_le_NM6 (c : Ctx7 G L) (hb : B6Std c) :
    M7 c.s ≤ normalizer (M6 c.e : Set G) :=
  fun _ hm => y7b_X76_le_NM6 c hb (y7b_M7_le_X76 c hb hm)

end CFSG.OddStandard.HigherRank.YamadaG23
