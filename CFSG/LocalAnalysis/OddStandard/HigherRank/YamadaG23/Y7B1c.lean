module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B0Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Mb

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem mem_E_of_mul_d_sq (c : Ctx7 G L) (hb : B5Std c) {q : G}
    (hq : q ∈ e4Q c.s) (hqd : (q * c.d) ^ 2 = 1) : q ∈ c.s.fr.E := by
  rcases y56_mem_Q c.s hq with hqE | ⟨f, hf, rfl⟩
  · exact hqE
  · exfalso
    have hfA : f ∈ c.s.fr.A := s3_E_le_A c.s hf
    have hdf : c.d * f * c.d⁻¹ = f := y5_d_cent_A c.toCtx5 f hfA
    have hdt : c.d * c.s.t * c.d⁻¹ = c.s.fr.z * c.s.t := y5_dtd (c := c.toCtx5) hb.hH
    have hdd : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c.toCtx5
    have hff : f ^ 2 = 1 := y56_E_sq hb.hH f hf
    have htt : c.s.t * c.s.t = 1 := by
      rw [← pow_two, ← c.s.t_order]; exact pow_orderOf_eq_one c.s.t
    have hft : f * c.s.t = c.s.t * f := y56_t_comm_E c.s f hf
    have hzt : c.s.fr.z * c.s.t = c.s.t * c.s.fr.z :=
      y56_t_comm_E c.s c.s.fr.z (y56_z_mem_E hb.hH)
    have hdf' : c.d * f = f * c.d := by
      calc c.d * f = c.d * f * (c.d⁻¹ * c.d) := by group
        _ = (c.d * f * c.d⁻¹) * c.d := by group
        _ = f * c.d := by rw [hdf]
    have hcomm : Commute f (c.s.t * c.d) := by
      calc f * (c.s.t * c.d) = f * c.s.t * c.d := by group
        _ = c.s.t * f * c.d := by rw [hft]
        _ = c.s.t * (f * c.d) := by group
        _ = c.s.t * (c.d * f) := by rw [← hdf']
        _ = (c.s.t * c.d) * f := by group
    have htd : (c.s.t * c.d) ^ 2 = c.s.fr.z := by
      calc (c.s.t * c.d) ^ 2 = c.s.t * (c.d * c.s.t * c.d⁻¹) * (c.d * c.d) := by
            rw [pow_two]; group
        _ = c.s.t * (c.s.fr.z * c.s.t) * 1 := by rw [hdt, hdd]
        _ = c.s.fr.z := by rw [hzt, ← mul_assoc, htt, one_mul, mul_one]
    have key : (f * c.s.t * c.d) ^ 2 = c.s.fr.z := by
      rw [show f * c.s.t * c.d = f * (c.s.t * c.d) by group,
        hcomm.mul_pow 2, hff, htd, one_mul]
    rw [key] at hqd
    exact y54_z_ne_one (c := c.toCtx5) hb.hH hqd

private theorem inv_in_E (c : Ctx7 G L) (hb : B5Std c) {x : G} (hx : x ∈ C4 c.s) :
    ⁅x, c.d⁆ ∈ c.s.fr.E := by
  have hC4 := y56_C4_cand c.toCtx5 hb.hH
  have hxY : x ∈ e4Y c.s := hC4.2.1 hx
  have hdY : c.d ∈ e4Y c.s := hC4.2.1 hC4.2.2.2.2.2
  have hq : ⁅x, c.d⁆ ∈ e4Q c.s := y56_Y_comm c.toCtx5 hb.hH x hxY c.d hdY
  refine mem_E_of_mul_d_sq c hb hq ?_
  have h1 : ⁅x, c.d⁆ * c.d = x * c.d * x⁻¹ := by
    rw [commutatorElement_def]; group
  rw [h1, pow_two]
  have hdd : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c.toCtx5
  calc (x * c.d * x⁻¹) * (x * c.d * x⁻¹) = x * (c.d * c.d) * x⁻¹ := by group
    _ = 1 := by rw [hdd]; group

private theorem beta_mul (c : Ctx7 G L) (hb : B5Std c) {x y : G}
    (hx : x ∈ C4 c.s) (hy : y ∈ C4 c.s) :
    ⁅x * y, c.d⁆ = ⁅x, c.d⁆ * ⁅y, c.d⁆ := by
  have hC4 := y56_C4_cand c.toCtx5 hb.hH
  have hxY : x ∈ e4Y c.s := hC4.2.1 hx
  have hxcent : x ∈ centralizer (c.s.fr.E : Set G) := (Subgroup.mem_inf.mp hxY).2
  have hqy : ⁅y, c.d⁆ ∈ c.s.fr.E := inv_in_E c hb hy
  have hqyq : ⁅y, c.d⁆ * ⁅x, c.d⁆ = ⁅x, c.d⁆ * ⁅y, c.d⁆ :=
    y56_E_comm hb.hH ⁅y, c.d⁆ hqy ⁅x, c.d⁆ (inv_in_E c hb hx)
  have hxq : x * ⁅y, c.d⁆ = ⁅y, c.d⁆ * x :=
    (Subgroup.mem_centralizer_iff.mp hxcent ⁅y, c.d⁆ hqy).symm
  calc ⁅x * y, c.d⁆ = x * ⁅y, c.d⁆ * x⁻¹ * ⁅x, c.d⁆ := by
        rw [commutatorElement_def]; group
    _ = ⁅y, c.d⁆ * ⁅x, c.d⁆ := by rw [hxq]; group
    _ = ⁅x, c.d⁆ * ⁅y, c.d⁆ := hqyq

private def beta (c : Ctx7 G L) (hb : B5Std c) : ↥(C4 c.s) →* G where
  toFun x := ⁅(x : G), c.d⁆
  map_one' := by simp [commutatorElement_def]
  map_mul' x y := beta_mul c hb x.2 y.2

private theorem comm_t_d (c : Ctx7 G L) (hb : B5Std c) : ⁅c.s.t, c.d⁆ = c.s.fr.z := by
  have hdt : c.d * c.s.t * c.d⁻¹ = c.s.fr.z * c.s.t := y5_dtd (c := c.toCtx5) hb.hH
  have htt : c.s.t * c.s.t = 1 := by
    rw [← pow_two, ← c.s.t_order]; exact pow_orderOf_eq_one c.s.t
  have htinv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right htt
  have hzt : c.s.fr.z * c.s.t = c.s.t * c.s.fr.z :=
    y56_t_comm_E c.s c.s.fr.z (y56_z_mem_E hb.hH)
  calc ⁅c.s.t, c.d⁆ = c.s.t * (c.d * c.s.t * c.d⁻¹) := by
        rw [commutatorElement_def, htinv]; group
    _ = c.s.t * (c.s.fr.z * c.s.t) := by rw [hdt]
    _ = c.s.fr.z := by rw [hzt, ← mul_assoc, htt, one_mul]

private theorem beta_ker (c : Ctx7 G L) (hb : B5Std c) :
    (beta c hb).ker = (M4 c.e).subgroupOf (C4 c.s) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  show ⁅(x : G), c.d⁆ = 1 ↔ (x : G) ∈ M4 c.e
  constructor
  · intro hx
    have hC4 := y56_C4_cand c.toCtx5 hb.hH
    have hxY : (x : G) ∈ e4Y c.s := hC4.2.1 x.2
    have hxcent : (x : G) ∈ centralizer (c.s.fr.E : Set G) := (Subgroup.mem_inf.mp hxY).2
    have hxz : c.s.fr.z * (x : G) = (x : G) * c.s.fr.z :=
      Subgroup.mem_centralizer_iff.mp hxcent c.s.fr.z (y56_z_mem_E hb.hH)
    have hxd : (x : G) * c.d = c.d * (x : G) :=
      commutatorElement_eq_one_iff_mul_comm.mp hx
    have hmem : (x : G) ∈ centralizer (V1 c.e : Set G) := by
      rw [c.hV, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro v hv
      rcases hv with hv | hv
      · rw [hv]; exact hxz
      · rw [Set.mem_singleton_iff] at hv; rw [hv]; exact hxd.symm
    exact Subgroup.mem_inf.mpr ⟨x.2, hmem⟩
  · intro hx
    have hxmem : (x : G) ∈ C4 c.s ⊓ centralizer (V1 c.e : Set G) := by
      simpa only [M4, centIn] using hx
    have hxcent : (x : G) ∈ centralizer (V1 c.e : Set G) := hxmem.2
    have hdV1 : c.d ∈ V1 c.e := by
      rw [c.hV]; exact Subgroup.subset_closure (by simp)
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hxcent c.d hdV1).symm

theorem y7b_C4_cent_d_image (c : Ctx7 G L) (hb : B5Std c) :
    ∃ I : Subgroup G, I ≤ c.s.fr.E ∧ c.s.fr.z ∈ I ∧
      (∀ n ∈ normIn L c.s.fr.E, ∀ f ∈ I, n * f * n⁻¹ ∈ I) ∧
      (M4 c.e).relIndex (C4 c.s) = Nat.card ↥I := by
  have hC4 := y56_C4_cand c.toCtx5 hb.hH
  have hrel : (M4 c.e).relIndex (C4 c.s) = Nat.card ↥(beta c hb).range := by
    change ((M4 c.e).subgroupOf (C4 c.s)).index = Nat.card ↥(beta c hb).range
    rw [← beta_ker c hb, Subgroup.index_ker]
  refine ⟨(beta c hb).range, ?_, ?_, ?_, hrel⟩
  · rintro _ ⟨x, rfl⟩
    exact inv_in_E c hb x.2
  · refine ⟨⟨c.s.t, hC4.1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t))⟩, ?_⟩
    exact comm_t_d c hb
  · intro n hn f hf
    obtain ⟨⟨x, hx⟩, rfl⟩ := hf
    have hnd_q : ⁅n, c.d⁆ ∈ e4Q c.s := y56_NE_fix_d c.toCtx5 hb.hH n hn
    have hg : ⁅n, c.d⁆ ∈ c.s.fr.E := by
      refine mem_E_of_mul_d_sq c hb hnd_q ?_
      have h1 : ⁅n, c.d⁆ * c.d = n * c.d * n⁻¹ := by
        rw [commutatorElement_def]; group
      rw [h1, pow_two]
      have hdd : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c.toCtx5
      calc (n * c.d * n⁻¹) * (n * c.d * n⁻¹) = n * (c.d * c.d) * n⁻¹ := by group
        _ = 1 := by rw [hdd]; group
    have hx' : n * x * n⁻¹ ∈ C4 c.s := hC4.2.2.1 n hn x hx
    have hx'Y : n * x * n⁻¹ ∈ e4Y c.s := hC4.2.1 hx'
    have hx'cent : n * x * n⁻¹ ∈ centralizer (c.s.fr.E : Set G) :=
      (Subgroup.mem_inf.mp hx'Y).2
    have hx'g : (n * x * n⁻¹) * ⁅n, c.d⁆ = ⁅n, c.d⁆ * (n * x * n⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hx'cent ⁅n, c.d⁆ hg).symm
    have hq' : ⁅n * x * n⁻¹, c.d⁆ ∈ c.s.fr.E := inv_in_E c hb hx'
    have hgd : ⁅n * x * n⁻¹, ⁅n, c.d⁆ * c.d⁆ = ⁅n * x * n⁻¹, c.d⁆ := by
      have hEcomm : ⁅n, c.d⁆ * ⁅n * x * n⁻¹, c.d⁆ = ⁅n * x * n⁻¹, c.d⁆ * ⁅n, c.d⁆ :=
        y56_E_comm hb.hH ⁅n, c.d⁆ hg ⁅n * x * n⁻¹, c.d⁆ hq'
      have h1 : ⁅n * x * n⁻¹, ⁅n, c.d⁆ * c.d⁆ =
          ⁅n, c.d⁆ * ⁅n * x * n⁻¹, c.d⁆ * (⁅n, c.d⁆)⁻¹ := by
        calc ⁅n * x * n⁻¹, ⁅n, c.d⁆ * c.d⁆ =
              (n * x * n⁻¹) * (⁅n, c.d⁆ * c.d) * (n * x * n⁻¹)⁻¹ * (⁅n, c.d⁆ * c.d)⁻¹ :=
                commutatorElement_def _ _
          _ = (n * x * n⁻¹) * ⁅n, c.d⁆ * c.d * (n * x * n⁻¹)⁻¹ * c.d⁻¹
                * (⁅n, c.d⁆)⁻¹ := by group
          _ = ⁅n, c.d⁆ * (n * x * n⁻¹) * c.d * (n * x * n⁻¹)⁻¹ * c.d⁻¹
                * (⁅n, c.d⁆)⁻¹ := by rw [hx'g]
          _ = ⁅n, c.d⁆ *
                ((n * x * n⁻¹) * c.d * (n * x * n⁻¹)⁻¹ * c.d⁻¹) * (⁅n, c.d⁆)⁻¹ := by group
          _ = ⁅n, c.d⁆ * ⁅n * x * n⁻¹, c.d⁆ * (⁅n, c.d⁆)⁻¹ := by
                rw [← commutatorElement_def]
      rw [h1, hEcomm]; group
    have hnd : n * c.d * n⁻¹ = ⁅n, c.d⁆ * c.d := by
      rw [commutatorElement_def]; group
    refine ⟨⟨n * x * n⁻¹, hx'⟩, ?_⟩
    exact (calc n * ⁅x, c.d⁆ * n⁻¹
        = ⁅n * x * n⁻¹, n * c.d * n⁻¹⁆ := by rw [commutatorElement_def]; group
      _ = ⁅n * x * n⁻¹, ⁅n, c.d⁆ * c.d⁆ := by rw [hnd]
      _ = ⁅n * x * n⁻¹, c.d⁆ := hgd).symm

end CFSG.OddStandard.HigherRank.YamadaG23
