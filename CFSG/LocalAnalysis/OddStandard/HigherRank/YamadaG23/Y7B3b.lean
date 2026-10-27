module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {s : Setting3 G L} {e : Setting3.Ext s}

private theorem secProp_isElemAbelian_comm_sq {V N : Subgroup G}
    (h : SecProp V N (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y))) :
    (∀ m ∈ V, ∀ n ∈ V, ⁅m, n⁆ ∈ N) ∧ ∀ m ∈ V, m ^ 2 ∈ N := by
  obtain ⟨hN, hel⟩ := h
  let N' : Subgroup ↥V := N.subgroupOf V
  haveI : N'.Normal := hN
  have hcommQ : IsMulCommutative (↥V ⧸ N') := by
    apply IsMulCommutative.of_comm
    intro g h'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N' g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N' h'
    simpa using Subtype.ext_iff.mp (hel.1.is_comm.comm
      (⟨QuotientGroup.mk' N' x, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (↥V ⧸ N')))
      (⟨QuotientGroup.mk' N' y, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (↥V ⧸ N'))))
  have hcommle : _root_.commutator ↥V ≤ N' :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (G := ↥V) (N := N')).mp hcommQ
  refine ⟨?_, ?_⟩
  · intro m hm n hn
    have hmem : ⁅(⟨m, hm⟩ : ↥V), (⟨n, hn⟩ : ↥V)⁆ ∈ N' :=
      hcommle (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have hcoe : ((⁅(⟨m, hm⟩ : ↥V), (⟨n, hn⟩ : ↥V)⁆ : ↥V) : G) = ⁅m, n⁆ :=
      map_commutatorElement (f := V.subtype) _ _
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa [hcoe] using hmem
  · intro m hm
    have hsq : (QuotientGroup.mk' N' (⟨m, hm⟩ : ↥V)) ^ 2 = 1 := by
      simpa using hel.2 (⟨QuotientGroup.mk' N' (⟨m, hm⟩ : ↥V), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (↥V ⧸ N'))) (Subgroup.mem_top _)
    have hmem : (⟨m, hm⟩ : ↥V) ^ 2 ∈ N' := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change QuotientGroup.mk' N' ((⟨m, hm⟩ : ↥V) ^ 2) = 1
      rw [map_pow]
      exact hsq
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem

theorem y7b_M7_comm_sq (c : Ctx7 G L) (hb : B6Std c) :
    (∀ m ∈ M7 c.s, ∀ n ∈ M7 c.s, ⁅m, n⁆ ∈ M3 c.s) ∧ ∀ m ∈ M7 c.s, m ^ 2 ∈ M3 c.s :=
  secProp_isElemAbelian_comm_sq hb.h75.2.2.1

theorem y7b_M7_le_NM5 (c : Ctx7 G L) (hb : B6Std c) :
    M7 c.s ≤ normalizer (M5 c.e : Set G) := by
  intro m hm
  refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
  have hxM7 : x ∈ M7 c.s := y7b_M5_le_M7 c hb hx
  have hc : ⁅m, x⁆ ∈ M3 c.s := (y7b_M7_comm_sq c hb).1 m hm x hxM7
  have hM3M5 : M3 c.s ≤ M5 c.e := le_sup_left
  have he : m * x * m⁻¹ = ⁅m, x⁆ * x := by rw [commutatorElement_def]; group
  rw [he]
  exact (M5 c.e).mul_mem (hM3M5 hc) hx

theorem y7b_M7_le_NV2 (c : Ctx7 G L) (hb : B6Std c) :
    M7 c.s ≤ normalizer (V2 c.e : Set G) := by
  intro m hm
  refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
  have hvc : v ∈ cen (M7 c.s) := hb.h75.2.1.2.2 hv
  have hcomm : m * v = v * m :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hvc).2 m hm
  have he : m * v * m⁻¹ = v := by rw [hcomm]; group
  rw [he]
  exact hv

theorem y7b_M7_le_NV1 (c : Ctx7 G L) (hb : B6Std c) :
    M7 c.s ≤ normalizer (V1 c.e : Set G) := by
  intro m hm
  refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
  have hvV2 : v ∈ V2 c.e := y7b_V1_le_V2 c hb.toB5Std hv
  have hvc : v ∈ cen (M7 c.s) := hb.h75.2.1.2.2 hvV2
  have hcomm : m * v = v * m :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hvc).2 m hm
  have he : m * v * m⁻¹ = v := by rw [hcomm]; group
  rw [he]
  exact hv

theorem y7b_S_eq_sup (hH : F33Hyp s e) : s.fr.S = s.fr.A ⊔ s.fr.B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb', rfl⟩ := (y7b_mem_S hH).mp hx
    exact Subgroup.mul_mem_sup ha hb'
  · exact sup_le (s3_A_le_S s) (s3_B_le_S s)

theorem y7b_SM5_eq (c : Ctx7 G L) (hb : B5Std c) : SM5 c.e = AM5 c.e ⊔ BM5 c.e := by
  unfold SM5 AM5 BM5
  rw [y7b_S_eq_sup hb.hH]
  ac_rfl

theorem y7b_H_inf_AM5 (c : Ctx7 G L) (hb : B5Std c) : c.s.H ⊓ AM5 c.e = c.s.fr.A := by
  refine le_antisymm ?_ ?_
  · calc c.s.H ⊓ AM5 c.e ≤ c.s.H ⊓ M6 c.e :=
        inf_le_inf le_rfl (sup_le (y7b_A_le_M6 c hb) (y7b_M5_le_M6 c hb))
      _ = c.s.fr.A := hb.h71.2.1.2.1
  · exact le_inf ((s3_A_le_S c.s).trans
      ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))) le_sup_left

theorem y7b_H_inf_BM5 (c : Ctx7 G L) (hb : B6Std c) : c.s.H ⊓ BM5 c.e = c.s.fr.B := by
  refine le_antisymm ?_ ?_
  · calc c.s.H ⊓ BM5 c.e ≤ c.s.H ⊓ M7 c.s :=
        inf_le_inf le_rfl (sup_le (y7b_B_le_M7 c hb) (y7b_M5_le_M7 c hb))
      _ = c.s.fr.B := hb.h75.1.2.1
  · exact le_inf ((s3_B_le_S c.s).trans
      ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))) le_sup_left

theorem y7b_H_inf_SM5 (c : Ctx7 G L) (hb : B6Std c) : c.s.H ⊓ SM5 c.e = c.s.fr.S := by
  have hb5 := hb.toB5Std
  have hSH : c.s.fr.S ≤ c.s.H := (s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxH, hxSM5⟩ := Subgroup.mem_inf.mp hx
    have hSN : c.s.fr.S ≤ normalizer (M5 c.e : Set G) :=
      c.s.S_le_R.trans (y7b_R_le_NM5 c hb5)
    have hxSM5' : x ∈ c.s.fr.S ⊔ M5 c.e := hxSM5
    obtain ⟨s0, hs0, m, hm, hxsm⟩ :=
      (mem_sup_iff_exists_mul_of_le_normalizer hSN).mp hxSM5'
    have hmH : m ∈ c.s.H := by
      have h1 : s0⁻¹ * (s0 * m) ∈ c.s.H :=
        c.s.H.mul_mem (c.s.H.inv_mem (hSH hs0)) (hxsm ▸ hxH)
      rwa [inv_mul_cancel_left] at h1
    have hmM5 : m ∈ c.s.H ⊓ M5 c.e := Subgroup.mem_inf.mpr ⟨hmH, hm⟩
    rw [y7b_H_inf_M5 c hb] at hmM5
    rw [hxsm]
    exact c.s.fr.S.mul_mem hs0 ((inf_le_left.trans (s3_A_le_S c.s)) hmM5)
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨hSH hx, Subgroup.mem_sup_left hx⟩

theorem y7b_AM5_inf_BM5 (c : Ctx7 G L) (hb : B6Std c) : AM5 c.e ⊓ BM5 c.e = M5 c.e := by
  have hb5 := hb.toB5Std
  have hA : ∀ a ∈ c.s.fr.A, ∀ m ∈ M5 c.e, a * m * a⁻¹ ∈ M5 c.e := by
    intro a ha m hm
    have haR : a ∈ c.s.R := (s3_A_le_S c.s).trans c.s.S_le_R ha
    exact (Subgroup.mem_normalizer_iff.mp (y7b_R_le_NM5 c hb5 haR) m).mp hm
  have hB : ∀ b ∈ c.s.fr.B, ∀ m ∈ M5 c.e, b * m * b⁻¹ ∈ M5 c.e := by
    intro b hbB m hm
    have hbR : b ∈ c.s.R := (s3_B_le_S c.s).trans c.s.S_le_R hbB
    exact (Subgroup.mem_normalizer_iff.mp (y7b_R_le_NM5 c hb5 hbR) m).mp hm
  have hAM : ∀ a ∈ c.s.fr.A, a ∈ c.s.fr.B ⊔ M5 c.e → a ∈ M5 c.e := by
    intro a ha haBM5
    have haH : a ∈ c.s.H :=
      (s3_A_le_S c.s).trans ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS)) ha
    have haB : a ∈ c.s.fr.B := by
      have h1 : a ∈ c.s.H ⊓ BM5 c.e :=
        Subgroup.mem_inf.mpr ⟨haH, show a ∈ BM5 c.e from haBM5⟩
      rwa [y7b_H_inf_BM5 c hb] at h1
    exact y7b_EF_le_M5 c hb5 (Subgroup.mem_inf.mpr ⟨ha, haB⟩)
  have hmain := inf_sup_sup_eq_of_normalizes (A := c.s.fr.A) (B := c.s.fr.B) (M := M5 c.e)
    hA hB hAM
  simpa [AM5, BM5] using hmain

theorem y7b_R5_inf_M6 (c : Ctx7 G L) (hb : B5Std c) : R5 c.e ⊓ M6 c.e = AM5 c.e := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxR5, hxM6⟩ := Subgroup.mem_inf.mp hx
    have hxR5' : x ∈ c.s.R ⊔ M5 c.e := hxR5
    obtain ⟨r, hrR, m, hmM5, rfl⟩ :=
      (mem_sup_iff_exists_mul_of_le_normalizer (y7b_R_le_NM5 c hb)).mp hxR5'
    have hmM6 : m ∈ M6 c.e := y7b_M5_le_M6 c hb hmM5
    have hrM6 : r ∈ M6 c.e := by
      have h1 : (r * m) * m⁻¹ ∈ M6 c.e := (M6 c.e).mul_mem hxM6 ((M6 c.e).inv_mem hmM6)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h1
    have hrA : r ∈ c.s.fr.A := by
      have h1 : r ∈ c.s.H ⊓ M6 c.e :=
        Subgroup.mem_inf.mpr ⟨c.s.R_le_T.trans c.s.sylow_T.1 hrR, hrM6⟩
      rwa [hb.h71.2.1.2.1] at h1
    change r * m ∈ c.s.fr.A ⊔ M5 c.e
    exact Subgroup.mul_mem_sup hrA hmM5
  · intro x hx
    change x ∈ c.s.fr.A ⊔ M5 c.e at hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · change x ∈ c.s.R ⊔ M5 c.e
      exact sup_le (((s3_A_le_S c.s).trans c.s.S_le_R).trans le_sup_left) le_sup_right hx
    · exact sup_le (y7b_A_le_M6 c hb) (y7b_M5_le_M6 c hb) hx

theorem y7b_R5_inf_M7 (c : Ctx7 G L) (hb : B6Std c) : R5 c.e ⊓ M7 c.s = BM5 c.e := by
  have hb5 := hb.toB5Std
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxR5, hxM7⟩ := Subgroup.mem_inf.mp hx
    have hxR5' : x ∈ c.s.R ⊔ M5 c.e := hxR5
    obtain ⟨r, hrR, m, hmM5, rfl⟩ :=
      (mem_sup_iff_exists_mul_of_le_normalizer (y7b_R_le_NM5 c hb5)).mp hxR5'
    have hmM7 : m ∈ M7 c.s := y7b_M5_le_M7 c hb hmM5
    have hrM7 : r ∈ M7 c.s := by
      have h1 : (r * m) * m⁻¹ ∈ M7 c.s := (M7 c.s).mul_mem hxM7 ((M7 c.s).inv_mem hmM7)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h1
    have hrB : r ∈ c.s.fr.B := by
      have h1 : r ∈ c.s.H ⊓ M7 c.s :=
        Subgroup.mem_inf.mpr ⟨c.s.R_le_T.trans c.s.sylow_T.1 hrR, hrM7⟩
      rwa [hb.h75.1.2.1] at h1
    change r * m ∈ c.s.fr.B ⊔ M5 c.e
    exact Subgroup.mul_mem_sup hrB hmM5
  · intro x hx
    change x ∈ c.s.fr.B ⊔ M5 c.e at hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · change x ∈ c.s.R ⊔ M5 c.e
      exact sup_le (((s3_B_le_S c.s).trans c.s.S_le_R).trans le_sup_left) le_sup_right hx
    · exact sup_le (y7b_B_le_M7 c hb) (y7b_M5_le_M7 c hb) hx

end CFSG.OddStandard.HigherRank.YamadaG23
