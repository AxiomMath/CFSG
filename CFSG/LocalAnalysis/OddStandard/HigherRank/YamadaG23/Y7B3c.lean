module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BFd
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFR

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7b_F_le_M5 (c : Ctx7 G L) : c.s.fr.F ≤ M5 c.e :=
  le_trans (show c.s.fr.F ≤ M3 c.s from le_sup_right) le_sup_left

private lemma y7b_comm_mul_t_F (c : Ctx7 G L) {f y : G} (hf : f ∈ c.s.fr.F) :
    ⁅y * c.s.t, f⁆ = ⁅y, f⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_one_iff_mul_comm.mpr (y54_t_comm_F c.s f hf).symm]
  group

private lemma y7b_comm_mem_Z (c : Ctx7 G L) (hb : B5Std c) {x f : G}
    (hxS : x ∈ c.s.fr.S) (hfS : f ∈ c.s.fr.S) (hxV1 : ⁅x, f⁆ ∈ V1 c.e) :
    ⁅x, f⁆ ∈ c.s.fr.Z := by
  have hSH : c.s.fr.S ≤ c.s.H := (s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS)
  have hmem : ⁅x, f⁆ ∈ c.s.H ⊓ V1 c.e :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.commutator_le_self c.s.H
        (Subgroup.commutator_mem_commutator (hSH hxS) (hSH hfS)), hxV1⟩
  rwa [y7b_H_inf_V1 c hb] at hmem

theorem y7b_exists_comm_not_mem_V1 (c : Ctx7 G L) (hb : B5Std c) :
    ∃ m ∈ M5 c.e, ⁅m, c.s.t⁆ ∉ V1 c.e := by
  have hZleE : c.s.fr.Z ≤ c.s.fr.E := by
    rw [SFrame.Z]
    exact Subgroup.zpowers_le.mpr (y56_z_mem_E hb.hH)
  have hcardZ : Nat.card ↥(c.s.fr.Z) = 2 := by
    rw [SFrame.Z, Nat.card_zpowers, (lfactsA_of_setting hb.hH.hS hb.hH.hZ c.s).z_order]
  have hnot : ¬ (c.s.fr.E : Set G) ⊆ (c.s.fr.Z : Set G) := by
    intro hsub
    have heq : c.s.fr.E = c.s.fr.Z := le_antisymm hsub hZleE
    rw [← heq, y7b_card_E hb.hH] at hcardZ
    norm_num at hcardZ
  obtain ⟨f, hfE, hfZ⟩ := Set.not_subset.mp hnot
  obtain ⟨m, hmM4, hm⟩ := y7b_phi_M4 c hb f hfE
  refine ⟨m, show m ∈ M5 c.e from Subgroup.mem_sup_right hmM4, ?_⟩
  rw [hm]
  intro hfV1
  apply hfZ
  have hmem : f ∈ c.s.H ⊓ V1 c.e :=
    Subgroup.mem_inf.mpr
      ⟨(s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS)
        (s3_A_le_S c.s (s3_E_le_A c.s hfE)), hfV1⟩
  rwa [y7b_H_inf_V1 c hb] at hmem

theorem y7b_R_cs_le_A (c : Ctx7 G L) (hb : B5Std c) :
    ∀ r ∈ c.s.R, (∀ m ∈ M5 c.e, ⁅m, r⁆ ∈ V1 c.e) → r ∈ c.s.fr.A := by
  intro r hrR hr
  obtain ⟨y, hyS, hy | hy⟩ := s3_R_cases c.s hb.hH.hS hb.hH.h31 r hrR
  ·
    rw [hy]
    refine y7b_CF hb.hH y hyS fun f hf => y7b_comm_mem_Z c hb hyS
      (s3_A_le_S c.s (s3_F_le_A c.s hf)) ?_
    rw [← hy]
    simpa only [commutatorElement_inv] using
      (V1 c.e).inv_mem (hr f (y7b_F_le_M5 c hf))
  ·
    have hyA : y ∈ c.s.fr.A := by
      refine y7b_CF hb.hH y hyS fun f hf => y7b_comm_mem_Z c hb hyS
        (s3_A_le_S c.s (s3_F_le_A c.s hf)) ?_
      rw [← y7b_comm_mul_t_F c hf, ← hy]
      simpa only [commutatorElement_inv] using
        (V1 c.e).inv_mem (hr f (y7b_F_le_M5 c hf))
    exfalso
    obtain ⟨m0, hm0M5, hm0⟩ := y7b_exists_comm_not_mem_V1 c hb
    apply hm0
    have ht_eq : c.s.t = y⁻¹ * r := by rw [hy]; group
    have hyS_inv : y⁻¹ ∈ c.s.fr.S := (c.s.fr.S).inv_mem hyS
    have h2 : y⁻¹ * ⁅m0, r⁆ * y = ⁅m0, r⁆ := by
      rw [hb.h72.1.2.2.2.2 y⁻¹ hyS_inv ⁅m0, r⁆ (hr m0 hm0M5)]
      group
    have h1 : ⁅m0, y⁻¹⁆ ∈ V1 c.e :=
      (y7b_M6_comm_sq c hb).1 m0 (y7b_M5_le_M6 c hb hm0M5) y⁻¹
        (y7b_A_le_M6 c hb ((c.s.fr.A).inv_mem hyA))
    rw [ht_eq, commutatorElement_mul_right_eq_mul_conj]
    simp only [inv_inv]
    rw [show ⁅m0, y⁻¹⁆ * y⁻¹ * ⁅m0, r⁆ * y = ⁅m0, y⁻¹⁆ * (y⁻¹ * ⁅m0, r⁆ * y) by group,
      h2]
    exact (V1 c.e).mul_mem h1 (hr m0 hm0M5)

theorem y7b_R_cV2_le_B (c : Ctx7 G L) (hb : B5Std c) :
    ∀ r ∈ c.s.R, (∀ v ∈ V2 c.e, r * v = v * r) → r ∈ c.s.fr.B := by
  intro r hrR hr
  obtain ⟨y, hyS, hy | hy⟩ := s3_R_cases c.s hb.hH.hS hb.hH.h31 r hrR
  · rw [hy]
    exact y7b_B_cent hb.hH y hyS fun v hv => by
      rw [← hy]
      exact hr v (y7b_V_le_V2 c hb hv)
  · exfalso
    have hdV1 : c.d ∈ V1 c.e := by
      rw [c.hV]; exact Subgroup.subset_closure (by simp)
    have hyd : y * c.d = c.d * y := hb.h72.1.2.2.2.2 y hyS c.d hdV1
    have h1 : (y * c.s.t) * c.d = c.d * (y * c.s.t) := by
      rw [← hy]; exact hr c.d (y7b_V1_le_V2 c hb hdV1)
    have h2 : y * (c.s.t * c.d) = y * (c.d * c.s.t) := by
      calc y * (c.s.t * c.d) = (y * c.s.t) * c.d := by group
        _ = c.d * (y * c.s.t) := h1
        _ = (c.d * y) * c.s.t := by group
        _ = (y * c.d) * c.s.t := by rw [← hyd]
        _ = y * (c.d * c.s.t) := by group
    have htd : c.s.t * c.d = c.d * c.s.t := mul_left_cancel h2
    have h3 : c.d * c.s.t * c.d⁻¹ = c.s.t := by rw [← htd]; group
    have hz1 : c.s.fr.z = 1 := by
      have h4 : c.s.fr.z * c.s.t = c.s.t := by rw [← y5_dtd hb.hH]; exact h3
      exact mul_right_cancel (show c.s.fr.z * c.s.t = 1 * c.s.t by rw [one_mul]; exact h4)
    exact y54_z_ne_one hb.hH hz1

theorem y7b_R5_inf_cs (c : Ctx7 G L) (hb : B5Std c) :
    R5 c.e ⊓ centralizerSection (M5 c.e) (V1 c.e) = AM5 c.e := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR5, hxCS⟩ := Subgroup.mem_inf.mp hx
    simp only [centralizerSection, Set.mem_setOf_eq] at hxCS
    obtain ⟨_, _, hxcomm⟩ := hxCS
    have hxR5' : x ∈ c.s.R ⊔ M5 c.e := hxR5
    obtain ⟨r, hrR, m, hmM5, hxrm⟩ :=
      (mem_sup_iff_exists_mul_of_le_normalizer (y7b_R_le_NM5 c hb)).mp hxR5'
    have hrA : r ∈ c.s.fr.A := by
      refine y7b_R_cs_le_A c hb r hrR fun k hk => ?_
      have hkx : ⁅k, x⁆ ∈ V1 c.e := hxcomm k hk
      have hkm : ⁅k, m⁆ ∈ V1 c.e := (y7b_M5_comm_sq c hb).1 k hk m hmM5
      have hrm : r * ⁅k, m⁆ * r⁻¹ ∈ V1 c.e :=
        (Subgroup.mem_normalizer_iff.mp (y7b_R_le_NV1 c hb hrR) ⁅k, m⁆).mp hkm
      have hdecomp : ⁅k, x⁆ = ⁅k, r⁆ * (r * ⁅k, m⁆ * r⁻¹) := by
        rw [hxrm, commutatorElement_mul_right_eq_mul_conj]
        group
      have heq : ⁅k, r⁆ = ⁅k, x⁆ * (r * ⁅k, m⁆ * r⁻¹)⁻¹ := by
        rw [hdecomp]; group
      rw [heq]
      exact (V1 c.e).mul_mem hkx ((V1 c.e).inv_mem hrm)
    change x ∈ c.s.fr.A ⊔ M5 c.e
    rw [hxrm]
    exact Subgroup.mul_mem_sup hrA hmM5
  · intro x hx
    change x ∈ c.s.fr.A ⊔ M5 c.e at hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · change x ∈ c.s.R ⊔ M5 c.e
      exact sup_le (((s3_A_le_S c.s).trans c.s.S_le_R).trans le_sup_left) le_sup_right hx
    · have hACS : c.s.fr.A ≤ centralizerSection (M5 c.e) (V1 c.e) := by
        intro a ha
        refine ⟨?_, ?_, ?_⟩
        · exact y7b_R_le_NM5 c hb ((s3_A_le_S c.s).trans c.s.S_le_R ha)
        · exact y7b_R_le_NV1 c hb ((s3_A_le_S c.s).trans c.s.S_le_R ha)
        · intro k hk
          exact (y7b_M6_comm_sq c hb).1 k (y7b_M5_le_M6 c hb hk) a (y7b_A_le_M6 c hb ha)
      have hM5CS : M5 c.e ≤ centralizerSection (M5 c.e) (V1 c.e) := by
        intro m hm
        refine ⟨Subgroup.le_normalizer hm, ?_, ?_⟩
        · refine Subgroup.mem_normalizer_fintype fun w hw => ?_
          exact y7b_norm_of_V1_le c hb (N := V1 c.e) le_rfl
            ((y7b_V1_le_M5 c hb).trans (y7b_M5_le_M6 c hb))
            m (y7b_M5_le_M6 c hb hm) w hw
        · intro k hk
          exact (y7b_M5_comm_sq c hb).1 k hk m hm
      exact sup_le hACS hM5CS hx

theorem y7b_R5_inf_cV2 (c : Ctx7 G L) (hb : B6Std c) :
    R5 c.e ⊓ centralizer (V2 c.e : Set G) = BM5 c.e := by
  have hb5 := hb.toB5Std
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR5, hxCent⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_iff] at hxCent
    have hxR5' : x ∈ c.s.R ⊔ M5 c.e := hxR5
    obtain ⟨r, hrR, m, hmM5, hxrm⟩ :=
      (mem_sup_iff_exists_mul_of_le_normalizer (y7b_R_le_NM5 c hb5)).mp hxR5'
    have hrV2 : ∀ v ∈ V2 c.e, r * v = v * r := by
      intro v hv
      have hmv : m * v = v * m := by
        have hvM7 := (Subgroup.mem_inf.mp (hb.h75.2.1.2.2 hv)).2
        exact Subgroup.mem_centralizer_iff.mp hvM7 m (y7b_M5_le_M7 c hb hmM5)
      have h1 : r * (m * v) = (v * r) * m := by
        calc r * (m * v) = (r * m) * v := by group
          _ = x * v := by rw [hxrm]
          _ = v * x := (hxCent v hv).symm
          _ = v * (r * m) := by rw [hxrm]
          _ = (v * r) * m := by group
      have h2 : (r * v) * m = (v * r) * m := by
        calc (r * v) * m = r * (v * m) := by group
          _ = r * (m * v) := congrArg (fun w => r * w) hmv.symm
          _ = (v * r) * m := h1
      exact mul_right_cancel h2
    have hrB : r ∈ c.s.fr.B := y7b_R_cV2_le_B c hb5 r hrR hrV2
    change x ∈ c.s.fr.B ⊔ M5 c.e
    rw [hxrm]
    exact Subgroup.mul_mem_sup hrB hmM5
  · intro x hx
    change x ∈ c.s.fr.B ⊔ M5 c.e at hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · change x ∈ c.s.R ⊔ M5 c.e
      exact sup_le (((s3_B_le_S c.s).trans c.s.S_le_R).trans le_sup_left) le_sup_right hx
    · have hB : c.s.fr.B ≤ centralizer (V2 c.e : Set G) := by
        intro b hbB
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hb5.h72.1.2.1 b hbB v hv).symm
      have hM5 : M5 c.e ≤ centralizer (V2 c.e : Set G) := by
        intro m hm
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hvM7 := (Subgroup.mem_inf.mp (hb.h75.2.1.2.2 hv)).2
        exact (Subgroup.mem_centralizer_iff.mp hvM7 m (y7b_M5_le_M7 c hb hm)).symm
      exact sup_le hB hM5 hx

end CFSG.OddStandard.HigherRank.YamadaG23
