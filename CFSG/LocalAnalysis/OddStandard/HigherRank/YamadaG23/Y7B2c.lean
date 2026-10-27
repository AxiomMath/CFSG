module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B0Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsE
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Sq

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {s : Setting3 G L} {e : Setting3.Ext s}

theorem y7b_T_le_NHA (hH : F33Hyp s e) : s.T ≤ normIn s.H s.fr.A := by
  intro x hx
  refine ⟨s.sylow_T.1 hx, ?_⟩
  have hx1 : x ∈ e.T₁ := e.T_le hx
  have hx2 : x⁻¹ ∈ e.T₁ := inv_mem hx1
  show x ∈ normalizer (s.fr.A : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact s3_conj_A s e hH.h32 hx1 ha
  · intro ha
    have := s3_conj_A s e hH.h32 hx2 ha
    simpa [mul_assoc] using this

theorem y7b_R_le_NHA (hH : F33Hyp s e) : s.R ≤ normIn s.H s.fr.A :=
  s.R_le_T.trans (y7b_T_le_NHA hH)

theorem y7b_R_le_NHE (hH : F33Hyp s e) : s.R ≤ normIn s.H s.fr.E := by
  rw [y5_R_eq hH]
  apply sup_le
  · intro x hx
    exact y56_NL_le_N hH (y56_S_le_NE hH hx)
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.centralizer_le_normalizer (s.fr.E : Set G) fun f hf => y56_t_comm_E s f hf

theorem y7b_NHA_le_NV1 (c : Ctx7 G L) (hb : B5Std c) :
    normIn c.s.H c.s.fr.A ≤ normalizer (V1 c.e : Set G) := by
  intro x hx
  have hxN : x ∈ normalizer (C0 c.e : Set G) := by
    rw [hb.h71.1.1]
    exact Subgroup.mem_sup_left hx
  exact hb.h71.1.2 hxN

theorem y7b_NHA_le_NM6 (c : Ctx7 G L) (hb : B5Std c) :
    normIn c.s.H c.s.fr.A ≤ normalizer (M6 c.e : Set G) := by
  intro x hx
  have hC6 : x ∈ normalizer (C6 c.e : Set G) := by
    rw [hb.h73]
    exact Subgroup.mem_sup_left hx
  have hV1 : x ∈ normalizer (V1 c.e : Set G) := y7b_NHA_le_NV1 c hb hx
  show x ∈ normalizer ((C6 c.e ⊓ Subgroup.centralizer (V1 c.e : Set G) : Subgroup G) : Set G)
  exact mem_normalizer_inf hC6 (mem_normalizer_centralizer hV1)

theorem y7b_R_le_NV1 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.R ≤ normalizer (V1 c.e : Set G) :=
  (y7b_R_le_NHA hb.hH).trans (y7b_NHA_le_NV1 c hb)

theorem y7b_R_le_NM6 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.R ≤ normalizer (M6 c.e : Set G) :=
  (y7b_R_le_NHA hb.hH).trans (y7b_NHA_le_NM6 c hb)

theorem y7b_R_le_NC4 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.R ≤ normalizer (C4 c.s : Set G) := by
  intro r hr
  have hrN : r ∈ e4N c.s := y7b_R_le_NHE hb.hH hr
  have hY : r ∈ normalizer (e4Y c.s : Set G) :=
    Subgroup.mem_normalizer_fintype fun y hy => y56_N_norm_Y hb.hH r hrN y hy
  have hN : r ∈ normalizer (e4N c.s : Set G) := Subgroup.le_normalizer hrN
  have hQ : r ∈ normalizer (e4Q c.s : Set G) :=
    Subgroup.mem_normalizer_fintype fun q hq => y56_N_norm_Q hb.hH r hrN q hq
  have hsup : r ∈ normalizer ((⁅e4Y c.s, e4N c.s⁆ ⊔ e4Q c.s : Subgroup G) : Set G) :=
    mem_normalizer_sup (mem_normalizer_commutator hY hN) hQ
  rw [y56_C4_eq c.toCtx5 hb.hH]
  exact hsup

theorem y7b_R_le_NM4 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.R ≤ normalizer (M4 c.e : Set G) := by
  intro r hr
  have hC4 : r ∈ normalizer (C4 c.s : Set G) := y7b_R_le_NC4 c hb hr
  have hV1 : r ∈ normalizer (V1 c.e : Set G) := y7b_R_le_NV1 c hb hr
  show r ∈ normalizer ((C4 c.s ⊓ Subgroup.centralizer (V1 c.e : Set G) : Subgroup G) : Set G)
  exact mem_normalizer_inf hC4 (mem_normalizer_centralizer hV1)

theorem y7b_R_le_NV2 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.R ≤ normalizer (V2 c.e : Set G) := by
  intro r hr
  have hM3 : r ∈ normalizer (M3 c.s : Set G) :=
    Subgroup.mem_normalizer_fintype fun m hm => y54_R_norm_M3 c.toCtx5 hb.hH r hr m hm
  have hM4 : r ∈ normalizer (M4 c.e : Set G) := y7b_R_le_NM4 c hb hr
  show r ∈ normalizer ((M3 c.s ⊓ M4 c.e : Subgroup G) : Set G)
  exact mem_normalizer_inf hM3 hM4

theorem y7b_R_le_NM5 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.R ≤ normalizer (M5 c.e : Set G) := by
  intro r hr
  have hM3 : r ∈ normalizer (M3 c.s : Set G) :=
    Subgroup.mem_normalizer_fintype fun m hm => y54_R_norm_M3 c.toCtx5 hb.hH r hr m hm
  have hM4 : r ∈ normalizer (M4 c.e : Set G) := y7b_R_le_NM4 c hb hr
  show r ∈ normalizer ((M3 c.s ⊔ M4 c.e : Subgroup G) : Set G)
  exact mem_normalizer_sup hM3 hM4

end CFSG.OddStandard.HigherRank.YamadaG23
