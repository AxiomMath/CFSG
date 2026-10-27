module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7h
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y55

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_g_mul_self (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    c.g * c.g = 1 := by
  rw [← pow_two]
  exact (c.g_spec hRT).2.2.2.1

theorem y7b_g_cent_M3 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∀ m ∈ M3 c.s, c.g * m * c.g⁻¹ = m := by
  intro m hm
  exact hb.fact55 hRT m hm

theorem y7b_g_cent_V2 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∀ v ∈ V2 c.e, c.g * v * c.g⁻¹ = v := by
  intro v hv
  exact y7b_g_cent_M3 c hb hRT v (Subgroup.mem_inf.mp hv).1

theorem y7b_g_comm_NL (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∀ n ∈ normIn L c.s.fr.B, ⁅c.g, n⁆ ∈ c.s.fr.F := by
  intro n hn
  exact y55_g_comm_NL c.toCtx5 hb.hH hRT n (hb.hH.hLF.fact18.2.1.2.1 hn)

theorem y7b_g_comm_M4 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∀ m ∈ M4 c.e, ⁅c.g, m⁆ ∈ M3 c.s := by
  intro m hm
  exact hb.h72.2.2.2 hRT m (y7b_M4_le_M6 c hb hm)

theorem y7b_g_mem_X0 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    c.g ∈ y7bX0 c.s := by
  have hg1 : c.g * c.g = 1 := y7b_g_mul_self c hb hRT
  have hginv : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right hg1
  have hcent : ∀ m ∈ M3 c.s, c.g * m * c.g⁻¹ = m := y7b_g_cent_M3 c hb hRT
  have hgcommNL : ∀ n ∈ normIn L c.s.fr.B, ⁅c.g, n⁆ ∈ c.s.fr.F := y7b_g_comm_NL c hb hRT
  have hgt : c.g * c.s.t = c.s.t * c.g := s3_comm_t_of_mem_T c.s (c.g_spec hRT).1
  have hFleM3 : c.s.fr.F ≤ M3 c.s := fun _ hx => Subgroup.mem_sup_right hx
  have hforward : ∀ b ∈ c.s.fr.B, c.g * b * c.g⁻¹ ∈ c.s.fr.B := by
    intro b hbB
    have hbN : b ∈ normIn L c.s.fr.B :=
      Subgroup.mem_inf.mpr ⟨f3_B_le_L c.s hbB, (Subgroup.le_normalizer (H := c.s.fr.B)) hbB⟩
    have hcomm : ⁅c.g, b⁆ ∈ c.s.fr.F := hgcommNL b hbN
    rw [show c.g * b * c.g⁻¹ = ⁅c.g, b⁆ * b by rw [commutatorElement_def]; group]
    exact (c.s.fr.B).mul_mem (y54_F_le_B hb.hH hcomm) hbB
  have hgNB : c.g ∈ normalizer (c.s.fr.B : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr (fun b => ⟨hforward b, ?_⟩)
    intro hb
    have h2 := hforward (c.g * b * c.g⁻¹) hb
    have heq : c.g * (c.g * b * c.g⁻¹) * c.g⁻¹ = b := by
      rw [hginv]
      calc c.g * (c.g * b * c.g) * c.g = (c.g * c.g) * b * (c.g * c.g) := by group
        _ = b := by rw [hg1]; group
    rwa [heq] at h2
  have hgNM3 : c.g ∈ normalizer (M3 c.s : Set G) := by
    have hgc : c.g ∈ Subgroup.centralizer (M3 c.s : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h := hcent m hm
      calc m * c.g = (c.g * m * c.g⁻¹) * c.g := by rw [h]
        _ = c.g * m := by group
    exact Subgroup.centralizer_le_normalizer (M3 c.s : Set G) hgc
  have hgNzt : c.g ∈ normalizer (zpowers c.s.t : Set G) :=
    mem_normalizer_zpowers (by rw [hgt]; group)
  have hgNC3 : c.g ∈ normalizer (C3 c.s : Set G) := by
    rw [y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact mem_normalizer_sup hgNM3 hgNzt
  have hgNW : c.g ∈ normalizer (y7bW c.s : Set G) := by
    rw [y7bW]
    exact mem_normalizer_sup hgNB hgNC3
  have hBM : ∀ u ∈ y7bBM c.s, ⁅u, c.g⁆ ∈ M3 c.s := by
    intro u hu
    obtain ⟨b, hbB, m, hm, rfl⟩ := (y7b_mem_BM c hb).mp hu
    have hbg : ⁅b, c.g⁆ ∈ c.s.fr.F := by
      have hbN : b ∈ normIn L c.s.fr.B :=
        Subgroup.mem_inf.mpr ⟨f3_B_le_L c.s hbB, (Subgroup.le_normalizer (H := c.s.fr.B)) hbB⟩
      have h := hgcommNL b hbN
      have h' : ⁅b, c.g⁆ = (⁅c.g, b⁆)⁻¹ := by rw [commutatorElement_inv]
      rw [h']
      exact (c.s.fr.F).inv_mem h
    have hmg : ⁅m, c.g⁆ = 1 := by
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      have h := hcent m hm
      calc m * c.g = (c.g * m * c.g⁻¹) * c.g := by rw [h]
        _ = c.g * m := by group
    rw [commutatorElement_mul_left_eq_conj_mul, hmg]
    simpa using hFleM3 hbg
  have htcom : ⁅c.s.t, c.g⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hgt.symm
  refine ⟨hgNW, hgNM3, ?_⟩
  intro k hk
  obtain ⟨u, hu, hk⟩ := (y7b_mem_W c hb).mp hk
  rcases hk with hk | hk
  · rw [hk]
    exact hBM u hu
  · rw [hk, commutatorElement_mul_left_eq_conj_mul, htcom]
    simpa using hBM u hu

theorem y7b_X0_cases_g (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∀ a ∈ y7bX0 c.s, a ∈ y7bW c.s ∨ c.g * a ∈ y7bW c.s := by
  have hf3P_le_W : f3P c.s ≤ y7bW c.s := by
    rw [f3P, y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hM3_le_W : M3 c.s ≤ y7bW c.s := by
    rw [y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact le_sup_left.trans le_sup_right
  intro a ha
  obtain ⟨n, hn, m, hm, rfl⟩ := y7b_X0_decomp c hb a ha
  rcases y7b_f3X0_cases_g c.toCtx5 hb.hH hRT n hn with hnP | hgnP
  · left
    exact (y7bW c.s).mul_mem (hf3P_le_W hnP) (hM3_le_W hm)
  · right
    rw [show c.g * (n * m) = (c.g * n) * m by group]
    exact (y7bW c.s).mul_mem (hf3P_le_W hgnP) (hM3_le_W hm)

theorem y7b_X0_eq_W_of_R_eq_T (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R = c.s.T) :
    y7bX0 c.s = y7bW c.s := by
  have hf3P_le_W : f3P c.s ≤ y7bW c.s := by
    rw [f3P, y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hM3_le_W : M3 c.s ≤ y7bW c.s := by
    rw [y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact le_sup_left.trans le_sup_right
  refine le_antisymm ?_ (y7b_W_le_X0 c hb)
  intro a ha
  obtain ⟨n, hn, m, hm, rfl⟩ := y7b_X0_decomp c hb a ha
  rw [y7b_f3X0_eq_P hb.hH hRT] at hn
  exact (y7bW c.s).mul_mem (hf3P_le_W hn) (hM3_le_W hm)

theorem y7b_V2_eq_cen_M2 (c : Ctx7 G L) (hb : B5Std c) :
    V2 c.e = M2 c.s ⊓ centralizer (M2 c.s : Set G) := by
  have hB_le : c.s.fr.B ≤ Subgroup.centralizer (V2 c.e : Set G) := by
    intro b hbB
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hb.h72.1.2.1 b hbB v hv).symm
  have hV2_le : V2 c.e ≤ Subgroup.centralizer (V2 c.e : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨hcomm, -⟩ := y7b_V2_elem c hb
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  have hBN : c.s.fr.B ≤ normalizer (V2 c.e : Set G) :=
    hB_le.trans (Subgroup.centralizer_le_normalizer (V2 c.e : Set G))
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · rw [hb.h72.1.1]
      exact le_sup_right
    · exact (Subgroup.le_centralizer_iff).mpr
        (by rw [hb.h72.1.1]; exact sup_le hB_le hV2_le)
  · intro x hx
    obtain ⟨hxM2, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [hb.h72.1.1] at hxM2
    obtain ⟨b, hbB, v, hv, rfl⟩ :=
      (mem_sup_iff_exists_mul_of_le_normalizer (H := c.s.fr.B) (K := V2 c.e) hBN).mp hxM2
    have hb_comm_B : b ∈ Subgroup.centralizer (c.s.fr.B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'B
      have h1 : b' * (b * v) = (b * v) * b' :=
        (Subgroup.mem_centralizer_iff.mp hxC) b'
          (by rw [hb.h72.1.1]; exact Subgroup.mem_sup_left hb'B)
      have h2 : b' * v = v * b' := hb.h72.1.2.1 b' hb'B v hv
      calc b' * b = b' * (b * v) * v⁻¹ := by group
        _ = (b * v) * b' * v⁻¹ := by rw [h1]
        _ = b * (v * b') * v⁻¹ := by group
        _ = b * (b' * v) * v⁻¹ := by rw [← h2]
        _ = b * b' := by group
    exact (V2 c.e).mul_mem (y7b_V_le_V2 c hb (Subgroup.mem_inf.mpr ⟨hbB, hb_comm_B⟩)) hv

theorem y7b_NH_le_NV2 (c : Ctx7 G L) (hb : B5Std c) :
    normIn c.s.H c.s.fr.B ≤ normalizer (V2 c.e : Set G) := by
  intro n hn
  have hnM2 : n ∈ normalizer (M2 c.s : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr (fun m => ⟨?_, ?_⟩)
    · intro hm
      exact y54_M2_inv hb.hH n hn m hm
    · intro hm
      have h := y54_M2_inv hb.hH n⁻¹ ((normIn c.s.H c.s.fr.B).inv_mem hn)
        (n * m * n⁻¹) hm
      rwa [show n⁻¹ * (n * m * n⁻¹) * (n⁻¹)⁻¹ = m by group] at h
  rw [y7b_V2_eq_cen_M2 c hb]
  exact mem_normalizer_inf hnM2 (mem_normalizer_centralizer hnM2)

end CFSG.OddStandard.HigherRank.YamadaG23
