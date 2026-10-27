module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7f
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs7

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_BM_comm_mem (c : Ctx7 G L) (hb : B5Std c) :
    ∀ u ∈ y7bBM c.s, ∀ v ∈ y7bBM c.s, ⁅u, v⁆ ∈ M3 c.s := by
  refine y7b_comm_mem_of_sq_mem (le_sup_right : M3 c.s ≤ y7bBM c.s) ?_
    (y7b_BM_sq_mem_M3 c hb)
  intro v hv n hn
  have hv' : v ∈ normalizer (M3 c.s : Set G) := y7b_W_le_NM3 c hb (y7b_BM_le_W c hb hv)
  exact (Subgroup.mem_normalizer_iff.mp hv' n).mp hn

theorem y7b_normIn_norm_BM (c : Ctx7 G L) (hb : B5Std c) {n : G}
    (hn : n ∈ normIn c.s.H c.s.fr.B) :
    n ∈ normalizer (y7bBM c.s : Set G) ∧ n ∈ normalizer (M3 c.s : Set G) := by
  have hn' : n ∈ c.s.H ⊓ normalizer (c.s.fr.B : Set G) := by simpa only [normIn] using hn
  obtain ⟨-, hnB⟩ := Subgroup.mem_inf.mp hn'
  exact ⟨mem_normalizer_sup hnB (y7b_N_le_NM3 c hb hn), y7b_N_le_NM3 c hb hn⟩

theorem y7b_S_le_normIn (c : Ctx7 G L) (hb : B5Std c) : c.s.fr.S ≤ normIn c.s.H c.s.fr.B := by
  intro x hx
  show x ∈ c.s.H ⊓ normalizer (c.s.fr.B : Set G)
  exact ⟨s3_L_le_H c.s hb.hH.hS (s3_S_le_L c.s hx), y7b_S_le_normalizer_B hb.hH hx⟩

theorem y7b_B_le_K (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.B ≤ centralizerSection (y7bBM c.s) (M3 c.s) := by
  intro b hbB
  have hbS : b ∈ c.s.fr.S := s3_B_le_S c.s hbB
  have hbN : b ∈ normIn c.s.H c.s.fr.B := y7b_S_le_normIn c hb hbS
  obtain ⟨hbK, hbM3⟩ := y7b_normIn_norm_BM c hb hbN
  have hbBM : b ∈ y7bBM c.s := Subgroup.mem_sup_left hbB
  exact ⟨hbK, hbM3, fun u hu => y7b_BM_comm_mem c hb u hu b hbBM⟩

theorem y7b_S_le_K_of_A (c : Ctx7 G L) (hb : B5Std c)
    (hA : c.s.fr.A ≤ centralizerSection (y7bBM c.s) (M3 c.s)) :
    c.s.fr.S ≤ centralizerSection (y7bBM c.s) (M3 c.s) := by
  intro x hx
  obtain ⟨a, ha, b, hbB, rfl⟩ := (y7b_mem_S hb.hH).mp hx
  exact mul_mem (hA ha) (y7b_B_le_K c hb hbB)

end CFSG.OddStandard.HigherRank.YamadaG23
