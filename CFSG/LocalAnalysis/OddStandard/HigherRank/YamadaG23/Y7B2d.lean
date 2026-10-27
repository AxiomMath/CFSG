module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsE
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {s : Setting3 G L} {e : Setting3.Ext s}

theorem y7b_R_le_NC3 (hH : F33Hyp s e) : s.R ≤ normalizer (C3 s : Set G) := by
  intro r hr
  have hrT : r ∈ s.T := s.R_le_T hr
  have hrH : r ∈ s.H := s.sylow_T.1 hrT
  have hrt : r * s.t * r⁻¹ = s.t :=
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hrH)
  have hrF : r ∈ normalizer (s.fr.F : Set G) := by
    have h : r ∈ normIn s.H s.fr.F := y54_R_le_N hH hr
    rw [normIn] at h
    exact (Subgroup.mem_inf.mp h).2
  have hFt : r ∈ normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G) :=
    mem_normalizer_sup hrF (mem_normalizer_zpowers hrt)
  have hcent : r ∈ normalizer
      ((centIn (normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G))
        s.fr.F : Subgroup G) : Set G) := by
    rw [centIn]
    exact mem_normalizer_inf (mem_normalizer_normalizer hFt) (mem_normalizer_centralizer hrF)
  have hHF : r ∈ normalizer ((normIn s.H s.fr.F : Subgroup G) : Set G) := by
    rw [normIn]
    exact mem_normalizer_inf (Subgroup.le_normalizer hrH) (mem_normalizer_normalizer hrF)
  have hpc : r ∈ normalizer ((pCoreOf 2
      ⁅centIn (normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G)) s.fr.F,
        normIn s.H s.fr.F⁆ : Subgroup G) : Set G) :=
    mem_normalizer_pCoreOf (mem_normalizer_commutator hcent hHF)
  rw [C3]
  exact mem_normalizer_sup hpc hFt

theorem y7b_R_le_NM3 (hH : F33Hyp s e) : s.R ≤ normalizer (M3 s : Set G) := by
  intro r hr
  have hrT : r ∈ s.T := s.R_le_T hr
  have hrF : r ∈ normalizer (s.fr.F : Set G) := by
    have h : r ∈ normIn s.H s.fr.F := y54_R_le_N hH hr
    rw [normIn] at h
    exact (Subgroup.mem_inf.mp h).2
  have hrC3 : r ∈ normalizer (C3 s : Set G) := y7b_R_le_NC3 hH hr
  have hrL : r ∈ normalizer (L : Set G) := s3_T_le_N s hH.hS hrT
  have hrNF : r ∈ normalizer ((normIn L s.fr.F : Subgroup G) : Set G) := by
    rw [normIn]
    exact mem_normalizer_inf hrL (mem_normalizer_normalizer hrF)
  have hcomm : r ∈ normalizer ((⁅C3 s, normIn L s.fr.F⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator hrC3 hrNF
  rw [M3]
  exact mem_normalizer_sup hcomm hrF

theorem y7b_R_le_NX7 (hH : F33Hyp s e) : s.R ≤ normalizer (X7 s : Set G) := by
  intro r hr
  have hrB : r ∈ normalizer (s.fr.B : Set G) := by
    have h : r ∈ normIn s.H s.fr.B := y54_R_le_NB hH hr
    rw [normIn] at h
    exact (Subgroup.mem_inf.mp h).2
  have hrC3 : r ∈ normalizer (C3 s : Set G) := y7b_R_le_NC3 hH hr
  have hrM3 : r ∈ normalizer (M3 s : Set G) := y7b_R_le_NM3 hH hr
  have hBC3 : r ∈ normalizer ((s.fr.B ⊔ C3 s : Subgroup G) : Set G) :=
    mem_normalizer_sup hrB hrC3
  have hBM3 : r ∈ normalizer ((s.fr.B ⊔ M3 s : Subgroup G) : Set G) :=
    mem_normalizer_sup hrB hrM3
  rw [X7]
  exact mem_normalizer_inf
    (mem_normalizer_inf (mem_normalizer_normalizer hBC3) (mem_normalizer_normalizer hrM3))
    (mem_normalizer_centralizerSection hBM3 hrM3)

theorem y7b_R_le_NC7 (hH : F33Hyp s e) : s.R ≤ normalizer (C7 s : Set G) := by
  intro r hr
  have hrH : r ∈ s.H := s.sylow_T.1 (s.R_le_T hr)
  have hrB : r ∈ normalizer (s.fr.B : Set G) := by
    have h : r ∈ normIn s.H s.fr.B := y54_R_le_NB hH hr
    rw [normIn] at h
    exact (Subgroup.mem_inf.mp h).2
  have hrX7 : r ∈ normalizer (X7 s : Set G) := y7b_R_le_NX7 hH hr
  have hrC3 : r ∈ normalizer (C3 s : Set G) := y7b_R_le_NC3 hH hr
  have hrNHB : r ∈ normalizer ((normIn s.H s.fr.B : Subgroup G) : Set G) := by
    rw [normIn]
    exact mem_normalizer_inf (Subgroup.le_normalizer hrH) (mem_normalizer_normalizer hrB)
  have hcomm : r ∈ normalizer ((⁅X7 s, normIn s.H s.fr.B⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator hrX7 hrNHB
  have hBC3 : r ∈ normalizer ((s.fr.B ⊔ C3 s : Subgroup G) : Set G) :=
    mem_normalizer_sup hrB hrC3
  rw [C7]
  exact mem_normalizer_sup (mem_normalizer_pCoreOf hcomm) hBC3

theorem y7b_R_le_NM7 (hH : F33Hyp s e) : s.R ≤ normalizer (M7 s : Set G) := by
  intro r hr
  have hrT : r ∈ s.T := s.R_le_T hr
  have hrB : r ∈ normalizer (s.fr.B : Set G) := by
    have h : r ∈ normIn s.H s.fr.B := y54_R_le_NB hH hr
    rw [normIn] at h
    exact (Subgroup.mem_inf.mp h).2
  have hrM3 : r ∈ normalizer (M3 s : Set G) := y7b_R_le_NM3 hH hr
  have hrC7 : r ∈ normalizer (C7 s : Set G) := y7b_R_le_NC7 hH hr
  have hrL : r ∈ normalizer (L : Set G) := s3_T_le_N s hH.hS hrT
  have hrNLB : r ∈ normalizer ((normIn L s.fr.B : Subgroup G) : Set G) := by
    rw [normIn]
    exact mem_normalizer_inf hrL (mem_normalizer_normalizer hrB)
  have hcomm : r ∈ normalizer ((⁅C7 s, normIn L s.fr.B⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator hrC7 hrNLB
  have hBM3 : r ∈ normalizer ((s.fr.B ⊔ M3 s : Subgroup G) : Set G) :=
    mem_normalizer_sup hrB hrM3
  rw [M7]
  exact mem_normalizer_sup hcomm hBM3

end CFSG.OddStandard.HigherRank.YamadaG23
