module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_exists_k (c : Ctx7 G L) (hb : B5Std c) :
    ∃ k : G, k ∈ normIn L c.s.fr.B ∧ k ^ 3 = 1 ∧ k ≠ 1 ∧
      (∀ u ∈ y7bBM c.s, u ∉ M3 c.s → ∀ v ∈ y7bBM c.s, v ∉ M3 c.s →
        ∃ i : ℕ, v⁻¹ * (k ^ i * u * (k ^ i)⁻¹) ∈ M3 c.s) ∧
      (∀ u ∈ y7bBM c.s, u⁻¹ * (k * u * k⁻¹) ∈ M3 c.s → u ∈ M3 c.s) ∧
      (∀ n ∈ normIn L c.s.fr.B,
        ∃ b ∈ c.s.fr.B, n * k * n⁻¹ = k * b ∨ n * k * n⁻¹ = k⁻¹ * b) := by
  obtain ⟨k, hkN, hk3, hk1, _, _, hknorm⟩ := f3_exists_k hb.hH
  refine ⟨k, hkN, hk3, hk1, ?_, ?_, hknorm⟩
  · intro u huBM huM3 v hvBM hvM3
    obtain ⟨b, hbB, m, hmM3, rfl⟩ := (y7b_mem_BM c hb).mp huBM
    obtain ⟨b', hb'B, m', hm'M3, rfl⟩ := (y7b_mem_BM c hb).mp hvBM
    have hbF : b ∉ c.s.fr.F := fun hbF =>
      huM3 ((M3 c.s).mul_mem ((le_sup_right : c.s.fr.F ≤ M3 c.s) hbF) hmM3)
    have hb'F : b' ∉ c.s.fr.F := fun hb'F =>
      hvM3 ((M3 c.s).mul_mem ((le_sup_right : c.s.fr.F ≤ M3 c.s) hb'F) hm'M3)
    obtain ⟨i, hi⟩ := y7b_k_trans_BF hb.hH hkN hk3 hk1 b hbB hbF b' hb'B hb'F
    have hLH : L ≤ c.s.H := s3_L_le_H c.s hb.hH.hS
    have hkiN : k ^ i ∈ normIn L c.s.fr.B := Subgroup.pow_mem (normIn L c.s.fr.B) hkN i
    have hkiNM3 : k ^ i ∈ normalizer (M3 c.s : Set G) :=
      y7b_N_le_NM3 c hb ⟨hLH hkiN.1, hkiN.2⟩
    have hmi : k ^ i * m * (k ^ i)⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp hkiNM3 m).mp hmM3
    refine ⟨i, ?_⟩
    rw [show (b' * m')⁻¹ * (k ^ i * (b * m) * (k ^ i)⁻¹) =
      m'⁻¹ * (b'⁻¹ * (k ^ i * b * (k ^ i)⁻¹)) * (k ^ i * m * (k ^ i)⁻¹) from by
        group]
    exact (M3 c.s).mul_mem ((M3 c.s).mul_mem ((M3 c.s).inv_mem hm'M3)
      ((le_sup_right : c.s.fr.F ≤ M3 c.s) hi)) hmi
  · intro u huBM hfix
    obtain ⟨b, hbB, m, hmM3, rfl⟩ := (y7b_mem_BM c hb).mp huBM
    have hLH : L ≤ c.s.H := s3_L_le_H c.s hb.hH.hS
    have hkm : k * m * k⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp (y7b_N_le_NM3 c hb ⟨hLH hkN.1, hkN.2⟩) m).mp hmM3
    have h1 : m⁻¹ * (b⁻¹ * k * b * k⁻¹) ∈ M3 c.s := by
      have h := (M3 c.s).mul_mem hfix ((M3 c.s).inv_mem hkm)
      rwa [show (b * m)⁻¹ * (k * (b * m) * k⁻¹) * (k * m * k⁻¹)⁻¹ =
        m⁻¹ * (b⁻¹ * k * b * k⁻¹) from by group] at h
    have hX : b⁻¹ * k * b * k⁻¹ ∈ M3 c.s := by
      have h := (M3 c.s).mul_mem hmM3 h1
      rwa [show m * (m⁻¹ * (b⁻¹ * k * b * k⁻¹)) = b⁻¹ * k * b * k⁻¹ from by group] at h
    have hXB : b⁻¹ * k * b * k⁻¹ ∈ c.s.fr.B := by
      have hkb : k * b * k⁻¹ ∈ c.s.fr.B :=
        (Subgroup.mem_normalizer_iff.mp hkN.2 b).mp hbB
      have h := (c.s.fr.B).mul_mem ((c.s.fr.B).inv_mem hbB) hkb
      rwa [show b⁻¹ * (k * b * k⁻¹) = b⁻¹ * k * b * k⁻¹ from by group] at h
    have hXF : b⁻¹ * k * b * k⁻¹ ∈ c.s.fr.F := by
      have h := Subgroup.mem_inf.mpr ⟨hXB, hX⟩
      rwa [y7b_B_inf_M3 c hb] at h
    have hB_le_N : c.s.fr.B ≤ normIn L c.s.fr.B := by
      rw [normIn]
      exact le_inf (f3_B_le_L c.s) Subgroup.le_normalizer
    have h3b : normIn L c.s.fr.B ≤ normIn L c.s.fr.F := hb.hH.hLF.fact18.2.1.2.1
    have hcommF : k * b * k⁻¹ * b⁻¹ ∈ c.s.fr.F := by
      have hbNF : b ∈ normalizer (c.s.fr.F : Set G) := (h3b (hB_le_N hbB)).2
      have h := (Subgroup.mem_normalizer_iff.mp hbNF (b⁻¹ * k * b * k⁻¹)).mp hXF
      rwa [show b * (b⁻¹ * k * b * k⁻¹) * b⁻¹ = k * b * k⁻¹ * b⁻¹ from by group] at h
    have hbF : b ∈ c.s.fr.F := y7b_k_fix_BF hb.hH hkN hk3 hk1 b hbB hcommF
    exact (M3 c.s).mul_mem ((le_sup_right : c.s.fr.F ≤ M3 c.s) hbF) hmM3

theorem y7b_exists_seed (c : Ctx7 G L) (hb : B5Std c) :
    ∃ m₀ ∈ M4 c.e, m₀ ^ 2 = 1 ∧ ⁅m₀, c.s.t⁆ ∈ c.s.fr.E ∧ ⁅m₀, c.s.t⁆ ∉ M3 c.s := by
  have hnotEF : ¬ c.s.fr.E ≤ c.s.fr.F := by
    intro hle
    have hcard : Nat.card ↥(c.s.fr.E ⊓ c.s.fr.F) = Nat.card ↥c.s.fr.E := by
      rw [inf_eq_left.mpr hle]
    rw [y7b_E_inf_F hb.hH, y7b_card_V hb.hH, y7b_card_E hb.hH] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨e, heE, heF⟩ := Set.not_subset.mp hnotEF
  obtain ⟨m, hmM4, hmφ⟩ := y7b_phi_M4 c hb e heE
  refine ⟨m, hmM4, hb.h72.2.1.2 m hmM4, ?_, ?_⟩
  · rwa [hmφ]
  · intro hmM3
    have heH : e ∈ c.s.H :=
      (y56_E_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS) heE
    have heM3 : e ∈ M3 c.s := hmφ ▸ hmM3
    have hmem : e ∈ c.s.H ⊓ M3 c.s := Subgroup.mem_inf.mpr ⟨heH, heM3⟩
    rw [y54_H_inf_M3 c.toCtx5 hb.hH] at hmem
    exact heF hmem

theorem y7b_W_isPGroup (c : Ctx7 G L) (hb : B5Std c) : IsPGroup 2 ↥(y7bW c.s) :=
  IsPGroup.of_card (n := 9) (y7b_card_W c hb)

theorem y7b_pCoreOf_eq_self {K : Subgroup G} (hK : IsPGroup 2 ↥K) : pCoreOf 2 K = K := by
  show (pCore 2 ↥K).map K.subtype = K
  apply le_antisymm (Subgroup.map_subtype_le _)
  intro b hb
  have htop : (⊤ : Subgroup ↥K) ≤ pCore 2 ↥K :=
    le_sSup ⟨Subgroup.normal_top, hK.of_equiv Subgroup.topEquiv.symm⟩
  exact ⟨⟨b, hb⟩, htop (Subgroup.mem_top _), rfl⟩

end CFSG.OddStandard.HigherRank.YamadaG23
