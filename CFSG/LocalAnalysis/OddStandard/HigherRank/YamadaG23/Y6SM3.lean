module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Setting
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SProd

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y6_R_le_normalizer_M3 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    c.s.R ≤ Subgroup.normalizer (M3 c.s : Set G) :=
  Subgroup.le_normalizer_iff.mpr (y54_R_norm_M3 c.toCtx5 hH)

private theorem y6_T_le_normalizer_M3 (c : Ctx6 G L) (hH : F33Hyp c.s c.e)
    (hF : c.toCtx5.Facts5) : c.s.T ≤ Subgroup.normalizer (M3 c.s : Set G) := by
  by_cases hRT : c.s.R = c.s.T
  · rw [← hRT]
    exact y6_R_le_normalizer_M3 c hH
  · have h55 := hF.2.2.2.1 hRT
    have hg : c.g ∈ Subgroup.normalizer (M3 c.s : Set G) := by
      have hcent : c.g ∈ Subgroup.centralizer (M3 c.s : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h := h55 m hm
        calc m * c.g = (c.g * m * c.g⁻¹) * c.g := by rw [h]
          _ = c.g * m := by group
      exact Subgroup.centralizer_le_normalizer (M3 c.s : Set G) hcent
    rw [y5_T_eq_R_g hH hRT]
    exact sup_le (y6_R_le_normalizer_M3 c hH) (Subgroup.zpowers_le.mpr hg)

theorem y6_M3_le_X (c : Ctx6 G L) (hF : c.toCtx5.Facts5) : M3 c.s ≤ y6X c := by
  obtain ⟨-, ⟨⟨hC3, -, hcomm⟩, -⟩⟩ := hF.2.2.1
  have hFM3 : c.s.fr.F ≤ M3 c.s := le_sup_right
  have hcommC1 : ⁅C1 c.e, C3 c.s⁆ ≤ C1 c.e :=
    hcomm.trans (by
      rw [y6_C1_eq c]
      exact sup_le_sup_right (s3_F_le_A c.s) (C0 c.e))
  haveI : IsMulCommutative ↥(M3 c.s) := by
    rcases hF.2.2.2.2.2.2 with ⟨-, hE⟩ | ⟨-, hMC, -⟩
    · exact hE.1
    · exact hMC
  have hconj : ∀ m ∈ M3 c.s, ∀ x ∈ C1 c.e, m * x * m⁻¹ ∈ C1 c.e := by
    intro m hm x hx
    have hM3C3 : M3 c.s ≤ C3 c.s := hC3 ▸ le_sup_left
    have hmC3 : m ∈ C3 c.s := hM3C3 hm
    have hcm : ⁅m, x⁆ ∈ C1 c.e := by
      refine hcommC1 ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hmC3 hx
    have he : m * x * m⁻¹ = ⁅m, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact (C1 c.e).mul_mem hcm hx
  intro m hm
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj m hm x hx
    · intro hx
      have h := hconj m⁻¹ ((M3 c.s).inv_mem hm) (m * x * m⁻¹) hx
      have he : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x := by group
      rwa [he] at h
  · have hfix : ∀ y ∈ M3 c.s, m * y * m⁻¹ = y := by
      intro y hy
      have hc := Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s) hm hy
      calc m * y * m⁻¹ = y * m * m⁻¹ := by rw [hc]
        _ = y := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have hvM : v ∈ M3 c.s := (Subgroup.mem_inf.mp hv).2
      rw [hfix v hvM]
      exact hv
    · intro hv
      have hvM : m * v * m⁻¹ ∈ M3 c.s := (Subgroup.mem_inf.mp hv).2
      have hvM3 : v ∈ M3 c.s := by
        have he : m⁻¹ * (m * v * m⁻¹) * m = v := by group
        rw [← he]
        exact (M3 c.s).mul_mem ((M3 c.s).mul_mem ((M3 c.s).inv_mem hm) hvM) hm
      rw [← hfix v hvM3]
      exact hv

theorem y6_card_TM3 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    Nat.card ↥(c.s.T ⊔ M3 c.s) = 8 * Nat.card ↥c.s.T := by
  obtain ⟨⟨-, hB, -, -⟩, -⟩ := hF.2.2.1
  have hTN : c.s.T ≤ Subgroup.normalizer (M3 c.s : Set G) :=
    y6_T_le_normalizer_M3 c hH hF
  have hFT : c.s.fr.F ≤ c.s.T :=
    (s3_F_le_A c.s).trans ((s3_A_le_S c.s).trans (c.s.S_le_R.trans c.s.R_le_T))
  have hFM3 : c.s.fr.F ≤ M3 c.s := le_sup_right
  have hTF : c.s.T ⊓ M3 c.s = c.s.fr.F := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxT, hxM⟩ := Subgroup.mem_inf.mp hx
      rw [← hB]
      exact Subgroup.mem_inf.mpr ⟨c.s.sylow_T.1 hxT, hxM⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hFT hx, hFM3 hx⟩
  have hcardM3 : Nat.card ↥(M3 c.s) = 8 * Nat.card ↥c.s.fr.F := by
    have h := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := M3 c.s)
    rw [inf_of_le_left hFM3, y54_M3_relIndex c.toCtx5 hH] at h
    exact h.symm
  have hprod := y6_card_sup_mul_inf (H := c.s.T) (N := M3 c.s) hTN
  rw [hTF, hcardM3] at hprod
  have hpos : 0 < Nat.card ↥c.s.fr.F := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hprod]
  ring

theorem y6_TM3_pgroup (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    IsPGroup 2 ↥(c.s.T ⊔ M3 c.s) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := y6_card_TM3 c hH hF
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq c.s.sylow_T.2.1
  refine IsPGroup.of_card (n := k + 3) ?_
  rw [hcard, hk, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, Nat.add_comm 3 k]

theorem y6_TM3_le_X (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    c.s.T ⊔ M3 c.s ≤ y6X c :=
  sup_le ((s6_T_le_Y c hH).trans (s6_Y_le_X c hH)) (y6_M3_le_X c hF)

end CFSG.OddStandard.HigherRank.YamadaG23
