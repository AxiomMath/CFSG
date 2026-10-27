module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2CF
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2M6c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_fact72_4 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : c.s.R ≠ c.s.T → ∀ m ∈ M6 c.e, ⁅c.g, m⁆ ∈ M3 c.s := by
  intro hRT m hm
  obtain ⟨hgT, -, -, -, -⟩ := c.g_spec hRT
  have hgX : c.g ∈ y7aX c := y7a_Y_le_X c hH (s5_T_le_Y c.toCtx5 hH hgT)
  have hM3M6 : M3 c.s ≤ M6 c.e := h71.2.2.2.1
  have hk6 : ⁅c.g, m⁆ ∈ M6 c.e := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (y7a_M6_normal c hH hF c.g hgX m hm) (Subgroup.inv_mem _ hm)
  rw [← y7a_cent_M6_F c hH hF h71]
  refine Subgroup.mem_inf.mpr ⟨hk6, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hfM3 : f ∈ M3 c.s := y7a_F_le_M3 c hf
  have hfM6 : f ∈ M6 c.e := hM3M6 hfM3
  have hv : ⁅f, m⁆ ∈ V1 c.e :=
    y7a_M6_comm_le_V1 c hH hF (Subgroup.commutator_mem_commutator hfM6 hm)
  have hvM3 : ⁅f, m⁆ ∈ M3 c.s := y7a_V1_le_M3 c hv
  have e1 : c.g * f * c.g⁻¹ = f := hF.2.2.2.1 hRT f hfM3
  have e3 : c.g * ⁅f, m⁆ * c.g⁻¹ = ⁅f, m⁆ := hF.2.2.2.1 hRT _ hvM3
  have e4 : ⁅f, m⁆ * ⁅c.g, m⁆ = ⁅c.g, m⁆ * ⁅f, m⁆ :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk6).2 _ hv
  have e2 : f * m * f⁻¹ = ⁅f, m⁆ * m := by rw [commutatorElement_def]; group
  have e1' : f * c.g * f⁻¹ = c.g := by
    have := e1
    rw [mul_inv_eq_iff_eq_mul] at this ⊢
    exact this.symm
  have hconj : f * ⁅c.g, m⁆ * f⁻¹ = ⁅c.g, m⁆ := by
    calc f * ⁅c.g, m⁆ * f⁻¹
        = (f * c.g * f⁻¹) * (f * m * f⁻¹) * (f * c.g * f⁻¹)⁻¹ * (f * m * f⁻¹)⁻¹ := by
          rw [commutatorElement_def]; group
      _ = c.g * (⁅f, m⁆ * m) * c.g⁻¹ * (⁅f, m⁆ * m)⁻¹ := by rw [e1', e2]
      _ = (c.g * ⁅f, m⁆ * c.g⁻¹) * (c.g * m * c.g⁻¹ * m⁻¹) * ⁅f, m⁆⁻¹ := by group
      _ = ⁅f, m⁆ * ⁅c.g, m⁆ * ⁅f, m⁆⁻¹ := by rw [e3, commutatorElement_def (c.g) m]
      _ = ⁅c.g, m⁆ := by rw [e4]; group
  exact (mul_inv_eq_iff_eq_mul.mp hconj)

end CFSG.OddStandard.HigherRank.YamadaG23
