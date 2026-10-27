module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Z2b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Kchar
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4GSyl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec4S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_V_norm (c : Ctx4 s e) {y : G} (hy : y ∈ normalizer (s.T₂ : Set G)) :
    ∀ v ∈ cen s.fr.B, y * v * y⁻¹ ∈ cen s.fr.B := by
  have hZ : ∀ u ∈ zSeries 2 s.T₂, y * u * y⁻¹ ∈ zSeries 2 s.T₂ :=
    fun u hu => y4_conj_zSeries 2 hy hu
  intro v hv
  rw [← y4_omega1_Z2 c] at hv ⊢
  exact y4_conj_omega1 (U := zSeries 2 s.T₂) hZ hv

theorem y4_K_norm (c : Ctx4 s e) {y : G} (hy : y ∈ normalizer (s.T₂ : Set G)) :
    y ∈ normalizer ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) := by
  have hV : ∀ u ∈ cen s.fr.B, y * u * y⁻¹ ∈ cen s.fr.B := y4_V_norm c hy
  have hyV : y ∈ normalizer (cen s.fr.B : Set G) := y4_mem_normalizer_of_conj_mem hV
  have hZt : ∀ u ∈ y4Zt c, y * u * y⁻¹ ∈ y4Zt c :=
    fun u hu => y4_conj_Zmod (y4_T2_le_normV c) hy hyV hu
  have hCent : ∀ x ∈ Subgroup.centralizer (cen s.fr.B : Set G),
      y * x * y⁻¹ ∈ Subgroup.centralizer (cen s.fr.B : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hw : y⁻¹ * v * y ∈ cen s.fr.B := by
      have h := (Subgroup.mem_normalizer_iff.mp
        ((normalizer (cen s.fr.B : Set G)).inv_mem hyV) v).mp hv
      simpa using h
    have hxw : x * (y⁻¹ * v * y) * x⁻¹ = y⁻¹ * v * y := by
      rw [← hx (y⁻¹ * v * y) hw, mul_assoc, mul_inv_cancel, mul_one]
    have hgoal : (y * x * y⁻¹) * v * (y * x * y⁻¹)⁻¹ = v := by
      calc (y * x * y⁻¹) * v * (y * x * y⁻¹)⁻¹
          = y * (x * (y⁻¹ * v * y) * x⁻¹) * y⁻¹ := by group
        _ = y * (y⁻¹ * v * y) * y⁻¹ := by rw [hxw]
        _ = v := by group
    exact (mul_inv_eq_iff_eq_mul.mp hgoal).symm
  have hyCent : y ∈ normalizer (Subgroup.centralizer (cen s.fr.B : Set G) : Set G) :=
    y4_mem_normalizer_of_conj_mem hCent
  have hyU : y ∈ normalizer (y4Zt' c : Set G) := by
    refine y4_mem_normalizer_of_conj_mem fun u hu => ?_
    rw [y4Zt', Subgroup.mem_inf] at hu ⊢
    exact ⟨hZt u hu.1, hCent u hu.2⟩
  have hcen : ∀ u ∈ cen (y4Zt' c), y * u * y⁻¹ ∈ cen (y4Zt' c) :=
    fun u hu => y4_conj_cen hyU hu
  refine y4_mem_normalizer_of_conj_mem fun v hv => ?_
  rw [← y4_omega1_cen_Zt' c] at hv ⊢
  exact y4_conj_omega1 hcen hv

theorem sec42_of (hB : Sec3Inputs) : Sec42 := by
  intro G _ _ L hS hL s e hBr
  have c : Ctx4 s e := ctx4_of hB hS hL s e hBr
  refine y4_sylow_of_norm (P := s.T₂)
    (K := (cen s.fr.B ⊔ zpowers s.t : Subgroup G)) ?_ ?_
  · rw [← c.h33.1.1]
    exact f3_c9 c.toF33
  · intro y hy
    exact y4_K_norm c hy

end CFSG.OddStandard.HigherRank.YamadaG23
