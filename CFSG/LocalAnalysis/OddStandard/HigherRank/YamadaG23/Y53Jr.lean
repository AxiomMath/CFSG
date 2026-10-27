module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53JrAbs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53JrG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53JrQ
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53JrS

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y53_jr_apply {c : Ctx5 G L} (hH : F33Hyp c.s c.e)
    [(c.s.fr.Z.subgroupOf c.e.T₁).Normal]
    {W : Subgroup G} (hWT : W ≤ c.e.T₁) (hWsup : c.e.T₁ = W ⊔ C0 c.e)
    (hAW : c.s.fr.A ≤ W)
    (hCent : ∀ x ∈ W, (∀ a ∈ c.s.fr.A, ⁅a, x⁆ ∈ c.s.fr.Z) → x ∈ c.s.fr.A)
    (hNW : (W.subgroupOf c.e.T₁).Normal)
    (hJ : thompsonRank ((W.subgroupOf c.e.T₁).map
        (QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁))) =
      (c.s.fr.A.subgroupOf c.e.T₁).map (QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁))) :
    thompsonRank (⊤ : Subgroup (↥c.e.T₁ ⧸ c.s.fr.Z.subgroupOf c.e.T₁)) =
      ((C1 c.e).subgroupOf c.e.T₁).map (QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁)) := by
  let π : ↥c.e.T₁ →* (↥c.e.T₁ ⧸ c.s.fr.Z.subgroupOf c.e.T₁) :=
    QuotientGroup.mk' (c.s.fr.Z.subgroupOf c.e.T₁)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hWn : ((W.subgroupOf c.e.T₁).map π).Normal := hNW.map π hπ
  have hC0le : C0 c.e ≤ c.e.T₁ := inf_le_left
  have hWK : (W.subgroupOf c.e.T₁).map π ⊔ ((C0 c.e).subgroupOf c.e.T₁).map π = ⊤ := by
    rw [← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup (A := W) (A' := C0 c.e) (B := c.e.T₁) hWT hC0le, ← hWsup,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective π hπ]
  have hAWbar : (c.s.fr.A.subgroupOf c.e.T₁).map π ≤ (W.subgroupOf c.e.T₁).map π :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono c.e.T₁ hAW)
  have hCW : ∀ w ∈ (W.subgroupOf c.e.T₁).map π,
      (∀ a ∈ (c.s.fr.A.subgroupOf c.e.T₁).map π, w * a = a * w) →
      w ∈ (c.s.fr.A.subgroupOf c.e.T₁).map π := by
    intro w hw hcomm
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    have hxW : (y : G) ∈ W := Subgroup.mem_subgroupOf.mp hy
    have hxA : (y : G) ∈ c.s.fr.A := by
      refine hCent (y : G) hxW ?_
      intro a ha
      have haT : a ∈ c.e.T₁ := hWT (hAW ha)
      let aT : ↥c.e.T₁ := ⟨a, haT⟩
      have haBar : π aT ∈ (c.s.fr.A.subgroupOf c.e.T₁).map π :=
        Subgroup.mem_map.mpr ⟨aT, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have hc := hcomm (π aT) haBar
      have hker : π (y * aT * y⁻¹ * aT⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hc]
        group
      have hker' : ((y * aT * y⁻¹ * aT⁻¹ : ↥c.e.T₁) :
          ↥c.e.T₁ ⧸ c.s.fr.Z.subgroupOf c.e.T₁) = 1 := by
        simpa only [π, QuotientGroup.mk'_apply] using hker
      have hmem : y * aT * y⁻¹ * aT⁻¹ ∈ c.s.fr.Z.subgroupOf c.e.T₁ :=
        (QuotientGroup.eq_one_iff (N := c.s.fr.Z.subgroupOf c.e.T₁) _).mp hker'
      have hmemZ : ((y * aT * y⁻¹ * aT⁻¹ : ↥c.e.T₁) : G) ∈ c.s.fr.Z :=
        Subgroup.mem_subgroupOf.mp hmem
      have hcoe : ((y * aT * y⁻¹ * aT⁻¹ : ↥c.e.T₁) : G) =
          (y : G) * a * (y : G)⁻¹ * a⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, aT]
      rw [hcoe] at hmemZ
      have hcomm' : ⁅a, (y : G)⁆ = ((y : G) * a * (y : G)⁻¹ * a⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [hcomm']
      exact c.s.fr.Z.inv_mem hmemZ
    exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hxA, rfl⟩
  rw [y53_jr_abs hWn hWK hAWbar (y53_barA hH) (y53_barK hH)
      (y53_bar_cent hH) (y53_bar_inf hH) hCW hJ,
    y53_bar_sup hH]

theorem y53_jr {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    SecProp c.e.T₁ c.s.fr.Z (fun Y _ _ π =>
      thompsonRank (⊤ : Subgroup Y) = ((C1 c.e).subgroupOf c.e.T₁).map π) := by
  by_cases hRT : c.s.R = c.s.T
  · obtain ⟨hZn, hJ⟩ := y53_jrS_T1 hH
    refine ⟨hZn, ?_⟩
    haveI := hZn
    exact y53_jr_apply hH hH.h32.2.1.1 (y5_T1_eq_S_C0 hH hRT) (s3_A_le_S c.s)
      (fun x hxS h => y53_centS hH x hxS h) (y5_S_normal_T1 hH) hJ
  · obtain ⟨hZn, hJ⟩ := y53_jrG_T1 hH hRT
    refine ⟨hZn, ?_⟩
    haveI := hZn
    obtain ⟨_, _, hact, hg2, _⟩ := c.g_spec hRT
    exact y53_jr_apply hH (y5_Sg_le_T1 hH hRT) (y5_T1_eq_Sg_C0 hH hRT)
      ((s3_A_le_S c.s).trans le_sup_left)
      (fun x hxW h => y53_centSg hH hg2 hact x hxW h) (y5_Sg_normal_T1 hH hRT) hJ

end CFSG.OddStandard.HigherRank.YamadaG23