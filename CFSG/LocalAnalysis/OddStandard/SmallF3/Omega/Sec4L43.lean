module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma43_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h42 : Asc82Lemma42)
    (hf43 : Asc82Fact43) (hf43c : Asc82Fact43Class) : Asc82Lemma43 := by
  intro G _ _ t L S z hctx g hg
  let s : G := g⁻¹ * z * g
  have hgs : s ∈ centralizer ({t} : Set G) := hg
  have hSLB : Sec3SettingLB G t L := hctx.toSec4Setting.toSec3SettingLB
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hs2 : orderOf s = 2 := by
    show orderOf (g⁻¹ * z * g) = 2
    rw [orderOf_conjugate_eq z g, hz2]
  have hsN : s ∈ normalizer (L : Set G) := sec4_mem_normalizer h36 hSLB s hgs
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  have hE : CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G)) = ⊥ :=
    h37 G t L hSLB z g hctx.pocket hgs
  obtain ⟨w, hw, hcL⟩ := hf43 G L hL s hs2 hsN hE
  have hw_mem : w ∈ L := hw.mem
  obtain ⟨l, hl, hlw⟩ := hf43c G L hL z w hctx.pocket hw
  let c : G := w⁻¹ * s
  have hs_eq : s = w * c := by
    show s = w * (w⁻¹ * s)
    group
  have hcw : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hcL w hw_mem).symm
  have hsw : s * w = w * s := by
    rw [hs_eq, mul_assoc, hcw]
  have hsw_inv : s * w⁻¹ = w⁻¹ * s :=
    (Commute.inv_right (show Commute s w from hsw)).eq
  have hw2 : orderOf w = 2 := hw.1
  have hs_sq : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2, pow_two] at h
    exact h
  have hw_sq : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hw2, pow_two] at h
    exact h
  have hcc : c * c = 1 := by
    calc c * c = (w⁻¹ * s) * (w⁻¹ * s) := by rfl
      _ = w⁻¹ * (s * w⁻¹) * s := by group
      _ = w⁻¹ * (w⁻¹ * s) * s := by rw [hsw_inv]
      _ = (w⁻¹ * w⁻¹) * (s * s) := by group
      _ = 1 := by rw [hs_sq, mul_one, ← mul_inv_rev, hw_sq, inv_one]
  have hw_ct : w ∈ centralizer ({t} : Set G) := hctx.component.le hw_mem
  have hc_t : c ∈ centralizer ({t} : Set G) := by
    show w⁻¹ * s ∈ centralizer ({t} : Set G)
    exact (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).inv_mem hw_ct) hgs
  have hct : c * t = t * c :=
    (Subgroup.mem_centralizer_iff.mp hc_t t (Set.mem_singleton t)).symm
  have hcyc : ∀ P : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (P : Subgroup (centralizer (L : Set G))) := h42 G t L hctx.toSec4Setting
  have htL : t ∈ centralizer (L : Set G) :=
    sec4_t_mem_centralizer hctx.toSec4Setting.toSec3SettingLB.toSec3Setting
  have hlt : l * t = t * l :=
    (Subgroup.mem_centralizer_iff.mp (hctx.component.le hl) t (Set.mem_singleton t)).symm
  have hcase : c = 1 ∨ c = t :=
    sec4_eq_of_commute (H := centralizer (L : Set G)) hcyc hcL htL hcc hctx.involution hct
  change s ∈ conjClassIn L z ∨ s ∈ conjClassIn L (t * z)
  rcases hcase with hc1 | hct_eq
  · left
    exact ⟨l, hl, by rw [hs_eq, hc1, mul_one, hlw]⟩
  · right
    refine ⟨l, hl, ?_⟩
    calc s = w * c := hs_eq
      _ = w * t := by rw [hct_eq]
      _ = t * w := (Subgroup.mem_centralizer_iff.mp hw_ct t (Set.mem_singleton t)).symm
      _ = t * (l * z * l⁻¹) := by rw [hlw]
      _ = l * (t * z) * l⁻¹ := by
        rw [show t * (l * z * l⁻¹) = (t * l) * z * l⁻¹ by group,
            show l * (t * z) * l⁻¹ = (l * t) * z * l⁻¹ by group,
            hlt]

end CFSG.OddStandard.SmallF3.Omega
