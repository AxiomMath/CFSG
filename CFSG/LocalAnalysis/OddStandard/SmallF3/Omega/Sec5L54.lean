module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Fusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma54_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (tab : Asc82Tab5) : Asc82Lemma54 := by
  intro G _ _ t L S z h g hC
  have hs2 : orderOf (g⁻¹ * z * g) = 2 := by
    rw [orderOf_conjugate_eq, h.pocket.1]
  have hsN : g⁻¹ * z * g ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 h.toSec3SettingLB (g⁻¹ * z * g) hC
  have hbot : layerCent L (g⁻¹ * z * g) = ⊥ :=
    h37 G t L h.toSec3SettingLB z g h.pocket hC
  rcases tab.layer_trivial G L h.toSec5Setting.isOm6Z2 (g⁻¹ * z * g) hs2 hsN hbot with
    hk0 | hk3
  · have hsL : g⁻¹ * z * g ∈ L :=
      sec5_inner_decomp h52a h52b tab h.toSec5Setting hs2 hC hk0
    have hst : g⁻¹ * z * g ≠ t := sec5_t_not_conj_z h37 h g
    have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b h.toSec5Setting
    rcases tab.inv_classes G L h.toSec5Setting.isOm6Z2 t htZ h.involution z h.pocket
        (g⁻¹ * z * g) hsL hs2 hst with hz | htz
    · exact Or.inl hz
    · exfalso
      obtain ⟨a, -, ha⟩ := htz
      apply sec5_tz_not_conj_z h36 h37 h52b h53 tab h (g * a)
      have key : (g * a)⁻¹ * z * (g * a) = a⁻¹ * (g⁻¹ * z * g) * a := by
        rw [mul_inv_rev]; group
      rw [key, ha]; group
  · exact Or.inr hk3

end CFSG.OddStandard.SmallF3.Omega
