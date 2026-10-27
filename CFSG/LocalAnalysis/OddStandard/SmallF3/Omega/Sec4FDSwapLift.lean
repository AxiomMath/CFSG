module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G Pr : Type} [Group G] [Group Pr] {L : Subgroup G} {s : G} {X : Subgroup Pr} [X.Normal]
  {y : Pr} {ρ : ↥L →* ↥X}

private lemma sec4FD_swap_aux {c y pv : Pr} (hcy : c * y * c⁻¹ = y * pv)
    (hcomm : pv * y = y * pv) (hpv : pv * pv = 1) : c * (y * c⁻¹ * y⁻¹) * pv = 1 := by
  have hy : pv * y⁻¹ = y⁻¹ * pv := (Commute.inv_right (show Commute pv y from hcomm)).eq
  calc c * (y * c⁻¹ * y⁻¹) * pv
      = (c * y * c⁻¹) * (y⁻¹ * pv) := by group
    _ = (y * pv) * (y⁻¹ * pv) := by rw [hcy]
    _ = y * (pv * y⁻¹) * pv := by group
    _ = y * (y⁻¹ * pv) * pv := by rw [hy]
    _ = pv * pv := by group
    _ = 1 := hpv

theorem Sec4FDCover.mem_conjClassIn_swap (h : Sec4FDCover L s X y ρ) {v : G} (hvL : v ∈ L)
    (hvs : v * s = s * v) (hvv : v * v = 1) {c : Pr} (hcX : c ∈ X)
    (hc : c * y * c⁻¹ = y * ((ρ ⟨v, hvL⟩ : ↥X) : Pr)) :
    s * v ∈ conjClassIn L s := by
  obtain ⟨l₀, hl₀⟩ := h.cover.surjective (⟨c, hcX⟩ : ↥X)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right h.s_sq
  have hcval : ((ρ l₀ : ↥X) : Pr) = c := congrArg Subtype.val hl₀
  have hσval : ((ρ (sec4IConj L h.s_norm l₀⁻¹) : ↥X) : Pr) = y * c⁻¹ * y⁻¹ := by
    have he := h.equi l₀⁻¹ (sec4IConj L h.s_norm l₀⁻¹)
      (coe_sec4IConj L h.s_norm l₀⁻¹)
    rw [he]
    have h1 : ((ρ l₀⁻¹ : ↥X) : Pr) = c⁻¹ := by
      rw [map_inv, Subgroup.coe_inv, hcval]
    rw [h1]
  have hv0v0 : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := by
    apply Subtype.ext
    simpa using hvv
  have hpv2 : ((ρ ⟨v, hvL⟩ : ↥X) : Pr) * ((ρ ⟨v, hvL⟩ : ↥X) : Pr) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hv0v0, map_one]
    simp
  set m : ↥L := l₀ * sec4IConj L h.s_norm l₀⁻¹ * ⟨v, hvL⟩ with hm_def
  have hρm : ((ρ m : ↥X) : Pr) = 1 := by
    rw [hm_def]
    simp only [map_mul, Subgroup.coe_mul]
    rw [hcval, hσval]
    exact sec4FD_swap_aux hc (h.image_comm hvL hvs) hpv2
  have hmker : m ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simpa using hρm
  set a : G := (l₀ : G) * s * (l₀ : G)⁻¹ with ha_def
  set b : G := s * v with hb_def
  have hab_m : a * b = (m : G) := by
    rw [ha_def, hb_def, hm_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    rw [coe_sec4IConj, hsinv, Subgroup.coe_inv]
    group
  have haa : a * a = 1 := by
    rw [ha_def]
    calc ((l₀ : G) * s * (l₀ : G)⁻¹) * ((l₀ : G) * s * (l₀ : G)⁻¹)
        = (l₀ : G) * (s * s) * (l₀ : G)⁻¹ := by group
      _ = 1 := by rw [h.s_sq]; group
  have hbb : b * b = 1 := by
    rw [hb_def]
    calc (s * v) * (s * v) = s * (v * s) * v := by group
      _ = s * (s * v) * v := by rw [hvs]
      _ = (s * s) * (v * v) := by group
      _ = 1 := by rw [h.s_sq, hvv, one_mul]
  have hodd : Odd (orderOf (a * b)) := by
    rw [hab_m, Subgroup.orderOf_coe]
    exact h.cover.odd_card_ker.of_dvd_nat (Subgroup.orderOf_dvd_natCard ρ.ker hmker)
  obtain ⟨k, hk⟩ := sec4FD_exists_pow_conj haa hbb hodd
  refine ⟨((m ^ k * l₀ : ↥L) : G), (m ^ k * l₀ : ↥L).2, ?_⟩
  rw [hk, hab_m, ha_def, ← Subgroup.coe_pow]
  simp only [Subgroup.coe_mul]
  group

end CFSG.OddStandard.SmallF3.Omega
