module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Gen
public import CFSG.GH74.Generic.S1.SL2Facts
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_sl2_section {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h2 : pCore 2 Y = ⊥)
    {J : Subgroup Y} (hJ : IsComponent J) {K : Subgroup (Y ⧸ pCore p Y)} [K.Normal]
    (hJK : J.map (QuotientGroup.mk' (pCore p Y)) ≤ K) {q : ℕ} (hq : Odd q) (h4 : 4 ≤ q)
    (hK : CFSG.GH74.GLS.HasSL2Model ↥K (fun q' => q' = q)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hKqs : IsQuasisimple ↥K := CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 h4 hK
  have hJ' : IsComponent (J.map (QuotientGroup.mk' (pCore p Y))) :=
    isComponent_map_mk hp CFSG.pCore_normal hJ CFSG.pCore_isPGroup
  have hJeq : J.map (QuotientGroup.mk' (pCore p Y)) = ⁅K, K⁆ :=
    component_eq_commutator_of_le inferInstance hJ' hJK hKqs.2.1
  have hKK : ⁅K, K⁆ = K := by
    rw [← Subgroup.map_subtype_commutator, Group.isPerfect_def.mp hKqs.1, Subgroup.map_top,
      Subgroup.range_subtype]
  obtain ⟨t, htK, ht2, hu, -⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hq hK
  have hsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  have hcen : ∀ x ∈ K, t * x = x * t := by
    intro x hx
    have hxt : x * t * x⁻¹ ∈ K := mul_mem (mul_mem hx htK) (K.inv_mem hx)
    have hxsq : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [hsq]; group
    rcases hu _ hxt hxsq with h | h
    · exfalso
      apply ht1
      have : t = x⁻¹ * (x * t * x⁻¹) * x := by group
      rw [this, h]
      group
    · calc t * x = (x * t * x⁻¹) * x := by rw [h]
        _ = x * t := by group
  refine false_of_central_involution hp hp2 hJ h2 (t := t) ?_ ?_ hsq ht1
  · rw [hJeq, hKK]
    exact htK
  · intro x hx
    rw [hJeq, hKK] at hx
    exact hcen x hx

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
