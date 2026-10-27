module

public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSU3
public import CFSG.ClassicalInvolution.AschTight.S19GCore

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

section OutOne


theorem outOne_su3 : OutOne SU3 := by
  have hadm := statedLieAdmissible_psu3
  obtain ⟨e, -⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  have hZ : Subgroup.center (CompData.model .PSU 3).G = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ Subgroup.center SU3 := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨x, hx, rfl⟩
    rw [center_su3_eq_bot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (e.injective (by rw [h1, map_one]))
  have hT : StatedClassicalModel ((CompData.model .PSU 3).G ⧸
      Subgroup.center (CompData.model .PSU 3).G) .PSU 3 3 1 :=
    statedClassicalModel_center_quotient hadm card_F9
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound _ 3 3 1
    hT).2.2.1
  have hOT : OutOne ((CompData.model .PSU 3).G ⧸ Subgroup.center (CompData.model .PSU 3).G) :=
    OutOne.of_card_dvd_two (by rw [hcard]; norm_num)
  exact OutOne.of_mulEquiv e (OutOne.of_center_eq_bot hZ hOT)

end OutOne

theorem su3_involutory_fixes (hout : OutOne SU3) {g₀ : SU3} (ρ : MulAut SU3) (hρ2 : ρ * ρ = 1)
    (hρR : ∀ r ∈ conjSub g₀ rootSU2₃, ρ r = r) :
    ∃ k ∈ conjSub g₀ rootSU2₃, k * k = 1 ∧ ρ = MulAut.conj k := by
  rcases eq_one_or_conj_of_fixes_su3 hout hρ2 hρR with h | ⟨s, hs2, hs1, hsρ⟩
  · exact ⟨1, Subgroup.one_mem _, mul_one 1, by rw [h, map_one]⟩
  · have hcomm : ∀ r ∈ rootSU2₃, (g₀⁻¹ * s * g₀) * r = r * (g₀⁻¹ * s * g₀) := by
      intro r hr
      have h1 := hρR _ (conj_mem_conjSub hr)
      rw [hsρ, MulAut.conj_apply] at h1
      have h2 : s * (g₀ * r * g₀⁻¹) = (g₀ * r * g₀⁻¹) * s := by
        calc s * (g₀ * r * g₀⁻¹) = s * (g₀ * r * g₀⁻¹) * s⁻¹ * s := by group
          _ = (g₀ * r * g₀⁻¹) * s := by rw [h1]
      calc g₀⁻¹ * s * g₀ * r = g₀⁻¹ * (s * (g₀ * r * g₀⁻¹)) * g₀ := by group
        _ = g₀⁻¹ * ((g₀ * r * g₀⁻¹) * s) * g₀ := by rw [h2]
        _ = r * (g₀⁻¹ * s * g₀) := by group
    have hsq : (g₀⁻¹ * s * g₀) * (g₀⁻¹ * s * g₀) = 1 := by
      calc (g₀⁻¹ * s * g₀) * (g₀⁻¹ * s * g₀) = g₀⁻¹ * (s * s) * g₀ := by group
        _ = 1 := by rw [hs2]; group
    rcases eq_one_or_rootInvSU₃_of_commutes (fun r hr => (hcomm r hr).symm.symm) hsq with
      ht | ht
    · exfalso
      apply hs1
      have e : s = g₀ * (g₀⁻¹ * s * g₀) * g₀⁻¹ := by group
      rw [e, ht]
      group
    · refine ⟨s, ?_, hs2, hsρ⟩
      rw [mem_conjSub_iff, ht]
      exact rootInvSU_mem_rootSU2 (by norm_num)

end CFSG.ClassicalInvolution.Q3.Q3PP

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Fg0

theorem invol_fixes_of_fg0 {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) {R : Subgroup S}
    (hR : CFSG.ClassicalInvolution.Disconnected.AschTight.S19G.FG0Model R) (ρ : MulAut S)
    (hρ2 : ρ * ρ = 1) (hρR : ∀ r ∈ R, ρ r = r) :
    ∃ k ∈ R, k * k = 1 ∧ ρ = MulAut.conj k := by
  obtain ⟨g, hg⟩ := hR.2.2 ρ ⟨1, by simpa [pow_two] using hρ2⟩ hρR
  have hg2 : g * g = 1 := by
    have hc : g * g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 : (ρ * ρ) x = x := by rw [hρ2]; rfl
      rw [hg] at h1
      simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
      calc x * (g * g) = ((g * (g * x * g⁻¹) * g⁻¹)) * (g * g) := by rw [h1]
        _ = (g * g) * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  by_cases hg1 : g = 1
  · exact ⟨1, Subgroup.one_mem _, mul_one 1, by rw [hg, hg1, map_one]⟩
  · have hcent : g ∈ Subgroup.centralizer (R : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 := hρR r hr
      rw [hg, MulAut.conj_apply] at h1
      calc r * g = (g * r * g⁻¹) * g := by rw [h1]
        _ = g * r := by group
    rcases hR.1 g hcent hg2 with h | h
    · exact absurd h hg1
    · exact ⟨g, h, hg2, hg⟩

end Fg0


end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
