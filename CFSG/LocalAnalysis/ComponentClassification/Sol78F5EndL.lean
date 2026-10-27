module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndGen
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndW

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem le_oddResidualIn : L ≤ oddResidualIn L :=
  (oddResidualIn_eq_self_of_isPComponent H.sec5.zL.2.1 H.sec5.zL.2.2).ge

theorem t_not_mem_oddCoreIn : t ∉ oddCoreIn L := fun h1 =>
  not_mem_of_odd (odd_card_oddCoreIn L) H.mul_self_t H.t_ne_one h1

theorem le_of_forall_inf_centralizer_le (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {H' : Subgroup G}
    (hC : ∀ r ∈ S ⊓ L, orderOf r = 2 → L ⊓ centralizer ({r} : Set G) ≤ H') : L ≤ H' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := H.sec5
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := h.quotient_simple.1
  have : IsSimpleGroup 𝕊 := ε.symm.isSimpleGroup
  have hD : AschbacherKnownGroup.HasDihedralSylowTwo 𝕊 :=
    hasDihedralSylowTwo_of_gorensteinWalter
      (OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv ε.symm h.hasDihedralSylowTwo_quotient)
  have hnaR : ∃ a ∈ (h.Rbar ε : Subgroup 𝕊), ∃ b ∈ (h.Rbar ε : Subgroup 𝕊), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := H.nonab
    exact ⟨_, h.psi_mem_Rbar ε ha, _, h.psi_mem_Rbar ε hb,
      fun h1 => hab ((h.psi_comm_iff ε ha hb).mp h1)⟩
  have hnab : ∀ P : Sylow 2 𝕊, ∃ x ∈ (P : Subgroup 𝕊), ∃ y ∈ (P : Subgroup 𝕊), x * y ≠ y * x := by
    intro P
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq 𝕊 (h.Rbar ε) P
    obtain ⟨a, ha, b, hb, hab⟩ := hnaR
    refine ⟨g * a * g⁻¹, ?_, g * b * g⁻¹, ?_, fun h1 => hab ?_⟩
    · rw [← hg, Sylow.coe_subgroup_smul]
      exact ⟨a, ha, rfl⟩
    · rw [← hg, Sylow.coe_subgroup_smul]
      exact ⟨b, hb, rfl⟩
    · have h2 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
        calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
          _ = g * b * g⁻¹ * (g * a * g⁻¹) := h1
          _ = g * (b * a) * g⁻¹ := by group
      simpa using h2
  obtain ⟨ρ, b, j, hDR, -⟩ := H.exists_dihData_R
  obtain ⟨V, hVR, hV⟩ := exists_isKleinFour_of_dihData hDR
  obtain ⟨e⟩ := h.nonempty_Rbar_equiv ε
  exact le_of_forall_centralizer_le_gen hK hcalc H.le_oddResidualIn ε hD hnab
    (fun r hr => le_normalizer (mem_inf.mp hr).2) h.R_sylow.isPGroup ⟨h.Rbar ε, ⟨e⟩⟩ hV hVR hC

end Hyp

end CFSG.ComponentClassification.Sol78.F514
