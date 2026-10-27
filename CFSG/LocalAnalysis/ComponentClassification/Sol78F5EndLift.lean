module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndB

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

theorem le_of_forall_inf_centralizer_le_of_equiv
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    {M : Subgroup G} {b : G} (hM : IsTwoComponentAt b M) (hRM : S ⊓ L ≤ M)
    (e : L ⧸ pPrimeCore 2 L ≃* M ⧸ pPrimeCore 2 M) {H' : Subgroup G}
    (hC : ∀ r ∈ S ⊓ L, orderOf r = 2 → M ⊓ centralizer ({r} : Set G) ≤ H') : M ≤ H' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := H.sec5.quotient_simple.1
  have : IsSimpleGroup (M ⧸ pPrimeCore 2 M) := e.symm.isSimpleGroup
  have hD : AschbacherKnownGroup.HasDihedralSylowTwo (M ⧸ pPrimeCore 2 M) :=
    hasDihedralSylowTwo_of_gorensteinWalter
      (OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e.symm H.sec5.hasDihedralSylowTwo_quotient)
  have hMres : M ≤ oddResidualIn M := (oddResidualIn_eq_self_of_isPComponent hM.2.1 hM.2.2).ge
  have hRsyl : IsSylowOf 2 (S ⊓ L) M := by
    refine isSylowOf_of_card hRM ?_
    rw [H.sec5.R_sylow.card_eq, factorization_card_eq_of_equiv e]
  obtain ⟨P₀, hP₀⟩ := hRsyl.exists_sylow_eq_subgroupOf
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set P := P₀.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M)) with hP
  have hP2 : IsPGroup 2 ((S ⊓ L).subgroupOf M) := hP₀ ▸ P₀.isPGroup'
  have hinj : Function.Injective (π.subgroupMap ((S ⊓ L).subgroupOf M)) := fun x y hxy =>
    Subtype.ext (GSThmB.OddQuot.injOn_of_isPGroup hP2 x.2 y.2 (congrArg Subtype.val hxy))
  have hPcoe : (P : Subgroup (M ⧸ pPrimeCore 2 M)) = ((S ⊓ L).subgroupOf M).map π := by
    rw [hP, Sylow.coe_mapSurjective, hP₀]
  let eP : ↥((S ⊓ L).subgroupOf M) ≃* ↥(P : Subgroup (M ⧸ pPrimeCore 2 M)) :=
    (MulEquiv.ofBijective _ ⟨hinj, π.subgroupMap_surjective _⟩).trans
      (MulEquiv.subgroupCongr hPcoe.symm)
  let eR : ↥(P : Subgroup (M ⧸ pPrimeCore 2 M)) ≃* ↥(S ⊓ L) :=
    eP.symm.trans (subgroupOfEquivOfLe hRM)
  have hnaP : ∃ a ∈ (P : Subgroup (M ⧸ pPrimeCore 2 M)),
      ∃ c ∈ (P : Subgroup (M ⧸ pPrimeCore 2 M)), a * c ≠ c * a := by
    obtain ⟨a, ha, c, hc, hac⟩ := H.nonab
    refine ⟨eR.symm ⟨a, ha⟩, (eR.symm ⟨a, ha⟩).2, eR.symm ⟨c, hc⟩, (eR.symm ⟨c, hc⟩).2,
      fun h => hac ?_⟩
    have h1 : eR.symm (⟨a, ha⟩ * ⟨c, hc⟩) = eR.symm (⟨c, hc⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h
    exact congrArg Subtype.val (eR.symm.injective h1)
  have hnab : ∀ P' : Sylow 2 (↥M ⧸ pPrimeCore 2 ↥M), ∃ x ∈ (P' : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)),
      ∃ y ∈ (P' : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)), x * y ≠ y * x := by
    intro P'
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M ⧸ pPrimeCore 2 M) P P'
    obtain ⟨a, ha, c, hc, hac⟩ := hnaP
    refine ⟨g * a * g⁻¹, ?_, g * c * g⁻¹, ?_, fun h1 => hac ?_⟩
    · rw [← hg, Sylow.coe_subgroup_smul]
      exact ⟨a, ha, rfl⟩
    · rw [← hg, Sylow.coe_subgroup_smul]
      exact ⟨c, hc, rfl⟩
    · have h2 : g * (a * c) * g⁻¹ = g * (c * a) * g⁻¹ := by
        calc g * (a * c) * g⁻¹ = g * a * g⁻¹ * (g * c * g⁻¹) := by group
          _ = g * c * g⁻¹ * (g * a * g⁻¹) := h1
          _ = g * (c * a) * g⁻¹ := by group
      simpa using h2
  obtain ⟨ρ, b', j, hDR, -⟩ := H.exists_dihData_R
  obtain ⟨V, hVR, hV⟩ := exists_isKleinFour_of_dihData hDR
  exact le_of_forall_centralizer_le_gen hK hcalc hMres (MulEquiv.refl _) hD hnab
    (fun r hr => le_normalizer (hRM hr)) H.sec5.R_sylow.isPGroup ⟨P, ⟨eR⟩⟩ hV hVR hC

theorem nonempty_footeF_equiv {b : G} (hbQ : b ∈ Q) (hb2 : orderOf b = 2) :
    Nonempty (L ⧸ pPrimeCore 2 L ≃* footeF L₀ b ⧸ pPrimeCore 2 (footeF L₀ b)) := by
  obtain ⟨-, -, hMF, hMs, hMna, -⟩ := H.sec5.footeF_data hbQ hb2
  obtain ⟨eM⟩ := hMF.2
  obtain ⟨eL⟩ := H.sec5.quotient_simple.2
  exact ⟨eL.trans (eM.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (fusionZStar_eq_pPrimeCore _ hMna)))⟩

theorem footeF_le_of_mem_Rs (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {N : Subgroup G}
    (hWN : ∀ B₁ B₂ : Subgroup G, B₁ ≤ S ⊓ L → B₂ ≤ conjugate (S ⊓ L) s → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
      normalizer ((B₁ ⊔ B₂ : Subgroup G) : Set G) ≤ N) {b : G}
    (hb : b ∈ conjugate (S ⊓ L) s) (hb2 : orderOf b = 2) : footeF L₀ b ≤ N := by
  have hbQ := H.l511 hb
  obtain ⟨hfix, hM, -, -, -, -⟩ := H.sec5.footeF_data hbQ hb2
  obtain ⟨e⟩ := H.nonempty_footeF_equiv hbQ hb2
  have hb1 : zpowers b ≠ ⊥ := fun h => by
    have h1 := mem_zpowers b
    rw [h, mem_bot] at h1
    rw [h1, orderOf_one] at hb2
    omega
  refine H.le_of_forall_inf_centralizer_le_of_equiv hK hcalc hM
    (hfix ▸ H.sec5.R_le_footeFixed hbQ) e fun r hr hr2 x hx => ?_
  obtain ⟨hxM, hxr⟩ := mem_inf.mp hx
  have hr1 : zpowers r ≠ ⊥ := fun h => by
    have h1 := mem_zpowers r
    rw [h, mem_bot] at h1
    rw [h1, orderOf_one] at hr2
    omega
  refine hWN _ _ (zpowers_le_of_mem hr) (zpowers_le_of_mem hb) hr1 hb1 ?_
  exact mem_normalizer_sup
    (mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp hxr))
    (mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp (hM.2.1 hxM)))

end Hyp

end CFSG.ComponentClassification.Sol78.F514
