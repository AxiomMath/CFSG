module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitChainWeak

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GSLit

variable {G : Type} [Group G] [Finite G]

theorem nonempty_oddCore_equiv_of_gsIsoCorr {s t : G} {M N : Subgroup G}
    (h : GSIsoCorr s M t N) : Nonempty (M ⧸ pPrimeCore 2 M ≃* N ⧸ pPrimeCore 2 N) := by
  obtain ⟨hC, -, hTN⟩ := gsIsoCorr_iff_sup.mp h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hMq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _
    hC.2.2.2.1).1 hC.2.2.2.2.1
  have htK : t ∈ coreActionKernel M :=
    mem_coreActionKernel.mpr ⟨hC.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.1⟩
  have ht2 : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hC.2.1, pow_one])
  have hTM := (fixedLayer_sup_pPrimeCore hMq (zpowers_le.mpr htK) ht2).1
  rw [fixedLayer_zpowers] at hTM
  obtain ⟨eM, -⟩ := exists_quotient_equiv_of_sup (le_sup_left.trans hTM.le) hTM
    (map_pPrimeCore_eq_inf_of_sup_eq hTM)
  obtain ⟨eN, -⟩ := exists_quotient_equiv_of_sup (le_sup_left.trans hTN.le) hTN
    (map_pPrimeCore_eq_inf_of_sup_eq hTN)
  exact ⟨eM.symm.trans eN⟩

@[expose] def gsForwardFamily (J : Subgroup G) : Set (Subgroup G) :=
  {M | ∃ L : Subgroup G, GSWeakReach J L ∧ ∃ g : G, M = conjugate L g}

theorem nonempty_oddCore_equiv_of_weakReach_of_B2Setting {a : G} {J S : Subgroup G}
    (h : B2Setting a J S) {M : Subgroup G} (hM : GSWeakReach J M) :
    Nonempty (M ⧸ pPrimeCore 2 M ≃* J ⧸ pPrimeCore 2 J) := by
  induction hM with
  | refl => exact ⟨MulEquiv.refl _⟩
  | @tail M N hreach hEdge ih =>
    obtain ⟨s, t, hC⟩ := hEdge
    obtain ⟨eM⟩ := ih
    obtain ⟨eMN⟩ := nonempty_oddCore_equiv_of_gsIsoCorr
      (gsIsoCorr_of_weakReach_of_B2Setting h s t M N hreach hC)
    exact ⟨eMN.symm.trans eM⟩

theorem isomorphicFamily_forwardFamily_of_B2Setting {a : G} {J S : Subgroup G}
    (h : B2Setting a J S) {T : Type*} [Group T]
    (hJT : Nonempty (J ⧸ pPrimeCore 2 J ≃* T)) :
    FooteMarked.IsomorphicFamily (gsForwardFamily J) T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro M ⟨L, hJL, g, rfl⟩
    obtain ⟨e, L₀, g₀, -, -, hL₀, -, rfl⟩ := reach_conjugate_isoTarget_weak h hJL
    have hC := (gsIsoCorr_conjugate hL₀ (g₀ * g)).1
    refine ⟨(g₀ * g)⁻¹ * e * (g₀ * g), hC.2.1, ?_, ?_⟩
    · simpa only [conjugate_conjugate] using hC.2.2.2.2.2.1
    · simpa only [conjugate_conjugate] using hC.2.2.2.2.2.2.1
  · rintro M ⟨L, hJL, g, rfl⟩
    obtain ⟨eL⟩ := nonempty_oddCore_equiv_of_weakReach_of_B2Setting h hJL
    obtain ⟨eT⟩ := hJT
    let e : L ≃* conjugate L g :=
      L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    let eQ := QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
    exact ⟨eQ.symm.trans (eL.trans eT)⟩
  · rintro M ⟨L, hJL, g, rfl⟩ x
    exact ⟨L, hJL, g * x, conjugate_conjugate L g x⟩
  · rintro s t M ⟨L, hJL, g, rfl⟩ N hC
    have hC' := gsWeakCorr_conjugate hC g⁻¹
    rw [conjugate_conjugate_inv] at hC'
    have hNfam : N ∈ gsForwardFamily J :=
      ⟨conjugate N g⁻¹, GSWeakReach.tail hJL hC', g,
        by simpa only [inv_inv] using (conjugate_conjugate_inv N g⁻¹).symm⟩
    have hIso := gsIsoCorr_conjugate
      (gsIsoCorr_of_weakReach_of_B2Setting h _ _ _ _ hJL hC') g
    rw [inv_inv, show g⁻¹ * (g * s * g⁻¹) * g = s by group,
      show g⁻¹ * (g * t * g⁻¹) * g = t by group,
      show conjugate (conjugate N g⁻¹) g = N from
        by simpa only [inv_inv] using conjugate_conjugate_inv N g⁻¹] at hIso
    obtain ⟨-, hjoin, hcover⟩ := gsIsoCorr_iff_sup.mp hIso
    have hnormal : conjugate N s = N := le_antisymm (le_sup_right.trans hjoin.le) ?_
    · exact ⟨hNfam, hnormal, hcover⟩
    · have h1 : conjugate (conjugate N s) s = N := by
        rw [conjugate_conjugate, show s * s = 1 by
          simpa only [hC.1, pow_two] using pow_orderOf_eq_one s, conjugate_one]
      calc N = conjugate (conjugate N s) s := h1.symm
        _ ≤ conjugate N s := map_mono (le_sup_right.trans hjoin.le)

end CFSG.ComponentClassification.GrSLit
