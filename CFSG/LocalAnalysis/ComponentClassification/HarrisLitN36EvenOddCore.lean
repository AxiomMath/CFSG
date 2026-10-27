module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

namespace EvenOddCore

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueU

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] : CFSG.oddCore X = pPrimeCore 2 X := by
  unfold CFSG.oddCore pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem oddCore_eq_bot_of_exceptional
    {X : Type} [Group X] [Finite X] [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab' : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {t : StatedLieTag} {f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ChevalleyExceptionalModel (CFSG.generalizedFitting X) t 2 f) {z : X}
    (hz2 : orderOf z = 2) : CFSG.oddCore ↥(centralizer ({z} : Set X)) = ⊥ := by
  have hE6 := evenE6OuterInvolutionInput_holds
  obtain ⟨hadm, hcase⟩ := hmodel
  have hf : 1 ≤ f := hadm.2.1
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (UnbalancedCatalog.even_G2_almost_simple_odd_core_vanishing hnonab'
      ⟨hadm, hcase⟩).2 z hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inl rfl) hf K hK) hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inl rfl)) hf K hK) hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inr (.inl rfl))) hf K hK) hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inr (.inr rfl))) hf K hK) hz2
  all_goals
    obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hcase
    obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
      ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
        RingHom.ext fun _ => rfl⟩
    obtain ⟨e'⟩ := RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv _ Nat.prime_two hf K
      hK _ hσ
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab' (e.trans e')
      (graphFixedRootGroup_involution_centralizer_oddCore hE6 _ hf K hK σ' hσ) hz2

theorem evenLieInvolutionOddCoreFact_holds :
    EvenLieInvolutionOddCoreFact := by
  intro J _ _ t n f hL x hx
  have hs : IsSimpleGroup J := Timmesfeld.isSimpleGroup_of_lieModel hL
  rw [← oddCore_eq_pPrimeCore_two]
  by_contra hcore
  by_cases hnab : ∃ a b : J, a * b ≠ b * a
  ·
    have hFt : GeneralizedFitting.subgroup J = ⊤ :=
      CatLeaf.generalizedFitting_subgroup_eq_top_of_simple
    have hF : CFSG.generalizedFitting J = GeneralizedFitting.subgroup J :=
      CFSG.generalizedFitting_eq_componentClassification J
    let eG : GeneralizedFitting.subgroup J ≃* J := (MulEquiv.subgroupCongr hFt).trans topEquiv
    have hsimple : IsSimpleGroup (GeneralizedFitting.subgroup J) := eG.isSimpleGroup
    have hnonab : ∃ a b : GeneralizedFitting.subgroup J, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨eG.symm a, eG.symm b, fun h => hab (eG.symm.injective (by
        rw [map_mul, map_mul, h]))⟩
    have hsimple' : IsSimpleGroup (CFSG.generalizedFitting J) := hF ▸ hsimple
    have hnonab' : ∃ a b : CFSG.generalizedFitting J, a * b ≠ b * a := hF ▸ hnonab
    have hadm := admissible_of_lieModel' hL
    have hLG : LieModel (GeneralizedFitting.subgroup J) t n 2 f :=
      LieType.CurtisTits.lieModel_of_mulEquiv eG.symm hL
    rcases hLG with ⟨ht, hcl⟩ | ⟨-, ht, hex⟩ | ⟨-, ht, hrt⟩ | ⟨-, rfl, hsz⟩
    · have hcl' : StatedClassicalModel (CFSG.generalizedFitting J) t n 2 f := hF ▸ hcl
      simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨hlt, -⟩ := UnbalancedCatalog.even_linear_almost_simple_unbalanced_outcome hnonab'
          hcl' ⟨x, hx, hcore⟩
        exact hlt.ne (hF.trans hFt)
      · exact hcore ((UnbalancedCatalog.even_unitary_almost_simple_odd_core_vanishing hnonab'
          hcl').2 x hx)
      · exact hcore ((UnbalancedCatalog.even_symplectic_almost_simple_odd_core_vanishing hnonab'
          hcl').1 x hx)
      · obtain ⟨-, -, -, hp2⟩ := hcl.1
        exact absurd rfl hp2
      · exact hcore ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
          _ (.inl rfl) hcl').2 x hx)
      · exact hcore ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
          _ (.inr rfl) hcl').2 x hx)
    · exact hcore (oddCore_eq_bot_of_exceptional hnonab' ht (hF ▸ hex) hx)
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact absurd hadm.2.2.2.1 (by norm_num)
      · exact Sporadic.Schreier.LargeReeExcl.CTU_catalog_large_Ree_Tits_check J hsimple hnonab _ f
          (.inl rfl) hrt ⟨x, hx, hcore⟩
      · exact Sporadic.Schreier.LargeReeExcl.CTU_catalog_large_Ree_Tits_check J hsimple hnonab _ f
          (.inr rfl) hrt ⟨x, hx, hcore⟩
    · have hsz' : SuzukiModel (CFSG.generalizedFitting J) 2 f := hF ▸ hsz
      exact hcore (UnbalancedGS.catalog_suzuki_almost_simple_odd_core_vanishing hsimple' hnonab'
        hsz' x hx).2.2
  ·
    push Not at hnab
    apply hcore
    set C := centralizer ({x} : Set J) with hC
    set O := (CFSG.oddCore ↥C).map C.subtype with hO
    have hOn : O.Normal := ⟨fun a ha g => by rw [hnab g a, mul_inv_cancel_right]; exact ha⟩
    rcases hs.eq_bot_or_eq_top_of_normal O with h | h
    · exact (map_eq_bot_iff_of_injective _ C.subtype_injective).mp h
    · exfalso
      obtain ⟨o, ho, hox⟩ : x ∈ O := h ▸ mem_top x
      have h2 : orderOf (⟨o, ho⟩ : CFSG.oddCore ↥C) = 2 := by
        rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe, ← hx]
        exact congrArg orderOf hox
      have hodd : Odd (Nat.card ↥(CFSG.oddCore ↥C)) := by
        rw [oddCore_eq_pPrimeCore_two]
        exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
      have h2d : 2 ∣ Nat.card ↥(CFSG.oddCore ↥C) := h2 ▸ orderOf_dvd_natCard _
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2d)

end EvenOddCore

end CFSG.ComponentClassification.HarrisLit.N36
