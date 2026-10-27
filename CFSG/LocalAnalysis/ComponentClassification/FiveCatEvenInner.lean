module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Even

open CFSG Subgroup CatLeaf CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem oddCore_eq_bot_of_evenExceptional
    {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnonab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    {τ : StatedLieTag} {f : ℕ} (hτ : τ ∈ chevalleyExceptionalTags)
    (hmodel : ChevalleyExceptionalModel (GeneralizedFitting.subgroup X) τ 2 f) {z : X}
    (hz : orderOf z = 2) : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥ := by
  have hE6 : CatalogueU.EvenE6OuterInvolutionInput :=
    CatalogueU.evenE6OuterInvolutionInput_holds
  have hF : CFSG.generalizedFitting X = GeneralizedFitting.subgroup X :=
    CFSG.generalizedFitting_eq_componentClassification X
  have hsimple' : IsSimpleGroup (CFSG.generalizedFitting X) := hF ▸ hsimple
  have hnonab' : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := hF ▸ hnonab
  have hmodel' : ChevalleyExceptionalModel (CFSG.generalizedFitting X) τ 2 f := hF ▸ hmodel
  obtain ⟨hadm, hcase⟩ := hmodel'
  have hf : 1 ≤ f := hadm.2.1
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (UnbalancedCatalog.even_G2_almost_simple_odd_core_vanishing hnonab'
      ⟨hadm, hcase⟩).2 z hz
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact CatalogueU.oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (CatalogueU.adjointGroup_involution_centralizer_oddCore hE6 (.inl rfl) hf K hK) hz
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact CatalogueU.oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (CatalogueU.adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inl rfl)) hf K hK) hz
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact CatalogueU.oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (CatalogueU.adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inr (.inl rfl))) hf K
        hK) hz
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact CatalogueU.oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (CatalogueU.adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inr (.inr rfl))) hf K
        hK) hz
  all_goals
    obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hcase
    obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
      ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
        RingHom.ext fun _ => rfl⟩
    obtain ⟨e'⟩ := RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv _ Nat.prime_two hf K
      hK _ hσ
    exact CatalogueU.oddCore_centralizer_eq_bot_of_conjModel hnonab' (e.trans e')
      (CatalogueU.graphFixedRootGroup_involution_centralizer_oddCore hE6 _ hf K hK σ' hσ) hz

theorem oddCore_eq_bot_of_evenLie
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {τ : StatedLieTag} {n f : ℕ}
    (hL : Blueprint.LieModel S τ n 2 f) {t : S} (ht : orderOf t = 2) :
    CFSG.oddCore (centralizer ({t} : Set S)) = ⊥ := by
  by_contra hcore
  have hFt : GeneralizedFitting.subgroup S = ⊤ := generalizedFitting_subgroup_eq_top_of_simple
  have hF : CFSG.generalizedFitting S = GeneralizedFitting.subgroup S :=
    CFSG.generalizedFitting_eq_componentClassification S
  let eF : GeneralizedFitting.subgroup S ≃* S := (MulEquiv.subgroupCongr hFt).trans topEquiv
  have hsimple : IsSimpleGroup (GeneralizedFitting.subgroup S) := eF.isSimpleGroup
  have hnab : ∃ a b : GeneralizedFitting.subgroup S, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eF.symm x, eF.symm y, fun h => hxy (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hadm : StatedLieAdmissible τ n 2 f := hL.admissible
  have hmodel : Blueprint.LieModel (GeneralizedFitting.subgroup S) τ n 2 f :=
    Blueprint.LieModel.of_mulEquiv eF.symm hL
  have hsimple' : IsSimpleGroup (CFSG.generalizedFitting S) := hF ▸ hsimple
  have hnonab' : ∃ a b : CFSG.generalizedFitting S, a * b ≠ b * a := hF ▸ hnab
  have hlt : ¬ CFSG.generalizedFitting S < ⊤ := by
    rw [hF, hFt]
    exact lt_irrefl _
  have hz : ∃ z : S, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set S)) ≠ ⊥ :=
    ⟨t, ht, hcore⟩
  rcases hmodel with ⟨hτ, hcl⟩ | ⟨-, hτ, hex⟩ | ⟨-, hτ, hrt⟩ | ⟨-, rfl, hsz⟩
  · have hcl' : StatedClassicalModel (CFSG.generalizedFitting S) τ n 2 f := hF ▸ hcl
    simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hlt (UnbalancedCatalog.even_linear_almost_simple_unbalanced_outcome hnonab' hcl'
        hz).1
    · exact hcore ((UnbalancedCatalog.even_unitary_almost_simple_odd_core_vanishing hnonab'
        hcl').2 t ht)
    · exact hcore ((UnbalancedCatalog.even_symplectic_almost_simple_odd_core_vanishing hnonab'
        hcl').1 t ht)
    · obtain ⟨-, -, -, hp2⟩ := hcl.1
      exact absurd rfl hp2
    · exact hcore ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
        _ (.inl rfl) hcl').2 t ht)
    · exact hcore ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
        _ (.inr rfl) hcl').2 t ht)
  · exact hcore (oddCore_eq_bot_of_evenExceptional hsimple hnab hτ hex ht)
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl
    · exact absurd hadm.2.2.2.1 (by norm_num)
    · exact Sporadic.Schreier.LargeReeExcl.CTU_catalog_large_Ree_Tits_check S hsimple hnab _ f
        (.inl rfl) hrt hz
    · exact Sporadic.Schreier.LargeReeExcl.CTU_catalog_large_Ree_Tits_check S hsimple hnab _ f
        (.inr rfl) hrt hz
  · have hsz' : SuzukiModel (CFSG.generalizedFitting S) 2 f := hF ▸ hsz
    exact hcore (UnbalancedGS.catalog_suzuki_almost_simple_odd_core_vanishing hsimple' hnonab'
      hsz' t ht).2.2

theorem evenFiveInner
    (τ : StatedLieTag) :
    EvenFiveInner τ := by
  intro S _ _ _ hna n f hL t ht P hPc
  have hcore : CFSG.oddCore (centralizer ({t} : Set S)) = ⊥ := oddCore_eq_bot_of_evenLie hna hL ht
  have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
  exact involutionCentralizersComponentFree_of_evenLieType ⟨τ, n, f, hL.admissible, hL⟩ t ht _
    ⟨hq, hPc.choose_spec.2.1⟩

end CFSG.ComponentClassification.SolMax.FiveCat.Even
