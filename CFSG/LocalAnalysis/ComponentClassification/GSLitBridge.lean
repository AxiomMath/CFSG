module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.Assembly.CatalogTransport
import CFSG.Adapters.WholeGroupLayer
import CFSG.Models.Transport

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem generalizedFitting_eq_top_of_simple {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] :
    GeneralizedFitting.subgroup X = ⊤ :=
  (CFSG.generalizedFitting_eq_componentClassification X).symm.trans
    (CFSG.Adapters.generalizedFitting_eq_top_of_isSimpleGroup X)

noncomputable def generalizedFittingEquivOfSimple {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] : GeneralizedFitting.subgroup X ≃* X :=
  (MulEquiv.subgroupCongr generalizedFitting_eq_top_of_simple).trans Subgroup.topEquiv

theorem models_oddLieType_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : Models.OddLieType H) : Models.OddLieType G :=
  Models.OddLieType.of_mulEquiv e.symm h

theorem not_uOutcome_of_not_models
    (hLie : ∀ (X : Type) [Group X], Blueprint.OddLieType X → Models.OddLieType X)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnot : ¬ (Models.OddLieType X ∨
      ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (X ≃* alternatingGroup (Fin n)))) :
    ¬ OutcomeLocal.UOutcome X := by
  have htop := generalizedFitting_eq_top_of_simple (X := X)
  let e : GeneralizedFitting.subgroup X ≃* X := generalizedFittingEquivOfSimple
  rintro (h | ⟨n, hn, h7, ⟨eA⟩, h1⟩ | ⟨-, hlt⟩)
  · exact hnot (.inl (models_oddLieType_of_mulEquiv e.symm (hLie _ h)))
  · have h3 : n % 4 = 3 := by
      have hn1 : n % 4 ≠ 1 := fun h => (h1 h).ne htop
      obtain ⟨k, rfl⟩ := hn
      omega
    exact hnot (.inr ⟨n, h7, h3, ⟨e.symm.trans eA⟩⟩)
  · exact hlt.ne htop

theorem fusionOddCore_eq_oddCore (H : Type*) [Group H] : Open.fusionOddCore H = oddCore H := by
  rw [oddCore_eq_pPrimeCore_two, UnbalancingLocal.fusionOddCore_eq_pPrimeCore]

theorem exists_fusion_maximal_component_of_inputs (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGS : GriessSolomonInput) (hB : TheoremBBoundedInput)
    (hH : HarrisInput) (hGF : GloballyFirstRankTwoInput)
    (hCat : CFSG.Assembly.CatalogImp Assembly.InCatalog Blueprint.Catalog)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Open.IsKProper X)
    (hunbal : ∃ z : X, orderOf z = 2 ∧ Open.fusionOddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (htriple : ∃ (a b : X) (J : Subgroup X), Open.fusionUnbalancingTriple a b J) :
    ∃ (x y : X) (L : Subgroup X), Open.fusionMaximalUnbalancingTriple x y L ∧
      Open.fusionMaximalComponent L ∧
      (Nonempty (L ⧸ Open.fusionOddCore L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (L ⧸ Open.fusionOddCore L) .PSL 2 p f) := by
  have hK0 := CatalogueKProper.open_isKProper_iff.mp hK
  have hK' : Assembly.KProper Blueprint.Catalog X := Assembly.KProper.of_catalogImp hCat hK0
  have hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥ := by
    obtain ⟨z, hz, hne⟩ := hunbal
    exact ⟨z, hz, by rwa [← fusionOddCore_eq_oddCore]⟩
  have htriple' : ∃ (a b : X) (J : Subgroup X), GSUnbalancingTriple a b J := by
    obtain ⟨a, b, J, h⟩ := htriple
    exact ⟨a, b, J, fusionUnbalancingTriple_iff.1 h⟩
  obtain ⟨x, y, L, h1, h2, h3⟩ :=
    exists_maximal_component_of_inputs hTB hSA hGS hB hH hGF X hnonab hK' hz hU htriple'
  refine ⟨x, y, L, fusionMaximalUnbalancingTriple_iff.2 h1, fusionMaximalComponent_iff.2 h2, ?_⟩
  let q : L ⧸ Open.fusionOddCore L ≃* L ⧸ pPrimeCore 2 L :=
    QuotientGroup.quotientMulEquivOfEq (UnbalancingLocal.fusionOddCore_eq_pPrimeCore L)
  rcases h3 with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, h5, ⟨ht, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩
  · exact Or.inl ⟨q.trans e7⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, h5,
      Or.inl ⟨ht, SectionRank.statedClassicalModel_of_mulEquiv q hm⟩⟩
  all_goals exact absurd h0 (by norm_num)

theorem cl_lit_gilman_solomon_models_of_inputs (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGS : GriessSolomonInput) (hB : TheoremBBoundedInput)
    (hH : HarrisInput) (hGF : GloballyFirstRankTwoInput)
    (hCat : CFSG.Assembly.CatalogImp Assembly.InCatalog Blueprint.Catalog)
    (hLie : ∀ (X : Type) [Group X], Blueprint.OddLieType X → Models.OddLieType X) :
    ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
      (∃ a b : X, a * b ≠ b * a) → Open.IsKProper X →
      (∃ z : X, orderOf z = 2 ∧ Open.fusionOddCore (Subgroup.centralizer ({z} : Set X)) ≠ ⊥) →
      ¬ (Models.OddLieType X ∨
        ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) →
      (∃ (a b : X) (J : Subgroup X), Open.fusionUnbalancingTriple a b J) →
      ∃ (x y : X) (L : Subgroup X), Open.fusionMaximalUnbalancingTriple x y L ∧
        Open.fusionMaximalComponent L ∧
        ((Nonempty (L ⧸ Open.fusionOddCore L ≃* alternatingGroup (Fin 7)) ∨
          ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
            Models.LieModel (L ⧸ Open.fusionOddCore L) .PSL 2 p f) ∨
         (Blueprint.NativeSporadic.IsSporadic (L ⧸ Open.fusionOddCore L) .He ∨
           Models.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2)) := by
  intro X _ _ _ hnonab hK hunbal hnot htriple
  obtain ⟨x, y, L, h1, h2, h3⟩ := exists_fusion_maximal_component_of_inputs hTB hSA hGS hB hH
    hGF hCat X hnonab hK hunbal (not_uOutcome_of_not_models hLie hnot) htriple
  refine ⟨x, y, L, h1, h2, Or.inl (h3.imp_right ?_)⟩
  rintro ⟨p, f, hp, hp2, hf, h5, hLieL⟩
  have hm := statedClassicalModel_of_lieModel_psl_two hLieL
  exact ⟨p, f, hp, hp2, hf, h5, hm.1, Or.inl hm⟩

end CFSG.ComponentClassification.GSLit

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr in
theorem cl_lit_gilman_solomon_native_of_inputs
    (hTB : ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGS : GriessSolomonInput) (hB : TheoremBBoundedInput)
    (hH : HarrisInput) (hGF : GloballyFirstRankTwoInput) :
    ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
      (∃ a b : X, a * b ≠ b * a) → Assembly.KProper Blueprint.Catalog X →
      (∃ z : X, orderOf z = 2 ∧ oddCore (Subgroup.centralizer ({z} : Set X)) ≠ ⊥) →
      ¬ OutcomeLocal.UOutcome X →
      (∃ (a b : X) (J : Subgroup X), GSUnbalancingTriple a b J) →
      ∃ (x y : X) (L : Subgroup X), GSMaximalUnbalancingTriple x y L ∧
        GSMaximalComponent L ∧
        ((Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
          ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
            Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) ∨
         (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
           Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2)) := by
  intro X _ _ _ hnonab hK hunbal hnotOutcome htriple
  exact cl_lit_gilman_solomon_of_inputs hTB hSA hGS hB hH hGF
    X hnonab hK hunbal hnotOutcome htriple

end CFSG.ComponentClassification.GSLit
