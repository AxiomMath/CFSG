module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.ClassicalInvolution.Orders.OddLieType
public import CFSG.Dihedral.GorensteinWalter.FieldTransport

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem not_uOutcome_of_order_form {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnotLie : ∀ p : ℕ, p.Prime → p ≠ 2 → Nat.card X ∉ Open.lieOrdersChar p)
    (hnotAlt : ∀ n : ℕ, 7 ≤ n → n % 4 = 3 → IsEmpty (X ≃* alternatingGroup (Fin n))) :
    ¬ OutcomeLocal.UOutcome X := by
  have htop := generalizedFitting_eq_top_of_simple (X := X)
  let e : GeneralizedFitting.subgroup X ≃* X := generalizedFittingEquivOfSimple
  rintro (h | ⟨n, hn, h7, ⟨eA⟩, h1⟩ | ⟨-, hlt⟩)
  · obtain ⟨p, hp, hp2, hmem⟩ := ClassicalInvolution.card_mem_lieOrdersChar_of_oddLieType h
    rw [Nat.card_congr e.toEquiv] at hmem
    exact hnotLie p hp hp2 hmem
  · have h3 : n % 4 = 3 := by
      have hn1 : n % 4 ≠ 1 := fun h => (h1 h).ne htop
      obtain ⟨k, rfl⟩ := hn
      omega
    exact (hnotAlt n h7 h3).false (e.symm.trans eA)
  · exact hlt.ne htop

theorem nonempty_mulEquiv_psl_of_lieModel {G : Type} [Group G] {p f : ℕ} [Fact p.Prime]
    (h : Blueprint.LieModel G .PSL 2 p f) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_psl_two h
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField p f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p f (by omega)]
  exact ⟨e.trans ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (GorensteinWalter.FieldTransport.projectiveSpecialLinearGroupMulEquiv
      (FiniteField.ringEquivOfCardEq hcard)))⟩

open scoped MatrixGroups in
theorem cl_lit_gilman_solomon_tauCeti_of_inputs (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGS : GriessSolomonInput) (hB : TheoremBBoundedInput)
    (hH : HarrisInput) (hGF : GloballyFirstRankTwoInput)
    (hCat : CFSG.Assembly.CatalogImp Assembly.InCatalog Blueprint.Catalog) :
    ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
      (∃ a b : X, a * b ≠ b * a) → Open.IsKProper X →
      (∃ z : X, orderOf z = 2 ∧ Open.fusionOddCore (Subgroup.centralizer ({z} : Set X)) ≠ ⊥) →
      (∀ p : ℕ, p.Prime → p ≠ 2 → Nat.card X ∉ Open.lieOrdersChar p) →
      (∀ n : ℕ, 7 ≤ n → n % 4 = 3 → IsEmpty (X ≃* alternatingGroup (Fin n))) →
      (∃ (a b : X) (J : Subgroup X), Open.fusionUnbalancingTriple a b J) →
      ∃ (x y : X) (L : Subgroup X),
        Open.fusionMaximalUnbalancingTriple x y L ∧ Open.fusionMaximalComponent L ∧
        ((Nonempty (L ⧸ Open.fusionOddCore L ≃* alternatingGroup (Fin 7)) ∨
            ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
              Nonempty (L ⧸ Open.fusionOddCore L ≃* PSL(2, GaloisField p f))) ∨
          (Nonempty (L ⧸ Open.fusionOddCore L ≃* Open.fusionHe) ∨
            Nonempty (L ⧸ Open.fusionZStar L ≃* PSL(3, GaloisField 2 2)))) := by
  intro X _ _ _ hnonab hK hunbal hnotLie hnotAlt htriple
  obtain ⟨x, y, L, h1, h2, h3⟩ := exists_fusion_maximal_component_of_inputs hTB hSA hGS hB hH
    hGF hCat X hnonab hK hunbal (not_uOutcome_of_order_form hnotLie hnotAlt) htriple
  refine ⟨x, y, L, h1, h2, Or.inl (h3.imp_right ?_)⟩
  rintro ⟨p, f, hp, hp2, hf, h5, hLieL⟩
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨p, f, inferInstance, hp2, hf, h5, nonempty_mulEquiv_psl_of_lieModel hLieL⟩

end CFSG.ComponentClassification.GSLit
