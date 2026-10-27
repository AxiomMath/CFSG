module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB71Step1
public import CFSG.Dihedral.GorensteinWalter.FieldTransport

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open scoped MatrixGroups

@[expose] def CFDoubleCover : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Nat.card (center Y) = 2 →
    ((∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧ Nonempty (Y ⧸ center Y ≃* alternatingGroup (Fin n))) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (Y ⧸ center Y) .PSL 2 p f) →
    CFSG.pRank 2 Y ≤ 1 ∧
      ((∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧ Nonempty (Y ≃* SL(2, GaloisField p n))) ∨
        Nonempty (Y ⧸ center Y ≃* alternatingGroup (Fin 7)))

noncomputable def oddBarCenterEquiv (Y : Type*) [Group Y] :
    (Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y) ≃* Y ⧸ Open.fusionZStar Y := by
  have hO : Open.fusionOddCore Y = pPrimeCore 2 Y := GSLit.oddCore_eq_pPrimeCore_two Y
  have hle : Open.fusionOddCore Y ≤ Open.fusionZStar Y := fun o ho => by
    show (QuotientGroup.mk o : Y ⧸ Open.fusionOddCore Y) ∈ center _
    rw [(QuotientGroup.eq_one_iff o).mpr ho]
    exact one_mem _
  have hmap : (Open.fusionZStar Y).map (QuotientGroup.mk' (Open.fusionOddCore Y)) =
      center (Y ⧸ Open.fusionOddCore Y) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact (GorensteinWalter.FieldTransport.quotientCenterMulEquiv
      (QuotientGroup.quotientMulEquivOfEq hO.symm)).trans
    ((QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ _ hle))

variable {X : Type} [Group X] [Finite X]

theorem rankOne_witness_of_doubleCover (hCF : CFDoubleCover) (K : Subgroup X)
    (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K)) (hZ : Nat.card (center (K ⧸ pPrimeCore 2 K)) = 2)
    (htype : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
        Nonempty (K ⧸ Open.fusionZStar K ≃* alternatingGroup (Fin n))) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (K ⧸ Open.fusionZStar K) .PSL 2 p f) :
    CFSG.pRank 2 (K ⧸ pPrimeCore 2 K) ≤ 1 ∧ Open.classicalInvolutionWitness K := by
  let e := oddBarCenterEquiv K
  have htype' : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
        Nonempty ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K) ≃*
          alternatingGroup (Fin n))) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) .PSL 2 p f := by
    rcases htype with ⟨n, hn, ⟨φ⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
    · exact .inl ⟨n, hn, ⟨e.trans φ⟩⟩
    · exact .inr ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hL⟩
  obtain ⟨hrank, hwit⟩ := hCF _ hq hZ htype'
  refine ⟨hrank, ?_⟩
  have hO : Open.classicalInvolutionOddCore K = pPrimeCore 2 K :=
    GSLit.oddCore_eq_pPrimeCore_two K
  let f : K ⧸ Open.classicalInvolutionOddCore K ≃* K ⧸ pPrimeCore 2 K :=
    QuotientGroup.quotientMulEquivOfEq hO
  rcases hwit with ⟨p, n, hp, hp2, hn, ⟨φ⟩⟩ | hA7
  · exact .inl ⟨p, n, hp, hp2, hn, ⟨f.trans φ⟩⟩
  · obtain ⟨φ⟩ := hA7
    refine .inr ⟨(UnbalancingLocal.isQuasisimple_open_iff _).mpr
      (LocalCores.isQuasisimple_of_mulEquiv f.symm hq), ?_,
      ⟨(GorensteinWalter.FieldTransport.quotientCenterMulEquiv f).trans φ⟩⟩
    rw [Nat.card_congr (Subgroup.centerCongr f).toEquiv, hZ]

theorem lemma71_step1_of_doubleCover [IsSimpleGroup X] (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hCF : CFDoubleCover)
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (h : Hyp52 X) (hB : Nat.card h.B = 2)
    (h511 : h.B ≤ UnbalancedLayer.coreActionKernel h.V ∧
      ∃ R : Sylow 2 ↥(UnbalancedLayer.coreActionKernel h.V),
        (R : Subgroup _) = h.B.subgroupOf (UnbalancedLayer.coreActionKernel h.V))
    (hcase : (conjugate h.K h.a = h.K ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f ∧
        Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSL 2 p (2 * f)) ∨
      (conjugate h.K h.a ≠ h.K ∧ Nat.card (center (h.K ⧸ pPrimeCore 2 h.K)) = 2 ∧
        ((∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
            Nonempty (h.K ⧸ Open.fusionZStar h.K ≃* alternatingGroup (Fin n))) ∨
          ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
            Blueprint.LieModel (h.K ⧸ Open.fusionZStar h.K) .PSL 2 p f))) :
    ConclusionB1 h.J := by
  refine lemma71_step1 hCI hUc hnonab hz hU h hB h511 (hcase.imp id fun hK => ?_)
  obtain ⟨hKa, hZ, htype⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKW, hKpc⟩ := h.isPComponent_K
  have hq : IsQuasisimple (h.K ⧸ pPrimeCore 2 h.K) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hKW)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hKpc)
  exact ⟨hKa, rankOne_witness_of_doubleCover hCF h.K hq hZ htype⟩

end CFSG.ComponentClassification.GSThmB
