module

public import CFSG.HardMathSupport.Dickson.Bal207.FCBlock
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

theorem uni_isLieQuot_of_primeFormP {Y : Type} [Group Y] {k m : ℕ} {E : Type} [Field E]
    (h₀ : UnitaryFieldData 2 k E) (hk : k = 1 ∨ k = 3) (hm : 4 ≤ m) (h3 : ¬ 3 ∣ m)
    (e : (Y ⧸ Subgroup.center Y) ≃* primeFormP h₀ (oneGram E m)) :
    IsLieQuot Y (fun d => Bal207Index 3 d ∧ ¬ IsG2EightIndex d) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h₀.finite
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  let q : TauCeti.PrimePower := ⟨2, k, Nat.prime_two, by omega⟩
  have hv : (TauCeti.LieTypeIndex.twistedA r q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    exact ⟨by omega, fun hr => by omega⟩
  obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  haveI : Fintype K₀ := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hKK : Fintype.card E = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, h₀.card_eq_sq]
  let eK : E ≃+* K₀ := FiniteField.ringEquivOfCardEq hKK
  let eP := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK (r + 1) (2 ^ k)
  let eU : primeFormP h₀ (oneGram E (r + 1)) ≃* StatedProj (StatedSU (r + 1) (2 ^ k) E) :=
    (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h₀ (r + 1)).symm.trans
      (unitaryPSUEquiv h₀ (by omega))
  have hq : IsTwoPow q 1 ∨ IsTwoPow q 3 := by
    rcases hk with hk | hk
    · exact Or.inl ⟨rfl, hk⟩
    · exact Or.inr ⟨rfl, hk⟩
  exact ⟨⟨.twistedA r q, hv⟩, ⟨⟨rfl, Or.inl ⟨hq, h3⟩⟩, fun h => h⟩,
    ⟨((e.trans eU).trans eP).trans e₀.symm⟩⟩

theorem uni_isBalSmall_of_block {X : Type} [Group X] {K J : Subgroup X} {S : Type} [Group S]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) (hJK : J ≤ K) (hJp : commutator ↥J = ⊤)
    {f m : ℕ} {E : Type} [Field E] (h : UnitaryFieldData 2 f E) (hf : f = 3) (hm : m = 2)
    {ι : ↥(primeFormUnitary h (oneGram E m)) →* S} (hι : Function.Injective ι)
    (hJι : (J.comap K.subtype).map (uniMap e) = (blockSU h m).map ι) : IsBalSmall J := by
  subst hf hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.finite
  haveI := h.charP
  obtain ⟨eS⟩ := CFSG.ComponentClassification.RankTwoClassical.nonempty_SL2_equiv_statedSU_two
    (K := E) (f := 3) h.card_eq_sq
  let φ : ↥J →* Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield E 2 3) :=
    (eS.symm.toMonoidHom.comp
      (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 2)).symm.toMonoidHom).comp
        (blockPre e h hJK hι hJι)
  have hφ : Function.Surjective φ :=
    (eS.symm.surjective.comp
      (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 2)).symm.surjective).comp
        ((blockEquiv e h hι hJι).surjective.comp (uniRestr_surjective e hJK))
  have hker : φ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    apply ker_uniRestr_le_center e hJK
    have hj' : eS.symm ((MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 2)).symm
        (blockEquiv e h hι hJι (uniRestr e hJK j))) = 1 := hj
    rw [MonoidHom.mem_ker]
    rwa [map_eq_one_iff _ eS.symm.injective,
      map_eq_one_iff _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 2)).symm.injective,
      map_eq_one_iff _ (blockEquiv e h hι hJι).injective] at hj'
  obtain ⟨eJ⟩ := LieComp.nonempty_centralQuotient_mulEquiv hJp φ hφ hker
  have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield E 2 3) = 2 ^ 3 :=
    CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField
    (CFSG.LieType.Steinberg.fixedSubfield E 2 3) 2 3 (by norm_num) hF
  let eP := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  exact Or.inr (Or.inr ⟨⟨.A 1 q, hv⟩, ⟨rfl, rfl, rfl⟩, ⟨eJ.trans (eP.trans eC.symm)⟩⟩)

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
