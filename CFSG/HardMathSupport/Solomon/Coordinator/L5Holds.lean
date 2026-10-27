module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5ClauseC
public import CFSG.HardMathSupport.Solomon.Coordinator.L5LinEven
public import CFSG.HardMathSupport.Solomon.Coordinator.WeakHolds

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem unitary_catalogue_model_stated {S : Type} [Group S] (r : ℕ) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r Q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r Q, hv⟩).Group) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData Q.p Q.exponent K),
      Nonempty (S ≃* primeFormP h (idGram K (r + 1))) ∧
      Nonempty (S ≃* StatedProj (StatedSU (r + 1) (Q.p ^ Q.exponent) K)) := by
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r Q hv e
  obtain ⟨⟨hℓ, hf, -, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData Q.p Q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  exact ⟨K, inferInstance, h, ⟨(eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm⟩,
    ⟨eT⟩⟩

theorem lFiveEpsFiveTwo_holds : LFiveEpsFiveTwo := by
  intro G _ _ hG X hX B hBX hB hrank _ L hL idx hidx he
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  change CFSG.HardMathSupport.Timmesfeld.LocalTwo.IsLpEpsIndex 5 d at hidx
  have hp : Nat.Prime 5 := Nat.prime_five
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    left
    have e' := e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 4 Q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 _))
    have h5 := dvd_card_galoisField_sub_one (by norm_num) Q hQ
    have hK : Nat.card (GaloisField Q.p Q.exponent) = Q.p ^ Q.exponent :=
      GaloisField.card _ _ Q.exponent_pos.ne'
    by_cases hp2 : Q.p = 2
    · have : CharP (GaloisField Q.p Q.exponent) 2 := CharP.congr Q.p hp2
      exact isCompLocallyBalanced_five_projectiveSL_even hBX hB hrank hL Q.exponent_pos
        (by rw [hK, hp2]) h5 e'
    · exact isCompLocallyBalanced_five_projectiveSL hBX hB hrank hL Q.prime_p Q.exponent_pos hK h5
        (by rw [ringChar.eq (GaloisField Q.p Q.exponent) Q.p]; exact hp2) e'
  · subst hd
    obtain ⟨K, _, h, ⟨e'⟩, ⟨eT⟩⟩ := unitary_catalogue_model_stated 4 Q hv e
    have hpq : 5 ∣ Q.p ^ Q.exponent + 1 := by
      rw [← TauCeti.PrimePower.card_def]
      exact Nat.dvd_of_mod_eq_zero hQ
    by_cases hp2 : Q.p = 2
    · by_cases hbal : IsCompLocallyBalanced 5 2 B L
      · exact Or.inl hbal
      · right
        obtain ⟨hsimple, hnabS, -⟩ := isCatalogGroup_quotient_center_barOf hp hG hX hL
        have : Fact (Nat.Prime 5) := ⟨hp⟩
        obtain ⟨eO⟩ := i196_exists_mulEquiv_quot_oPrimeP 5 (H := ↥L) hsimple hnabS
        exact input19_10ClauseC_five_primeFormP_even hBX hB hrank hL h hp2 hpq e'
          ⟨eO.symm.trans eT⟩ hbal
    · left
      have : CharP K Q.p := h.charP
      exact isCompLocallyBalanced_five_primeFormP hBX hB hrank hL h hpq
        (by rw [ringChar.eq K Q.p]; exact hp2) e'

end CFSG.HardMathSupport.Solomon.Coordinator
