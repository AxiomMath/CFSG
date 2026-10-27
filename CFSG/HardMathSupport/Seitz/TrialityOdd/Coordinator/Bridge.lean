module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Interface
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.NoRSubgroupTransport
public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.LieType.SeitzGeneration.ExcPrimeSplit
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

theorem exists_cat_model_trialityD4_odd {q : PrimePower} (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hq : q.p ≠ 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (q.p ^ q.exponent) ^ 3 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
      Nonempty (Cat ⟨.trialityD4 q, hv⟩ ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  exists_mulEquiv_graphFixedRootGroup_card .D4 q.prime_p q.exponent_pos
    (twistedModel_of_bridge Twisted.twistedBridge_trialityD4 q hv hq (by decide) (MulEquiv.refl _))

theorem seitzExcAnisotropicForAt_of_innerModelGen {Q : ℕ → Prop} (h : InnerModelGen Q) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d p => Q p ∧ ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) := by
  rintro ⟨d, hv⟩ p hp hp2 hpc - E hE hcard ⟨hin, -, ⟨hQ, q, rfl, hq⟩, hrk, hnr⟩
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_cat_model_trialityD4_odd hv hq
  have hchar := LieTypeIndex.characteristic_trialityD4 q
  have hpℓ : p ≠ q.p := by rw [← hchar]; exact hpc
  have hnr' : ¬ ∃ R : Subgroup (Cat ⟨.trialityD4 q, hv⟩), R ≠ ⊥ ∧ IsPGroup q.p R ∧
      ∀ ε ∈ E, R.map ε.toMonoidHom = R := by
    rw [← hchar]; exact hnr
  rw [← planeGen_map_congr e]
  refine h q.p q.exponent q.prime_p hq q.exponent_pos K hK σ hσ p hp hp2 hpℓ hQ _
    (isElemAbelian_map_congr e hE) (by rw [card_map_congr, hcard]) ?_ (RankLE2.of_mulEquiv e hrk)
    fun hS => hnr' ((Proving.no_prime_subgroup_normalized_congr_iff e q.p E).2 hS)
  have hle := Subgroup.map_mono (f := (MulAut.congr e).toMonoidHom) hin
  rwa [map_range_conj_congr e] at hle

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
