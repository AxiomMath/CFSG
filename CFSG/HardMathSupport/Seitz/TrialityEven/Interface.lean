module

public import CFSG.HardMathSupport.Seitz.TrialityEven.Split

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open TauCeti CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

section Defs


@[expose] def InnerModelGenEvenThree : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (2 ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ f)) →
    ∀ E : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      E ≤ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      RankLE2 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
      ¬ (∃ S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), S ≠ ⊥ ∧ IsPGroup 2 S ∧
        ∀ β ∈ E, S.map β.toMonoidHom = S) →
      PlaneGen E

end Defs


theorem nonempty_catEquiv_graphFixedRootGroup_even {q : PrimePower} (hq : q.p = 2)
    (hv : (LieTypeIndex.trialityD4 q).Valid) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ q.exponent) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ q.exponent)) :
    Nonempty (Cat ⟨.trialityD4 q, hv⟩ ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hqc : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq]
  obtain ⟨eB⟩ := Even.chevalleyBridgesAll.trialityD4 q hv K (by rw [hqc]; exact hK) σ.toRingHom
    (fun x => by rw [hqc]; exact hσ x)
  obtain ⟨-, -, -, -, -, -, -, ⟨eC⟩⟩ :=
    even_triality_exact_automorphism_normal_form q.exponent_pos K hK σ hσ
  exact ⟨eB.symm.trans eC⟩

theorem seitzExcAnisotropicTrialityEvenThreeGe_of_innerModelGen (h : InnerModelGenEvenThree) :
    SeitzExcAnisotropicTrialityEvenThreeGe := by
  rintro ⟨d, hv⟩ p hp hp2 hpc - E hE hcard ⟨hin, -, ⟨hp3, q, rfl, hq, hq2⟩, hrk, hnr⟩
  subst hp3
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hchar := LieTypeIndex.characteristic_trialityD4 q
  have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := hq ▸ hK
  have hσ' : ∀ c, σ c = c ^ (2 ^ q.exponent) := hq ▸ hσ
  have hnr' : ¬ ∃ R : Subgroup (Cat ⟨.trialityD4 q, hv⟩), R ≠ ⊥ ∧ IsPGroup 2 R ∧
      ∀ ε ∈ E, R.map ε.toMonoidHom = R := by
    rw [← hq, ← hchar]
    exact hnr
  rw [← planeGen_map_congr e]
  refine h q.exponent hq2 K hK' σ hσ' _ (isElemAbelian_map_congr e hE)
    (by rw [card_map_congr, hcard]) ?_ (RankLE2.of_mulEquiv e hrk)
    fun hS => hnr' ((CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.no_prime_subgroup_normalized_congr_iff
      e 2 E).2 hS)
  have hle := Subgroup.map_mono (f := (MulAut.congr e).toMonoidHom) hin
  rwa [map_range_conj_congr e] at hle

end CFSG.HardMathSupport.Seitz.TrialityEven
