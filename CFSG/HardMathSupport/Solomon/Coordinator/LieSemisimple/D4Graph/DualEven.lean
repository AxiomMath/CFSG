module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.ClassOne
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.ResidualLayer
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofCent
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEvenDesc

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec8 CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


theorem perfectInLayer_fieldActor_two {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) : PerfectInLayer (fieldActor (t := TwistTag.D4) σ σ) := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨e⟩ := KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σ) hK2
  have hfix : fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) =
      (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  exact perfectInLayer_of_mulEquiv_g2 _ ((MulEquiv.subgroupCongr hfix).trans e)

theorem outer_three_even {f : ℕ} (hf : 1 ≤ f)
    {K₃ : Type} [Field K₃] [Finite K₃] (hK₃ : Nat.card K₃ = (2 ^ f) ^ 3) (Fr : K₃ ≃+* K₃)
    (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    PerfectInLayer φ := by
  have hG2 := perfectInLayer_fieldActor_two hf Fr hK₃ hFr
  rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK₃ hFr hφ3 hφ with
    ⟨β, hβ | hβ⟩ | he₂
  · rw [hβ]
    exact perfectInLayer_conj β _ hG2
  · rw [hβ]
    exact perfectInLayer_conj β _ ((perfectInLayer_inv_iff _).2 hG2)
  · obtain ⟨e₂⟩ := he₂
    have hfixφ : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    let ef : ↥(fixSubgroup φ) ≃* ↥(Sec4.autFix φ) := MulEquiv.subgroupCongr hfixφ
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0Even_holds f hfe hf K₃ Fr hK₃ hFr
      have hPi : Sec4.PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
      have hf2 : 2 ≤ f := by
        obtain ⟨k, hk⟩ := hfe
        omega
      have h2 : 2 < 2 ^ f :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact perfectInLayer_of_perfectResidual φ
        (Item8KFacts2Proof.perfectResidual_eq_bot_or_of_mulEquiv (ef.trans (e₂.trans e₃))
          (Item8KFacts2Proof.perfectResidual_projImage_glPi_eq_bot_or_isQuasisimple hPi
            (fun _ => h2)))
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds f hfo K₃ Fr hK₃ hFr
      have hPi : Sec4.PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
      exact perfectInLayer_of_perfectResidual φ
        (Item8KFacts2Proof.perfectResidual_eq_bot_or_of_mulEquiv (ef.trans (e₂.trans e₃))
          (Item8KFacts2Proof.perfectResidual_projImage_glPi_eq_bot_or_isQuasisimple hPi
            (fun h => absurd h (by decide))))

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
