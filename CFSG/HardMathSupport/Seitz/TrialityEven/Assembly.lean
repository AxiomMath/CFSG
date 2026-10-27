module

public import CFSG.HardMathSupport.Seitz.TrialityEven.Split
public import CFSG.HardMathSupport.Seitz.TrialityEven.Interface
public import CFSG.HardMathSupport.Seitz.TrialityEven.ToralQ1All
public import CFSG.HardMathSupport.Seitz.TrialityEven.MinusDichotomyAll
public import CFSG.HardMathSupport.Seitz.TrialityEven.FrameRowsEven
public import CFSG.HardMathSupport.Seitz.TrialityEven.TwistedEven
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.InnerPlanePullback

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (SeitzExcAnisotropicTrialityEvenThree)


theorem innerModelGenEvenThree_of_tori (h1 : PhiFramePlaneGenEvenThree 1)
    (h2 : PhiFramePlaneGenEvenThree (-1)) :
    InnerModelGenEvenThree := by
  have hT := twistedTorusPlaneGenEvenThree
  intro f hf K _ _ hK σ hσ E hE hcard hin _ hno
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form (by omega) K hK σ hσ
  have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mulAut_conj_injective_of_center_bot hZ
  refine CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.planeGen_of_closure_centralizers hinj E hin
    ?_
  set F := E.comap (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hFdef
  have hFea : CFSG.IsElementaryAbelian 3 F :=
    CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.isElementaryAbelian_comap_conj hinj hE
  have hFcard : Nat.card F = 3 ^ 2 := by
    rw [CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.card_comap_conj hinj hin, hcard]
  have hanis := CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.not_le_normalizer_of_no_invariant
    hin hno
  have htrans : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
        ∃ x ∈ F.map (β⁻¹).toMonoidHom, x ≠ 1 ∧ k * x = x * k} = ⊤ →
      Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
        ∃ x ∈ F, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
    intro β h
    rw [CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.closure_centralizers_map_mulAut,
      ← Subgroup.map_top_of_surjective (β⁻¹).toMonoidHom (β⁻¹).surjective] at h
    exact Subgroup.map_injective (β⁻¹).injective h
  have hmapea : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian 3 (F.map (β⁻¹).toMonoidHom) := fun β =>
    CFSG.IsElementaryAbelian.map _
  have hmapcard : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Nat.card (F.map (β⁻¹).toMonoidHom) = 3 ^ 2 := fun β => by
    rw [Subgroup.card_map_of_injective (β⁻¹).injective, hFcard]
  have hq3 : ¬ 3 ∣ 2 ^ f := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hK3 : Nat.card K = 2 ^ (f * 3) := by rw [hK, ← pow_mul]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  rcases (by omega : (2 ^ f) % 3 = 1 ∨ (2 ^ f) % 3 = 2) with hq | hq
  · obtain ⟨β, hFr, -⟩ := d4_toral_q1_all (by omega) hq K hK σ hσ F hFea hFcard hanis
    refine htrans β (h1 f hf K hK σ hσ ?_ _ (hmapea β) (hmapcard β) hFr)
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = 3 * k + 1 := ⟨2 ^ f / 3, by omega⟩
    rw [hk]
    exact ⟨3 * k ^ 2 + 3 * k + 1, by push_cast; ring⟩
  · rcases d4Minus_plane_dichotomy_all Nat.prime_two (by omega) hq K hK σ hσ F hFea hFcard with
      hT0 | ⟨β, hFr, -⟩
    · exact hT f hf K hK σ hσ (by omega) F hFea hFcard hT0
    · refine htrans β (h2 f hf K hK σ hσ ?_ _ (hmapea β) (hmapcard β) hFr)
      obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = 3 * k + 2 := ⟨2 ^ f / 3, by omega⟩
      rw [hk]
      exact ⟨3 * k ^ 2 + 3 * k + 1, by push_cast; ring⟩

theorem seitzExcAnisotropicTrialityEvenThreeGe_proved : SeitzExcAnisotropicTrialityEvenThreeGe :=
  seitzExcAnisotropicTrialityEvenThreeGe_of_innerModelGen
    (innerModelGenEvenThree_of_tori (phiFramePlaneGenEvenThree_pm (Or.inl rfl))
      (phiFramePlaneGenEvenThree_pm (Or.inr rfl)))

theorem seitzExcAnisotropicTrialityEvenThree_of_leaves (h2 : TrialityTwoThreePlanes) :
    SeitzExcAnisotropicTrialityEvenThree :=
  seitzExcAnisotropicTrialityEvenThree_of_split h2 seitzExcAnisotropicTrialityEvenThreeGe_proved

end CFSG.HardMathSupport.Seitz.TrialityEven
