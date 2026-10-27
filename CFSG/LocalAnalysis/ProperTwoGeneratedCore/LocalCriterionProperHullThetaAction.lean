module

public import CFSG.LocalAnalysis.SignalizerFunctor.JointInvariantSylow
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementTheta

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.ShultStronglyClosedTI
open CFSG.SignalizerFunctor.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_theta_joint_invariant_sylow
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (D X V : Subgroup G) (s : G)
    (hX : IsPGroup p X) (hs : orderOf s = 2)
    (hsX : s ∈ Subgroup.normalizer (X : Set G))
    (hXD : X ≤ Subgroup.normalizer (D : Set G))
    (hsD : s ∈ Subgroup.normalizer (D : Set G))
    (hV : IsPGroup q V) (hVC : V ≤ minimalLocalFailurePairConfinementTheta p D)
    (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hsV : s ∈ Subgroup.normalizer (V : Set G)) :
    ∃ Q : Sylow q (minimalLocalFailurePairConfinementTheta p D),
      V ≤ (Q : Subgroup (minimalLocalFailurePairConfinementTheta p D)).map
        (minimalLocalFailurePairConfinementTheta p D).subtype ∧
      X ≤ Subgroup.normalizer
        (((Q : Subgroup (minimalLocalFailurePairConfinementTheta p D)).map
          (minimalLocalFailurePairConfinementTheta p D).subtype : Subgroup G) : Set G) ∧
      s ∈ Subgroup.normalizer
        (((Q : Subgroup (minimalLocalFailurePairConfinementTheta p D)).map
          (minimalLocalFailurePairConfinementTheta p D).subtype : Subgroup G) : Set G) := by
  let C := minimalLocalFailurePairConfinementTheta p D
  let Z := Subgroup.zpowers s
  have hZ : IsPGroup 2 Z := IsPGroup.of_card
    ((Nat.card_zpowers s).trans hs |>.trans (pow_one 2).symm)
  obtain ⟨hodd, hcop⟩ := pairConfinement_theta_order p hp D
  have hXnorm : X ≤ Subgroup.normalizer (C : Set G) :=
    hXD.trans (pairConfinement_theta_normalizer p D)
  have hsC : s ∈ Subgroup.normalizer (C : Set G) :=
    pairConfinement_theta_normalizer p D hsD
  obtain ⟨Q, hVQ, hZQ, hXQ⟩ := jointly_normalized_sylow_containing
    2 p q Nat.prime_two hp hq Z X C V hZ hX
    (Subgroup.zpowers_le.mpr hsX) (CFSG.FeitThompson.isSolvable_of_odd_natCard C hodd)
    hodd.coprime_two_left hcop
    (Subgroup.zpowers_le.mpr hsC) hXnorm hVC hV
    (Subgroup.zpowers_le.mpr hsV) hXV
  exact ⟨Q, hVQ, hXQ, hZQ (Subgroup.mem_zpowers s)⟩

theorem properHull_theta_nontrivial_joint_sylow
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (D X : Subgroup G) (s : G)
    (hX : IsPGroup p X) (hs : orderOf s = 2)
    (hsX : s ∈ Subgroup.normalizer (X : Set G))
    (hXD : X ≤ Subgroup.normalizer (D : Set G))
    (hsD : s ∈ Subgroup.normalizer (D : Set G))
    (hqC : q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p D)) :
    ∃ Q : Sylow q (minimalLocalFailurePairConfinementTheta p D),
      let R := (Q : Subgroup (minimalLocalFailurePairConfinementTheta p D)).map
        (minimalLocalFailurePairConfinementTheta p D).subtype
      R ≠ ⊥ ∧ IsPGroup q R ∧ R ≤ minimalLocalFailurePairConfinementTheta p D ∧
        X ≤ Subgroup.normalizer (R : Set G) ∧ s ∈ Subgroup.normalizer (R : Set G) := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, _hbot, hXQ, hsQ⟩ := properHull_theta_joint_invariant_sylow
    p q hp hq D X ⊥ s hX hs hsX hXD hsD IsPGroup.of_bot bot_le
    (Subgroup.le_normalizer_of_normal (H := (⊥ : Subgroup G)))
    (Subgroup.le_normalizer_of_normal (H := (⊥ : Subgroup G)) (Subgroup.mem_zpowers s))
  have hne : (Q : Subgroup (minimalLocalFailurePairConfinementTheta p D)).map
      (minimalLocalFailurePairConfinementTheta p D).subtype ≠ ⊥ := by
    intro heq
    have hcard := Q.dvd_card_of_dvd_card hqC
    have hmapcard : Nat.card ((Q : Subgroup (minimalLocalFailurePairConfinementTheta p D)).map
        (minimalLocalFailurePairConfinementTheta p D).subtype) = Nat.card Q :=
      Subgroup.card_map_of_injective (minimalLocalFailurePairConfinementTheta p D).subtype_injective
    rw [← hmapcard, heq, Subgroup.card_bot] at hcard
    exact hq.not_dvd_one hcard
  exact ⟨Q, hne, Q.isPGroup'.map _, Subgroup.map_subtype_le _, hXQ, hsQ⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
