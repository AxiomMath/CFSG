module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullThetaAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullThetaTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullInversion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullTheta
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointMotion

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_class_centralizer_le_stabilizer
    {H : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (hs : s ∈ involutionPointClass z) (epsilon : pointRightCosetSpace H)
    (hfix : pointRightCosetMul H epsilon s = epsilon) :
    Subgroup.centralizer ({s} : Set G) ≤ rightCosetStabilizer H epsilon := by
  obtain ⟨gamma, _hgamma, huniq⟩ :=
    (((involution_point_unique_containment_action h.distinguished_mem
      h.distinguished_order).2 h.unique_containment).2.1 s hs)
  intro c hc
  apply (mem_point_right_stabilizer_iff H epsilon c).mpr
  have hcomm : c * s = s * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have htranslated : pointRightCosetMul H (pointRightCosetMul H epsilon c) s =
      pointRightCosetMul H epsilon c := by
    rw [pointRightCosetMul_mul, hcomm, ← pointRightCosetMul_mul, hfix]
  exact (huniq _ htranslated).trans (huniq _ hfix).symm

theorem properHull_theta_class_centralizer_eq_bot
    {H : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (hs : s ∈ involutionPointClass z) (epsilon : pointRightCosetSpace H)
    (hfix : pointRightCosetMul H epsilon s = epsilon)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (D Q : Subgroup G)
    (hQ : IsPGroup q Q) (hQC : Q ≤ minimalLocalFailurePairConfinementTheta p D)
    (hqE : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (D ⊓ rightCosetStabilizer H epsilon))) :
    Q ⊓ Subgroup.centralizer ({s} : Set G) = ⊥ := by
  have hQE := properHull_pGroup_inf_theta_eq_bot p q hp hq D
    (D ⊓ rightCosetStabilizer H epsilon) Q inf_le_left hQ hQC hqE
  apply le_bot_iff.mp
  rw [← hQE]
  exact le_inf inf_le_left (le_inf
    (inf_le_left.trans (hQC.trans (pairConfinement_theta_le p D)))
    (inf_le_right.trans (properHull_class_centralizer_le_stabilizer h hs epsilon hfix)))

theorem properHull_theta_self_commutator_centralizes
    {H : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (hs : s ∈ involutionPointClass z) (epsilon : pointRightCosetSpace H)
    (hfix : pointRightCosetMul H epsilon s = epsilon)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (D X Q : Subgroup G)
    (hQ : IsPGroup q Q) (hQC : Q ≤ minimalLocalFailurePairConfinementTheta p D)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hsQ : s ∈ Subgroup.normalizer (Q : Set G))
    (hqE : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (D ⊓ rightCosetStabilizer H epsilon)))
    (hself : ⁅X, Subgroup.zpowers s⁆ = X) :
    X ≤ Subgroup.centralizer (Q : Set G) ∧
      Q ≤ Subgroup.centralizer (X : Set G) := by
  have hsorder := order_two_of_mem_pointClass h.distinguished_order hs
  have hssq : s * s = 1 := by
    simpa only [hsorder, pow_two] using pow_orderOf_eq_one s
  have hc := properHull_self_commutator_centralizes_inverted X Q s hssq hXQ hsQ
    (properHull_theta_class_centralizer_eq_bot h hs epsilon hfix p q hp hq D Q hQ hQC hqE)
    hself
  refine ⟨hc, ?_⟩
  intro a ha
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hc hx) a ha).symm

theorem properHull_theta_opposite_normalizer_escape
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (X : Subgroup G)
    (hX : IsPGroup p X) (hXE : X ≤ triplePointStabilizer H z beta)
    (hzX : z ∈ Subgroup.normalizer (X : Set G))
    (hself : ⁅X, Subgroup.zpowers z⁆ = X)
    (hqB : q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (pairPointStabilizer H beta)))
    (hqE : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (triplePointStabilizer H z beta))) :
    ∃ Q : Sylow q (minimalLocalFailurePairConfinementTheta p
        (oppositePairStabilizer H z beta)),
      let R := (Q : Subgroup (minimalLocalFailurePairConfinementTheta p
        (oppositePairStabilizer H z beta))).map
          (minimalLocalFailurePairConfinementTheta p
            (oppositePairStabilizer H z beta)).subtype
      R ≠ ⊥ ∧ R ⊓ H = ⊥ ∧ X ≤ Subgroup.centralizer (R : Set G) ∧
        R ≤ Subgroup.centralizer (X : Set G) ∧
        ¬ Subgroup.normalizer (X : Set G) ≤ H := by
  let D := oppositePairStabilizer H z beta
  let E := triplePointStabilizer H z beta
  have hXD : X ≤ D := by
    intro x hx
    exact ⟨(hXE hx).1.2, (hXE hx).2⟩
  have hEeq : D ⊓ rightCosetStabilizer H (rightCosetMk H 1) = E := by
    ext x
    change ((x ∈ rightCosetStabilizer H beta ∧
      x ∈ rightCosetStabilizer H (rightCosetTranslate H beta z)) ∧
      x ∈ rightCosetStabilizer H (rightCosetMk H 1)) ↔
      ((x ∈ rightCosetStabilizer H (rightCosetMk H 1) ∧
        x ∈ rightCosetStabilizer H beta) ∧
        x ∈ rightCosetStabilizer H (rightCosetTranslate H beta z))
    tauto
  have hpaircard := properHull_pair_theta_card_of_double_transitivity H p hdoubly
    (rightCosetMk H 1) beta beta (pointRightCosetMul H beta z)
    hbeta.symm (by
      rw [pointRightCosetMul_eq_translate]
      exact (triple_point_cosets_distinct h hbeta).2.1.symm)
  have hqD : q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p D) := by
    change q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (rightCosetStabilizer H beta ⊓
        rightCosetStabilizer H (rightCosetTranslate H beta z)))
    rw [← pointRightCosetMul_eq_translate, hpaircard]
    exact hqB
  obtain ⟨Q, hRne, hR, hRC, hXR, hzR⟩ :=
    properHull_theta_nontrivial_joint_sylow p q hp hq D X z hX h.distinguished_order
      hzX (hXD.trans Subgroup.le_normalizer)
      (opposite_pair_normalized_by_distinguished h beta) hqD
  let R := (Q : Subgroup (minimalLocalFailurePairConfinementTheta p D)).map
    (minimalLocalFailurePairConfinementTheta p D).subtype
  have hqDbase : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (D ⊓ rightCosetStabilizer H (rightCosetMk H 1))) := by
    rw [hEeq]
    exact hqE
  have hcentral := properHull_theta_self_commutator_centralizes h
    (distinguished_mem_pointClass z) (rightCosetMk H 1)
    ((point_right_base_fixed_iff H z).mpr h.distinguished_mem)
    p q hp hq D X R hR hRC hXR hzR hqDbase hself
  have hRD : R ≤ D := hRC.trans (pairConfinement_theta_le p D)
  have hRE : R ⊓ E = ⊥ :=
    properHull_pGroup_inf_theta_eq_bot p q hp hq D E R
      (hEeq ▸ inf_le_left) hR hRC hqE
  have hRH : R ⊓ H = ⊥ := by
    apply le_bot_iff.mp
    rw [← hRE]
    exact le_inf inf_le_left (by
      rw [← hEeq, rightCosetStabilizer_base]
      exact le_inf (inf_le_left.trans hRD) inf_le_right)
  have hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H := by
    intro hNH
    have hRHle : R ≤ H := hcentral.2.trans
      ((Subgroup.centralizer_le_normalizer (X : Set G)).trans hNH)
    exact hRne (le_bot_iff.mp (hRH ▸ le_inf le_rfl hRHle))
  exact ⟨Q, hRne, hRH, hcentral.1, hcentral.2, hescape⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
