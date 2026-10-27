module

public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizer

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

section Helpers


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem titsAct_zOne_smul_43 :
    F4.fixedOrbitElement ⟨0, by decide⟩ • orbitCertRoot F4.tag 43 = orbitCertRoot F4.tag 44 := by
  rw [fixedOrbitElement_smul]
  decide +kernel

theorem titsAct_zOne_smul_46 :
    F4.fixedOrbitElement ⟨0, by decide⟩ • orbitCertRoot F4.tag 46 = orbitCertRoot F4.tag 47 := by
  rw [fixedOrbitElement_smul]
  decide +kernel

theorem titsAct_isRoot_43 : IsRoot F4.tag (orbitCertRoot F4.tag 43) := by
  obtain ⟨-, -, -, -, -, -, ⟨-, -, h2, -⟩, -⟩ := blockRoots_eq_orbitCertRoot
  rw [← h2]
  exact CFSG.LieType.Ree.LargeReeCover.isRoot_fourRoot 2 2

theorem titsAct_isRoot_46 : IsRoot F4.tag (orbitCertRoot F4.tag 46) := by
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, h3⟩, -⟩ := blockRoots_eq_orbitCertRoot
  rw [← h3]
  exact CFSG.LieType.Ree.LargeReeCover.isRoot_fourRoot 2 3

theorem titsAct_conj_43 :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) *
        sylowX K 43 1 *
      (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹ =
      sylowX K 44 1 := by
  have h := canonicalRep_mul_pinnedX_mul_inv_of_two (F4_two_eq_zero (K := K))
    (F4.fixedOrbitElement ⟨0, by decide⟩) titsAct_isRoot_43 (1 : K)
  rw [titsAct_zOne_smul_43] at h
  exact h

theorem titsAct_conj_46 :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) *
        sylowX K 46 1 *
      (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹ =
      sylowX K 47 1 := by
  have h := canonicalRep_mul_pinnedX_mul_inv_of_two (F4_two_eq_zero (K := K))
    (F4.fixedOrbitElement ⟨0, by decide⟩) titsAct_isRoot_46 (1 : K)
  rw [titsAct_zOne_smul_46] at h
  exact h

theorem titsAct_conj_F :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) *
        (sylowX K 43 1 * sylowX K 46 1) *
      (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹ =
      sylowX K 44 1 * sylowX K 47 1 := by
  have e : ∀ A B C : ModGL F4.tag K, A * (B * C) * A⁻¹ = A * B * A⁻¹ * (A * C * A⁻¹) :=
    fun A B C => by group
  rw [e, titsAct_conj_43, titsAct_conj_46]

theorem titsAct_centralAOne_comm :
    Commute (centralAOne : ModGL F4.tag K) (sylowX K 44 1 * sylowX K 47 1) := by
  have hA : (centralAOne : ModGL F4.tag K) = sylowX K 33 1 * sylowX K 24 1 := by
    rw [centralAOne, sylowX, sylowX, orbitCertRoot_thirtyThree, orbitCertRoot_twentyFour,
      pinnedX_single, pinnedX_single]
  have c1 : Commute (sylowX K 33 1) (sylowX K 44 1) :=
    sylowX_commute_of_commFactors (by decide) (by decide) (by decide) (by decide) 1 1
  have c2 : Commute (sylowX K 24 1) (sylowX K 44 1) :=
    sylowX_commute_of_commFactors (by decide) (by decide) (by decide) (by decide) 1 1
  have c3 : Commute (sylowX K 33 1) (sylowX K 47 1) :=
    sylowX_commute_of_commFactors (by decide) (by decide) (by decide) (by decide) 1 1
  have c4 : Commute (sylowX K 24 1) (sylowX K 47 1) :=
    sylowX_commute_of_commFactors (by decide) (by decide) (by decide) (by decide) 1 1
  rw [hA]
  exact (c1.mul_left c2).mul_right (c3.mul_left c4)

theorem titsAct_sylowX_ne (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    sylowX K 43 1 * sylowX K 46 1 ≠ sylowX K 44 1 * sylowX K 47 1 := by
  have hF : sylowX K 43 1 * sylowX K 46 1 =
      sylowVec a K ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL,
      largeReeSigma_zero, largeReeSigma_one, sylowX, pinnedX_zero]
  have hZ : sylowX K 44 1 * sylowX K 47 1 =
      sylowVec a K ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL,
      largeReeSigma_zero, largeReeSigma_one, sylowX, pinnedX_zero]
  intro h
  rw [hF, hZ] at h
  have h' := (bijOn_sylowVec hK).2.1 (Set.mem_univ _) (Set.mem_univ _) h
  have h6 := congrFun h' 6
  simp at h6

end Helpers

section Main


theorem largeReeA1Hom_g3_moves_complement_zero {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ w ∈ ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩,
      largeReeA1Hom K a (uSL 1 * WSL) * w ≠ w * largeReeA1Hom K a (uSL 1 * WSL) := by
  have hg : largeReeA1Hom K a (uSL 1 * WSL) = centralAOne *
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) := by
    rw [map_mul, largeReeA1Hom_uSL, one_pow, largeReeA1Hom_WSL,
      canonicalRep_F4_fixedOrbitElement_zero, centralAOne]
  refine ⟨sylowX K 43 1 * sylowX K 46 1,
    (Subgroup.mem_inf.1 (sylowF_zero_one_mem_tKernel hK)).1, ?_⟩
  rw [hg]
  intro h
  have key : (centralAOne : ModGL F4.tag K) * (sylowX K 44 1 * sylowX K 47 1) =
      sylowX K 43 1 * sylowX K 46 1 * centralAOne := by
    calc (centralAOne : ModGL F4.tag K) * (sylowX K 44 1 * sylowX K 47 1)
        = (centralAOne : ModGL F4.tag K) *
            (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) *
              (sylowX K 43 1 * sylowX K 46 1) *
              (canonicalRep (coxeterSystem F4.tag) K
                (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹) := by
          rw [titsAct_conj_F]
      _ = (centralAOne : ModGL F4.tag K) *
            canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) *
            (sylowX K 43 1 * sylowX K 46 1) *
            (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹ := by
          group
      _ = (sylowX K 43 1 * sylowX K 46 1) * ((centralAOne : ModGL F4.tag K) *
            canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩)) *
            (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹ := by
          rw [h]
      _ = sylowX K 43 1 * sylowX K 46 1 * centralAOne := by
          group
  have hZF : sylowX K 44 1 * sylowX K 47 1 = sylowX K 43 1 * sylowX K 46 1 :=
    mul_right_cancel ((titsAct_centralAOne_comm (K := K)).eq.symm.trans key)
  exact titsAct_sylowX_ne hK hZF.symm

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
