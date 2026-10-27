module

public import CFSG.RankThree.PartOne.KGD.D4T36Family

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KE
open scoped Matrix

theorem permLattice_D4_permLattice_symm (x : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm (permLattice TwistTag.D4.perm.symm x) = x := by
  ext j
  simp [permLattice]

theorem weylTwist_D4_wordProd (l : List (Fin TwistTag.D4.tag.rank)) :
    weylTwist TwistTag.D4 ((coxeterSystem TwistTag.D4.tag).wordProd l) =
      (coxeterSystem TwistTag.D4.tag).wordProd (l.map TwistTag.D4.perm) := by
  induction l with
  | nil => simp [CoxeterSystem.wordProd_nil]
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih, List.map_cons, CoxeterSystem.wordProd_cons]
    congr 1

theorem wordProd_D4_eq_of_wordMat {l₁ l₂ : List (Fin TwistTag.D4.tag.rank)}
    (h : wordMat TwistTag.D4.tag l₁ = wordMat TwistTag.D4.tag l₂) :
    (coxeterSystem TwistTag.D4.tag).wordProd l₁ = (coxeterSystem TwistTag.D4.tag).wordProd l₂ :=
  eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec, h]

@[expose] def jWordU : List (Fin TwistTag.D4.tag.rank) := [0]

@[expose] def jWordW2 : List (Fin TwistTag.D4.tag.rank) := [0, 1, 3, 2]

theorem jWordU_map : jWordU.map TwistTag.D4.perm = [1] := by decide

theorem jWordW2_twist_mat :
    wordMat TwistTag.D4.tag (jWordW2.map TwistTag.D4.perm) = wordMat TwistTag.D4.tag jWordW2 := by
  decide +kernel

theorem jWord_frame_mat :
    wordMat TwistTag.D4.tag (jWordU ++ jWordW2 ++ [1]) =
      wordMat TwistTag.D4.tag (trialityWordSix ++ trialityWordFour) := by
  decide +kernel

@[expose] def jA2tauList : List (Fin Tag.D4.rank → ℤ) :=
  [![0, 0, 1, 0], ![1, 1, 1, 1], ![1, 1, 2, 1], ![0, 0, -1, 0], ![-1, -1, -1, -1],
    ![-1, -1, -2, -1]]

theorem jA2tau_of_fix : ∀ x ∈ rootFinset Tag.D4, permLattice trialityRho x = x →
    x ∈ jA2tauList := by
  decide +kernel

theorem jA2tau_root : ∀ x ∈ jA2tauList, x ∈ rootFinset Tag.D4 := by
  decide +kernel

theorem jA2tau_fix : ∀ x ∈ jA2tauList, permLattice trialityRho x = x := by
  decide +kernel

theorem jA2tau_map : ∀ x ∈ jA2tauList, wordMat Tag.D4 [0] *ᵥ x ∈ trialitySigmaList 0 := by
  decide +kernel

theorem jA2tau_onto : ∀ v ∈ trialitySigmaList 0, ∃ x ∈ jA2tauList, wordMat Tag.D4 [0] *ᵥ x = v := by
  decide +kernel

@[expose] noncomputable def jU : WeylGroup TwistTag.D4.tag :=
  (coxeterSystem TwistTag.D4.tag).wordProd jWordU

@[expose] noncomputable def jW2 : WeylGroup TwistTag.D4.tag :=
  (coxeterSystem TwistTag.D4.tag).wordProd jWordW2

theorem jU_eq_simple : jU = (coxeterSystem TwistTag.D4.tag).simple 0 := by
  rw [jU, jWordU, CoxeterSystem.wordProd_singleton]

theorem jWeyl_zero_spec :
    (∀ x, weylTwist TwistTag.D4 jU • x =
      permLattice TwistTag.D4.perm (jU • permLattice TwistTag.D4.perm.symm x)) ∧
    (∀ x, jW2 • permLattice TwistTag.D4.perm x = permLattice TwistTag.D4.perm (jW2 • x)) ∧
    (∀ x, (jU * jW2 * (weylTwist TwistTag.D4 jU)⁻¹) • x =
      d4T36M (-1) *ᵥ permLattice TwistTag.D4.perm.symm x) ∧
    ((fun x : Fin TwistTag.D4.tag.rank → ℤ => jU • x) ''
      {x | IsRoot Tag.D4 x ∧ permLattice TwistTag.D4.perm x = x} = d4Sigma 0) := by
  set u := jU with hu
  set w₂ := jW2 with hw₂
  have hρu : ∀ x, weylTwist TwistTag.D4 u • x =
      permLattice TwistTag.D4.perm (u • permLattice TwistTag.D4.perm.symm x) := fun x => by
    conv_lhs => rw [← permLattice_D4_permLattice_symm x]
    rw [weylTwist_smul_permLattice]
  have hw₂t : weylTwist TwistTag.D4 w₂ = w₂ := by
    rw [hw₂, jW2, weylTwist_D4_wordProd]
    exact wordProd_D4_eq_of_wordMat jWordW2_twist_mat
  have hρu_eq : weylTwist TwistTag.D4 u = (coxeterSystem TwistTag.D4.tag).wordProd [1] := by
    rw [hu, jU, weylTwist_D4_wordProd, jWordU_map]
  have hρu2 : (weylTwist TwistTag.D4 u)⁻¹ = weylTwist TwistTag.D4 u := by
    rw [hρu_eq, CoxeterSystem.wordProd_singleton, CoxeterSystem.inv_simple]
  have hframe : u * w₂ * (weylTwist TwistTag.D4 u)⁻¹ =
      (coxeterSystem TwistTag.D4.tag).wordProd (trialityWordSix ++ trialityWordFour) := by
    rw [hρu2, hρu_eq, hu, hw₂, jU, jW2, ← CoxeterSystem.wordProd_append,
      ← CoxeterSystem.wordProd_append]
    exact wordProd_D4_eq_of_wordMat jWord_frame_mat
  have key : ∀ v, (-trialityAMat) *ᵥ v =
      (coxeterSystem Tag.D4).wordProd (trialityWordSix ++ trialityWordFour) •
        permLattice trialityRho v := fun v => by
    rw [← trialityAMat_eq_wordMat.2, ← Matrix.mulVec_mulVec, trialityP_mulVec,
      wordProd_smul_eq_wordMat_mulVec]
  refine ⟨hρu, fun x => ?_, fun x => ?_, ?_⟩
  · calc w₂ • permLattice TwistTag.D4.perm x
        = weylTwist TwistTag.D4 w₂ • permLattice TwistTag.D4.perm x := by rw [hw₂t]
      _ = permLattice TwistTag.D4.perm (w₂ • x) := weylTwist_smul_permLattice TwistTag.D4 w₂ x
  · have h1 := key (permLattice TwistTag.D4.perm.symm x)
    rw [show permLattice trialityRho (permLattice TwistTag.D4.perm.symm x) = x from
      permLattice_D4_permLattice_symm x] at h1
    have h2 : d4T36M (-1) = -trialityAMat := neg_one_smul ℤ trialityAMat
    rw [h2, hframe]
    exact h1.symm
  · ext v
    constructor
    · rintro ⟨x, ⟨hr, hf⟩, rfl⟩
      have hx : x ∈ jA2tauList := jA2tau_of_fix x (mem_rootFinset.2 hr) hf
      have hux : u • x = wordMat Tag.D4 [0] *ᵥ x :=
        wordProd_smul_eq_wordMat_mulVec TwistTag.D4.tag jWordU x
      show u • x ∈ trialitySigma 0
      rw [hux]
      exact mem_trialitySigma.2 (jA2tau_map x hx)
    · intro hv
      have hv' : v ∈ trialitySigmaList 0 := mem_trialitySigma.1 hv
      obtain ⟨x, hx, rfl⟩ := jA2tau_onto v hv'
      exact ⟨x, ⟨mem_rootFinset.1 (jA2tau_root x hx), jA2tau_fix x hx⟩,
        wordProd_smul_eq_wordMat_mulVec TwistTag.D4.tag jWordU x⟩

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
