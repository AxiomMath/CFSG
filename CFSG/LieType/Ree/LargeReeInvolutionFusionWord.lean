module

public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizerBruhat

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open ReeTag

section Weyl

variable (K : Type) [Field K]

abbrev weylOne : ModGL F4.tag K :=
  canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩)

abbrev weylTwo : ModGL F4.tag K :=
  canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩)

end Weyl

abbrev weylOnePairs : List (ℕ × ℕ) :=
  [(25, 26), (26, 25), (27, 34), (28, 36), (29, 35), (30, 39), (31, 38), (32, 37), (34, 27),
    (35, 29), (36, 28), (37, 32), (38, 31), (39, 30), (40, 42), (41, 41), (42, 40), (43, 44),
    (44, 43), (45, 45), (46, 47), (47, 46)]

abbrev weylTwoPairs : List (ℕ × ℕ) :=
  [(24, 31), (26, 29), (29, 26), (31, 24), (32, 32), (33, 40), (34, 37), (35, 35), (36, 43),
    (37, 34), (38, 41), (39, 46), (40, 33), (41, 38), (42, 45), (43, 36), (44, 44), (45, 42),
    (46, 39), (47, 47)]

theorem weylOnePairs_check : ∀ p ∈ weylOnePairs, (24 ≤ p.1 ∧ p.1 ≤ 47) ∧
    (F4.fixedOrbitWord ⟨0, by decide⟩).foldr (reflect F4.tag) (orbitCertRoot F4.tag p.1) =
      orbitCertRoot F4.tag p.2 := by
  decide +kernel

theorem weylTwoPairs_check : ∀ p ∈ weylTwoPairs, (24 ≤ p.1 ∧ p.1 ≤ 47) ∧
    (F4.fixedOrbitWord ⟨1, by decide⟩).foldr (reflect F4.tag) (orbitCertRoot F4.tag p.1) =
      orbitCertRoot F4.tag p.2 := by
  decide +kernel

section Conj

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime]

theorem weyl_conj_mul {G : Type*} [Group G] (n x y : G) :
    n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by
  group

theorem weylOne_conj_sylowX
    {r r' : ℕ} (h : (r, r') ∈ weylOnePairs) (c : K) :
    weylOne K * sylowX K r c * (weylOne K)⁻¹ = sylowX K r' c := by
  obtain ⟨⟨h1, h2⟩, hw⟩ := weylOnePairs_check _ h
  rw [sylowX, sylowX, canonicalRep_mul_pinnedX_mul_inv_of_two F4_two_eq_zero _
    (sylowRoot_pos h1 h2).1, fixedOrbitElement_smul]
  exact congrArg (fun α => pinnedX F4.tag K α c) hw

theorem weylTwo_conj_sylowX
    {r r' : ℕ} (h : (r, r') ∈ weylTwoPairs) (c : K) :
    weylTwo K * sylowX K r c * (weylTwo K)⁻¹ = sylowX K r' c := by
  obtain ⟨⟨h1, h2⟩, hw⟩ := weylTwoPairs_check _ h
  rw [sylowX, sylowX, canonicalRep_mul_pinnedX_mul_inv_of_two F4_two_eq_zero _
    (sylowRoot_pos h1 h2).1, fixedOrbitElement_smul]
  exact congrArg (fun α => pinnedX F4.tag K α c) hw

theorem weylOne_conj_pair
    {r₁ r₁' r₂ r₂' : ℕ} (h₁ : (r₁, r₁') ∈ weylOnePairs)
    (h₂ : (r₂, r₂') ∈ weylOnePairs) (c d : K) :
    weylOne K * (sylowX K r₁ c * sylowX K r₂ d) * (weylOne K)⁻¹ =
      sylowX K r₁' c * sylowX K r₂' d := by
  rw [weyl_conj_mul, weylOne_conj_sylowX h₁, weylOne_conj_sylowX h₂]

theorem weylTwo_conj_pair
    {r₁ r₁' r₂ r₂' : ℕ} (h₁ : (r₁, r₁') ∈ weylTwoPairs)
    (h₂ : (r₂, r₂') ∈ weylTwoPairs) (c d : K) :
    weylTwo K * (sylowX K r₁ c * sylowX K r₂ d) * (weylTwo K)⁻¹ =
      sylowX K r₁' c * sylowX K r₂' d := by
  rw [weyl_conj_mul, weylTwo_conj_sylowX h₁, weylTwo_conj_sylowX h₂]

omit [CharP K F4.prime] in
theorem sylowB_zero_left (c : K) :
    sylowB m K 0 c = sylowX K 28 c * sylowX K 30 (largeReeSigma m c) := by
  simp [sylowB, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [CharP K F4.prime] in
theorem sylowD_zero_left (e : K) :
    sylowD m K 0 e = sylowX K 36 e * sylowX K 39 (largeReeSigma m e) := by
  simp [sylowD, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [CharP K F4.prime] in
theorem sylowF_zero_left (g : K) :
    sylowF m K 0 g = sylowX K 43 g * sylowX K 46 (largeReeSigma m g) := by
  simp [sylowF, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [CharP K F4.prime] in
theorem sylowH_zero_left (i : K) :
    sylowH m K 0 i = sylowX K 44 i * sylowX K 47 (largeReeSigma m i) := by
  simp [sylowH, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [CharP K F4.prime] in
theorem sylowH_zero_eq_centralZ
    (i : K) : sylowH m K 0 i = centralZ K m i := by
  rw [sylowH_zero_left, centralZ, sylowX, sylowX, largeReeSigma]
  congr 2 <;> decide

end Conj

@[expose] def fuseConjWord : Word :=
  [(25, [[]]), (27, [[]]), (30, [[]]), (24, [[]]), (33, [[]]), (36, [[]]), (39, [[]]),
    (43, [[]]), (46, [[]]), (33, [[]]), (24, [[]]), (30, [[]]), (27, [[]]), (25, [[]])]

@[expose] def fuseMidWord : Word :=
  [(36, [[]]), (38, [[]]), (39, [[]]), (42, [[]])]

@[expose] def fuseMidCoords : List Poly :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [[]], [], [[]], [[]], [], [], [[]], [], [], [],
    [], []]

@[expose] def fuseTWord : Word :=
  [(43, [[]]), (41, [[]]), (46, [[]]), (45, [[]])]

@[expose] def fuseBtBWord : Word :=
  [(30, [[]]), (27, [[]]), (25, [[]]), (41, [[]]), (45, [[]]), (25, [[]]), (27, [[]]), (30, [[]])]

@[expose] def fuseTCoords : List Poly :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[]], [], [[]], [], [[]],
    [[]], []]

theorem fuseConj_check : collectCheck 500 fuseConjWord fuseMidCoords = true := by
  decide +kernel

theorem fuseMid_check : collectCheck 500 fuseMidWord fuseMidCoords = true := by
  decide +kernel

theorem fuseT_check : collectCheck 500 fuseTWord fuseTCoords = true := by
  decide +kernel

theorem fuseBtB_check : collectCheck 500 fuseBtBWord fuseTCoords = true := by
  decide +kernel

section Fusion

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime]

theorem sylowX_one_inv
    (r : ℕ) : (sylowX K r 1)⁻¹ = sylowX K r 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [sylowX, pinnedX_neg, CharTwo.neg_eq]

omit [CharP K F4.prime] in
theorem sylowB_one_zero
    : sylowB m K 1 0 = sylowX K 25 1 * sylowX K 27 1 * sylowX K 30 1 := by
  simp [sylowB, sylowX, largeReeSigma_zero, largeReeSigma_one, pinnedX_zero]

theorem fusion_word :
    (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) *
        (sylowB m K 0 1 * sylowH m K 0 1) *
          (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K)⁻¹ =
      sylowL m K 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hy0 : sylowB m K 0 1 * sylowH m K 0 1 =
      sylowX K 28 1 * sylowX K 30 1 * (sylowX K 44 1 * sylowX K 47 1) := by
    rw [sylowB_zero_left, sylowH_zero_left, largeReeSigma_one]
  have hy1 : weylOne K * (sylowX K 28 1 * sylowX K 30 1 * (sylowX K 44 1 * sylowX K 47 1)) *
      (weylOne K)⁻¹ = sylowX K 36 1 * sylowX K 39 1 * (sylowX K 43 1 * sylowX K 46 1) := by
    rw [weyl_conj_mul, weylOne_conj_pair (r₁ := 28) (r₁' := 36) (r₂ := 30) (r₂' := 39)
      (by decide) (by decide),
      weylOne_conj_pair (r₁ := 44) (r₁' := 43) (r₂ := 47) (r₂' := 46) (by decide) (by decide)]
  have hA : sylowA m K (1 : K) = sylowX K 24 1 * sylowX K 33 1 := by
    rw [sylowA, largeReeSigma_one]
  have hval : ∀ w : Word, wordEval K (fun _ => (0 : K)) w =
      (w.map fun f => sylowX K f.1 (polyEval (fun _ => (0 : K)) f.2)).prod := fun _ => rfl
  have hone : polyEval (fun _ => (0 : K)) [[]] = 1 := by simp [polyEval, monoEval]
  have hy3 : sylowB m K 1 0 * sylowA m K 1 *
      (sylowX K 36 1 * sylowX K 39 1 * (sylowX K 43 1 * sylowX K 46 1)) *
        (sylowA m K 1)⁻¹ * (sylowB m K 1 0)⁻¹ =
      sylowX K 36 1 * sylowX K 38 1 * sylowX K 39 1 * sylowX K 42 1 := by
    have h := (wordEval_eq_iff fuseConj_check fuseMid_check (fun _ => (0 : K))).2 fun _ => rfl
    rw [hval, hval] at h
    simp only [fuseConjWord, fuseMidWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, hone, mul_one] at h
    rw [sylowB_one_zero, hA]
    simp only [mul_inv_rev, mul_assoc]
    rw [sylowX_one_inv 33, sylowX_one_inv 24, sylowX_one_inv 30, sylowX_one_inv 27,
      sylowX_one_inv 25]
    exact h
  have hy4 : weylTwo K * (sylowX K 36 1 * sylowX K 38 1 * sylowX K 39 1 * sylowX K 42 1) *
      (weylTwo K)⁻¹ = sylowX K 43 1 * sylowX K 41 1 * sylowX K 46 1 * sylowX K 45 1 := by
    rw [weyl_conj_mul, weyl_conj_mul, weyl_conj_mul,
      weylTwo_conj_sylowX (r := 36) (r' := 43) (by decide),
      weylTwo_conj_sylowX (r := 38) (r' := 41) (by decide),
      weylTwo_conj_sylowX (r := 39) (r' := 46) (by decide),
      weylTwo_conj_sylowX (r := 42) (r' := 45) (by decide)]
  have hy5 : sylowX K 43 1 * sylowX K 41 1 * sylowX K 46 1 * sylowX K 45 1 =
      (sylowB m K 1 0)⁻¹ * sylowL m K 1 * sylowB m K 1 0 := by
    have h := (wordEval_eq_iff fuseT_check fuseBtB_check (fun _ => (0 : K))).2 fun _ => rfl
    rw [hval, hval] at h
    simp only [fuseTWord, fuseBtBWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, hone, mul_one] at h
    rw [sylowB_one_zero, sylowL, largeReeSigma_one]
    simp only [mul_inv_rev, mul_assoc]
    rw [sylowX_one_inv 30, sylowX_one_inv 27, sylowX_one_inv 25]
    exact h
  calc (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K) *
        (sylowB m K 0 1 * sylowH m K 0 1) *
          (sylowB m K 1 0 * weylTwo K * sylowB m K 1 0 * sylowA m K 1 * weylOne K)⁻¹ =
      sylowB m K 1 0 * (weylTwo K * (sylowB m K 1 0 * sylowA m K 1 *
        (weylOne K * (sylowB m K 0 1 * sylowH m K 0 1) * (weylOne K)⁻¹) *
          (sylowA m K 1)⁻¹ * (sylowB m K 1 0)⁻¹) * (weylTwo K)⁻¹) * (sylowB m K 1 0)⁻¹ := by
        group
    _ = sylowB m K 1 0 * ((sylowB m K 1 0)⁻¹ * sylowL m K 1 * sylowB m K 1 0) *
        (sylowB m K 1 0)⁻¹ := by rw [hy0, hy1, hy3, hy4, hy5]
    _ = sylowL m K 1 := by group

end Fusion

end CFSG.LieType.Ree.LargeReeInvolution
