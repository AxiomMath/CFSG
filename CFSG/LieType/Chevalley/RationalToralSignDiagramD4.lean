module

public import CFSG.LieType.Chevalley.RationalToralSignDiagramOrbits
public import CFSG.LieType.Chevalley.RationalToralSignDiagramCheck

public section

namespace CFSG.LieType.Chevalley.ToralSign

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def d4Orbit0 : OrbitEntries :=
  [([false, false, false, false], [])]

@[expose] def d4Orbit4 : OrbitEntries :=
  [([false, false, true, false], []), ([true, true, true, true], [2]),
    ([true, true, false, true], [0, 2])]

@[expose] def d4OtherOrbit0 : OrbitEntries :=
  [([true, false, false, false], []), ([true, false, true, false], [0]),
    ([false, true, true, true], [2, 0]), ([false, true, false, true], [1, 2, 0])]

@[expose] def d4OtherOrbit1 : OrbitEntries :=
  [([false, true, false, false], []), ([false, true, true, false], [1]),
    ([true, false, true, true], [2, 1]), ([true, false, false, true], [0, 2, 1])]

@[expose] def d4OtherOrbit2 : OrbitEntries :=
  [([true, true, false, false], []), ([true, true, true, false], [0]),
    ([false, false, true, true], [2, 0]), ([false, false, false, true], [3, 2, 0])]

@[expose] def d4RhoIdx : List ℕ :=
  [1, 3, 2, 0, 6, 7, 10, 9, 8, 5, 4, 14, 15, 12, 16, 13, 11, 20, 17, 19, 18, 21, 22, 23]

@[expose] def d4Splus0 : List ℕ :=
  [0, 1, 2, 3, 5, 7, 9, 12, 13, 15, 19, 22]

@[expose] def d4Delta0 : List ℕ :=
  [0, 1, 2, 3]

@[expose] def d4Paths0_0 : List (ℕ × List ℕ) :=
  [(0, []), (1, []), (2, []), (3, []), (4, [0]), (5, [2]), (6, [0]), (7, [2]), (8, [2]), (9, [2]),
    (10, [0]), (11, [2, 0]), (12, [0, 2]), (13, [0, 2]), (14, [2, 0]), (15, [0, 2]), (16, [2, 0]),
    (17, [0, 2, 0]), (18, [0, 2, 0]), (19, [0]), (20, [0, 2, 0]), (21, [0, 2]), (22, [2, 0]),
    (23, [2, 0, 2])]

@[expose] def d4Splus4 : List ℕ :=
  [0, 1, 3, 22]

@[expose] def d4Delta4 : List ℕ :=
  [0, 1, 3, 22]

@[expose] def d4Paths4_0 : List (ℕ × List ℕ) :=
  [(0, []), (1, []), (3, []), (4, [0]), (6, [0]), (10, [0]), (22, []), (23, [22])]

@[expose] def d4Paths4_1 : List (ℕ × List ℕ) :=
  [(0, []), (1, []), (3, []), (4, [0]), (6, [1]), (10, [1]), (22, []), (23, [1])]

@[expose] def d4Paths4_2 : List (ℕ × List ℕ) :=
  [(0, []), (1, []), (3, []), (4, [0]), (6, [0]), (10, [3]), (22, []), (23, [0])]

@[expose] def d4Paths4_3 : List (ℕ × List ℕ) :=
  [(0, []), (1, []), (3, []), (4, [0]), (6, [1]), (10, [0]), (22, []), (23, [0])]

@[expose] def d4OmegaWords0 : List (List (Fin Tag.D4.rank)) :=
  [[]]

@[expose] def d4Word4_1 : List (Fin Tag.D4.rank) :=
  ([2, 0, 1, 2] : List (Fin 4))

@[expose] def d4Word4_2 : List (Fin Tag.D4.rank) :=
  ([2, 0, 3, 2] : List (Fin 4))

@[expose] def d4Word4_3 : List (Fin Tag.D4.rank) :=
  ([2, 1, 3, 2] : List (Fin 4))

@[expose] def d4OmegaWords4 : List (List (Fin Tag.D4.rank)) :=
  [[], d4Word4_1, d4Word4_2, d4Word4_3]

@[expose] def d4SignDiagramReps : List (SignRep .D4) :=
  [⟨0, 1, 1, d4OmegaWords0⟩, ⟨4, 3, 4, d4OmegaWords4⟩]

@[expose] def d4OrbitCert : OrbitCert .D4 where
  stable := d4SignDiagramReps.zip [d4Orbit0, d4Orbit4]
  other := [d4OtherOrbit0, d4OtherOrbit1, d4OtherOrbit2]

theorem d4OrbitCert_reps : d4OrbitCert.reps = d4SignDiagramReps :=
  rfl

theorem d4OrbitCert_check :
    d4OrbitCert.check (TwistTag.D4.perm : Equiv.Perm (Fin Tag.D4.rank)) = true := by
  decide +kernel

theorem d4OrbitCert_covers : d4OrbitCert.Covers := by
  unfold OrbitCert.Covers
  decide +kernel

theorem d4_rhoCheck :
    rhoCheck d4Certificate (TwistTag.D4.perm : Equiv.Perm (Fin Tag.D4.rank)) d4RhoIdx = true := by
  decide +kernel

theorem d4_splus0 : splusCheck d4Certificate 0 d4Splus0 = true := by
  decide +kernel

theorem d4_delta0 : deltaCheck d4Certificate d4Splus0 d4Delta0 = true := by
  decide +kernel

theorem d4_omega0 : d4OmegaWords0.all (omegaCheck d4Certificate 0 d4Splus0) = true := by
  decide +kernel

theorem d4_distinct0 : distinctCheck d4Certificate d4OmegaWords0 = true := by
  decide +kernel

theorem d4_card0
    : Nat.card (kernelPosStabilizer (signMaskChar .D4 0)) ≤ 1 :=
  (natCard_kernelPosStabilizer_le_of_stabCert d4Certificate_check d4SignStab0_check
    (by decide)).trans (by decide +kernel)

theorem d4_orbit0_0 :
    orbitCheck d4Certificate 0 (thetaIdx d4Certificate d4RhoIdx []) 3 = true := by
  decide +kernel

theorem d4_path0_0 : pathCheck d4Certificate 0 (thetaIdx d4Certificate d4RhoIdx []) 3
    d4Delta0 d4Paths0_0 = true := by
  decide +kernel

theorem d4_splus4 : splusCheck d4Certificate 4 d4Splus4 = true := by
  decide +kernel

theorem d4_delta4 : deltaCheck d4Certificate d4Splus4 d4Delta4 = true := by
  decide +kernel

theorem d4_omega4 : d4OmegaWords4.all (omegaCheck d4Certificate 4 d4Splus4) = true := by
  decide +kernel

theorem d4_distinct4 : distinctCheck d4Certificate d4OmegaWords4 = true := by
  decide +kernel

theorem d4_card4
    : Nat.card (kernelPosStabilizer (signMaskChar .D4 4)) ≤ 4 :=
  (natCard_kernelPosStabilizer_le_of_stabCert d4Certificate_check d4SignStab4_check
    (by decide)).trans (by decide +kernel)

theorem d4_orbit4_0 :
    orbitCheck d4Certificate 4 (thetaIdx d4Certificate d4RhoIdx []) 3 = true := by
  decide +kernel

theorem d4_path4_0 : pathCheck d4Certificate 4 (thetaIdx d4Certificate d4RhoIdx []) 3
    d4Delta4 d4Paths4_0 = true := by
  decide +kernel

theorem d4_orbit4_1 :
    orbitCheck d4Certificate 4 (thetaIdx d4Certificate d4RhoIdx d4Word4_1) 3 = true := by
  decide +kernel

theorem d4_path4_1 : pathCheck d4Certificate 4 (thetaIdx d4Certificate d4RhoIdx d4Word4_1) 3
    d4Delta4 d4Paths4_1 = true := by
  decide +kernel

theorem d4_orbit4_2 :
    orbitCheck d4Certificate 4 (thetaIdx d4Certificate d4RhoIdx d4Word4_2) 3 = true := by
  decide +kernel

theorem d4_path4_2 : pathCheck d4Certificate 4 (thetaIdx d4Certificate d4RhoIdx d4Word4_2) 3
    d4Delta4 d4Paths4_2 = true := by
  decide +kernel

theorem d4_orbit4_3 :
    orbitCheck d4Certificate 4 (thetaIdx d4Certificate d4RhoIdx d4Word4_3) 3 = true := by
  decide +kernel

theorem d4_path4_3 : pathCheck d4Certificate 4 (thetaIdx d4Certificate d4RhoIdx d4Word4_3) 3
    d4Delta4 d4Paths4_3 = true := by
  decide +kernel

theorem rationalToralSignDiagram_D4 :
    RationalToralSignDiagram .D4 (TwistTag.D4.perm : Equiv.Perm (Fin Tag.D4.rank)) 3
      d4SignDiagramReps := by
  rw [← d4OrbitCert_reps]
  refine RationalToralSignDiagram.of_cert d4OrbitCert_check d4OrbitCert_covers fun e he => ?_
  have hχ := OrbitCert.permChar_eq d4OrbitCert_check e he
  rw [d4OrbitCert_reps] at he
  simp only [d4SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · refine repClaims_of_check d4Certificate_check (TwistTag.cartan_perm .D4) (Matrix.one_mul _)
      (by decide) hχ d4_rhoCheck d4_splus0 d4_delta0 d4_omega0 d4_distinct0
      rfl d4_card0 ?_
    · intro l hl
      simp only [d4OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
      subst hl
      exact ⟨_, d4_orbit0_0, d4_path0_0⟩
  · refine repClaims_of_check d4Certificate_check (TwistTag.cartan_perm .D4) (Matrix.one_mul _)
      (by decide) hχ d4_rhoCheck d4_splus4 d4_delta4 d4_omega4 d4_distinct4
      rfl d4_card4 ?_
    · intro l hl
      simp only [d4OmegaWords4, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · exact ⟨_, d4_orbit4_0, d4_path4_0⟩
      · exact ⟨_, d4_orbit4_1, d4_path4_1⟩
      · exact ⟨_, d4_orbit4_2, d4_path4_2⟩
      · exact ⟨_, d4_orbit4_3, d4_path4_3⟩

end CFSG.LieType.Chevalley.ToralSign

