module

public import CFSG.LieType.Chevalley.RationalToralSignDiagramOrbits
public import CFSG.LieType.Chevalley.RationalToralSignDiagramCheck

public section

namespace CFSG.LieType.Chevalley.ToralSign

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def e6Orbit0 : OrbitEntries :=
  [([false, false, false, false, false, false], [])]

@[expose] def e6Orbit20 : OrbitEntries :=
  [([false, false, true, false, true, false], []), ([true, false, true, true, true, false], [2]),
    ([false, false, true, true, true, true], [4]),
    ([true, false, false, true, true, false], [0, 2]),
    ([true, true, false, true, false, false], [3, 2]),
    ([true, false, true, false, true, true], [4, 2]),
    ([false, true, false, true, false, true], [3, 4]),
    ([false, false, true, true, false, true], [5, 4]),
    ([true, true, true, true, false, false], [3, 0, 2]),
    ([true, false, false, false, true, true], [4, 0, 2]),
    ([true, true, false, false, false, false], [1, 3, 2]),
    ([true, false, true, false, false, true], [5, 4, 2]),
    ([false, true, false, false, false, true], [1, 3, 4]),
    ([false, true, false, true, true, true], [5, 3, 4]),
    ([true, true, true, false, false, false], [1, 3, 0, 2]),
    ([false, true, true, false, false, false], [2, 3, 0, 2]),
    ([true, false, false, false, false, true], [5, 4, 0, 2]),
    ([false, true, false, false, true, true], [5, 1, 3, 4]),
    ([false, true, false, false, true, false], [4, 5, 3, 4]),
    ([false, true, true, true, false, false], [2, 1, 3, 0, 2]),
    ([false, true, false, true, true, false], [4, 5, 1, 3, 4]),
    ([false, false, false, true, true, false], [3, 2, 1, 3, 0, 2]),
    ([false, false, true, true, false, false], [3, 4, 5, 1, 3, 4]),
    ([false, false, false, false, true, true], [4, 3, 2, 1, 3, 0, 2]),
    ([true, false, true, false, false, false], [2, 3, 4, 5, 1, 3, 4]),
    ([false, false, false, false, false, true], [5, 4, 3, 2, 1, 3, 0, 2]),
    ([true, false, false, false, false, false], [0, 2, 3, 4, 5, 1, 3, 4])]

@[expose] def e6Orbit2 : OrbitEntries :=
  [([false, true, false, false, false, false], []),
    ([false, true, false, true, false, false], [1]),
    ([false, false, true, true, true, false], [3, 1]),
    ([true, false, true, false, true, false], [2, 3, 1]),
    ([false, false, true, false, true, true], [4, 3, 1]),
    ([true, false, false, false, true, false], [0, 2, 3, 1]),
    ([true, false, true, true, true, true], [4, 2, 3, 1]),
    ([false, false, true, false, false, true], [5, 4, 3, 1]),
    ([true, false, false, true, true, true], [4, 0, 2, 3, 1]),
    ([true, true, false, true, false, true], [3, 4, 2, 3, 1]),
    ([true, false, true, true, false, true], [5, 4, 2, 3, 1]),
    ([true, true, true, true, false, true], [3, 4, 0, 2, 3, 1]),
    ([true, false, false, true, false, true], [5, 4, 0, 2, 3, 1]),
    ([true, true, false, false, false, true], [1, 3, 4, 2, 3, 1]),
    ([true, true, false, true, true, true], [5, 3, 4, 2, 3, 1]),
    ([true, true, true, false, false, true], [1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, false, false, true], [2, 3, 4, 0, 2, 3, 1]),
    ([true, true, true, true, true, true], [5, 3, 4, 0, 2, 3, 1]),
    ([true, true, false, false, true, true], [5, 1, 3, 4, 2, 3, 1]),
    ([true, true, false, false, true, false], [4, 5, 3, 4, 2, 3, 1]),
    ([false, true, true, true, false, true], [2, 1, 3, 4, 0, 2, 3, 1]),
    ([true, true, true, false, true, true], [5, 1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, false, true, true], [5, 2, 3, 4, 0, 2, 3, 1]),
    ([true, true, true, false, true, false], [4, 5, 3, 4, 0, 2, 3, 1]),
    ([true, true, false, true, true, false], [4, 5, 1, 3, 4, 2, 3, 1]),
    ([false, false, false, true, true, true], [3, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, true, true, true], [5, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([true, true, true, true, true, false], [4, 5, 1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, true, true, false], [4, 5, 2, 3, 4, 0, 2, 3, 1]),
    ([true, false, true, true, false, false], [3, 4, 5, 1, 3, 4, 2, 3, 1]),
    ([false, false, false, false, true, false], [4, 3, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([false, false, false, true, false, true], [5, 3, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, false, true, false], [4, 5, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([true, false, false, true, false, false], [3, 4, 5, 1, 3, 4, 0, 2, 3, 1]),
    ([false, false, false, true, false, false], [3, 4, 5, 2, 3, 4, 0, 2, 3, 1]),
    ([false, false, true, false, false, false], [2, 3, 4, 5, 1, 3, 4, 2, 3, 1])]

@[expose] def e6RhoIdx : List ℕ :=
  [5, 1, 4, 3, 2, 0, 16, 15, 8, 9, 14, 13, 12, 11, 10, 7, 6, 26, 25, 19, 21, 20, 24, 23, 22, 18,
    17, 36, 33, 35, 31, 30, 32, 28, 34, 29, 27, 42, 45, 44, 40, 41, 37, 43, 39, 38, 51, 47, 52, 49,
    50, 46, 48, 57, 54, 58, 56, 53, 55, 63, 60, 62, 61, 59, 65, 64, 66, 67, 68, 69, 70, 71]

@[expose] def e6Splus0 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 7, 9, 11, 13, 15, 18, 20, 21, 23, 25, 28, 29, 32, 33, 35, 39, 40, 43, 44, 48,
    49, 52, 55, 56, 58, 61, 62, 66, 68, 70]

@[expose] def e6Delta0 : List ℕ :=
  [0, 1, 2, 3, 4, 5]

@[expose] def e6Paths0_0 : List (ℕ × List ℕ) :=
  [(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (6, [0]), (7, [2]), (8, [1]), (9, [3]),
    (10, [2]), (11, [3]), (12, [3]), (13, [3]), (14, [2]), (15, [0]), (16, [0]), (17, [2, 0]),
    (18, [3, 2]), (19, [3, 1]), (20, [1, 3]), (21, [1, 3]), (22, [3, 2]), (23, [2]), (24, [3, 2]),
    (25, [3, 0]), (26, [0, 2]), (27, [3, 2, 0]), (28, [1, 3, 2]), (29, [2, 3, 2]), (30, [1, 3, 2]),
    (31, [1, 3, 2]), (32, [2, 3]), (33, [1, 3, 0]), (34, [2, 3]), (35, [2, 3, 0]), (36, [3, 0, 2]),
    (37, [1, 3, 2, 0]), (38, [2, 3, 2, 0]), (39, [2, 1, 3, 2]), (40, [0, 2]), (41, [2, 3, 1]),
    (42, [1, 3, 0, 2]), (43, [3, 2, 3]), (44, [2, 1, 3, 0]), (45, [2, 3, 0, 2]),
    (46, [2, 1, 3, 2, 0]), (47, [0, 2, 3]), (48, [3, 2, 1, 3, 2]), (49, [0, 2, 3]),
    (50, [3, 2, 3, 1]), (51, [2, 1, 3, 0, 2]), (52, [3, 2, 1, 3, 0]), (53, [3, 2, 1, 3, 2, 0]),
    (54, [0, 2, 3, 1]), (55, [2, 3, 2, 1, 3, 2]), (56, [3, 0, 2, 3]), (57, [3, 2, 1, 3, 0, 2]),
    (58, [2, 3, 2, 1, 3, 0]), (59, [2, 3, 2, 1, 3, 2, 0]), (60, [3, 0, 2, 3, 1]),
    (61, [0, 2, 3, 2, 1, 3, 2]), (62, [0, 2, 3, 2, 1, 3, 0]), (63, [2, 3, 2, 1, 3, 0, 2]),
    (64, [0, 2, 3, 2, 1, 3, 2, 0]), (65, [0, 2, 3, 2, 1, 3, 0, 2]), (66, [2, 3, 0, 2, 3]),
    (67, [2, 3, 0, 2, 3, 1]), (68, [3, 2, 3, 0, 2, 3]), (69, [3, 2, 3, 0, 2, 3, 1]),
    (70, [1, 3, 2, 3, 0, 2, 3]), (71, [1, 3, 2, 3, 0, 2, 3, 1])]

@[expose] def e6Splus20 : List ℕ :=
  [0, 1, 3, 5, 9, 23, 29, 32, 35, 39, 40, 43, 44, 48, 49, 52, 56, 66, 68, 70]

@[expose] def e6Delta20 : List ℕ :=
  [0, 1, 3, 5, 23]

@[expose] def e6Paths20_0 : List (ℕ × List ℕ) :=
  [(0, []), (1, []), (3, []), (5, []), (6, [0]), (8, [1]), (9, [3]), (12, [3]), (16, [0]),
    (19, [3, 1]), (23, []), (29, [23]), (32, [23]), (34, [23]), (35, [23]), (38, [23, 0]),
    (39, [1, 23]), (40, [0]), (41, [23, 1]), (43, [23, 3]), (44, [1, 23]), (45, [23, 0]),
    (46, [1, 23, 0]), (47, [0, 23]), (48, [3, 1, 23]), (49, [0, 23]), (50, [23, 3, 1]),
    (51, [1, 23, 0]), (52, [3, 1, 23]), (53, [3, 1, 23, 0]), (54, [0, 23, 1]), (56, [0, 23, 3]),
    (57, [3, 1, 23, 0]), (60, [0, 23, 3, 1]), (66, [23, 0, 23]), (67, [23, 0, 23, 1]),
    (68, [23, 0, 23, 3]), (69, [23, 0, 23, 3, 1]), (70, [1, 23, 0, 23, 3]),
    (71, [1, 23, 0, 23, 3, 1])]

@[expose] def e6Splus2 : List ℕ :=
  [0, 2, 3, 4, 5, 7, 11, 13, 15, 18, 23, 25, 29, 35, 40, 70]

@[expose] def e6Delta2 : List ℕ :=
  [0, 2, 3, 4, 5, 70]

@[expose] def e6Paths2_0 : List (ℕ × List ℕ) :=
  [(0, []), (2, []), (3, []), (4, []), (5, []), (6, [0]), (7, [2]), (10, [2]), (11, [3]),
    (12, [3]), (13, [3]), (14, [2]), (15, [0]), (16, [0]), (17, [2, 0]), (18, [3, 2]),
    (22, [3, 2]), (23, [2]), (24, [3, 2]), (25, [3, 0]), (26, [0, 2]), (27, [3, 2, 0]),
    (29, [2, 3, 2]), (34, [2, 3]), (35, [2, 3, 0]), (36, [3, 0, 2]), (38, [2, 3, 2, 0]),
    (40, [0, 2]), (45, [2, 3, 0, 2]), (47, [0, 2, 3]), (70, []), (71, [70])]

@[expose] def e6OmegaWords0 : List (List (Fin Tag.E6.rank)) :=
  [[]]

@[expose] def e6OmegaWords20 : List (List (Fin Tag.E6.rank)) :=
  [[]]

@[expose] def e6OmegaWords2 : List (List (Fin Tag.E6.rank)) :=
  [[]]

@[expose] def e6SignDiagramReps : List (SignRep .E6) :=
  [⟨0, 1, 1, e6OmegaWords0⟩, ⟨20, 27, 1, e6OmegaWords20⟩, ⟨2, 36, 1, e6OmegaWords2⟩]

@[expose] def e6OrbitCert : OrbitCert .E6 where
  stable := e6SignDiagramReps.zip [e6Orbit0, e6Orbit20, e6Orbit2]
  other := []

theorem e6OrbitCert_reps : e6OrbitCert.reps = e6SignDiagramReps :=
  rfl

theorem e6OrbitCert_check :
    e6OrbitCert.check (TwistTag.E6.perm : Equiv.Perm (Fin Tag.E6.rank)) = true := by
  decide +kernel

theorem e6OrbitCert_covers : e6OrbitCert.Covers := by
  unfold OrbitCert.Covers
  decide +kernel

theorem e6_rhoCheck :
    rhoCheck e6Certificate (TwistTag.E6.perm : Equiv.Perm (Fin Tag.E6.rank)) e6RhoIdx = true := by
  decide +kernel

theorem e6_splus0 : splusCheck e6Certificate 0 e6Splus0 = true := by
  decide +kernel

theorem e6_delta0 : deltaCheck e6Certificate e6Splus0 e6Delta0 = true := by
  decide +kernel

theorem e6_omega0 : e6OmegaWords0.all (omegaCheck e6Certificate 0 e6Splus0) = true := by
  decide +kernel

theorem e6_distinct0 : distinctCheck e6Certificate e6OmegaWords0 = true := by
  decide +kernel

theorem e6_card0
    : Nat.card (kernelPosStabilizer (signMaskChar .E6 0)) ≤ 1 :=
  ((sign_kernel_positive_Weyl_component_representatives .E6 _).2.2.2.2.2.2.1
    (Or.inr (Or.inr (Or.inl rfl)))).le

theorem e6_orbit0_0 :
    orbitCheck e6Certificate 0 (thetaIdx e6Certificate e6RhoIdx []) 2 = true := by
  decide +kernel

theorem e6_path0_0 : pathCheck e6Certificate 0 (thetaIdx e6Certificate e6RhoIdx []) 2
    e6Delta0 e6Paths0_0 = true := by
  decide +kernel

theorem e6_splus20 : splusCheck e6Certificate 20 e6Splus20 = true := by
  decide +kernel

theorem e6_delta20 : deltaCheck e6Certificate e6Splus20 e6Delta20 = true := by
  decide +kernel

theorem e6_omega20 : e6OmegaWords20.all (omegaCheck e6Certificate 20 e6Splus20) = true := by
  decide +kernel

theorem e6_distinct20 : distinctCheck e6Certificate e6OmegaWords20 = true := by
  decide +kernel

theorem e6_card20
    : Nat.card (kernelPosStabilizer (signMaskChar .E6 20)) ≤ 1 :=
  ((sign_kernel_positive_Weyl_component_representatives .E6 _).2.2.2.2.2.2.1
    (Or.inr (Or.inr (Or.inl rfl)))).le

theorem e6_orbit20_0 :
    orbitCheck e6Certificate 20 (thetaIdx e6Certificate e6RhoIdx []) 2 = true := by
  decide +kernel

theorem e6_path20_0 : pathCheck e6Certificate 20 (thetaIdx e6Certificate e6RhoIdx []) 2
    e6Delta20 e6Paths20_0 = true := by
  decide +kernel

theorem e6_splus2 : splusCheck e6Certificate 2 e6Splus2 = true := by
  decide +kernel

theorem e6_delta2 : deltaCheck e6Certificate e6Splus2 e6Delta2 = true := by
  decide +kernel

theorem e6_omega2 : e6OmegaWords2.all (omegaCheck e6Certificate 2 e6Splus2) = true := by
  decide +kernel

theorem e6_distinct2 : distinctCheck e6Certificate e6OmegaWords2 = true := by
  decide +kernel

theorem e6_card2
    : Nat.card (kernelPosStabilizer (signMaskChar .E6 2)) ≤ 1 :=
  ((sign_kernel_positive_Weyl_component_representatives .E6 _).2.2.2.2.2.2.1
    (Or.inr (Or.inr (Or.inl rfl)))).le

theorem e6_orbit2_0 :
    orbitCheck e6Certificate 2 (thetaIdx e6Certificate e6RhoIdx []) 2 = true := by
  decide +kernel

theorem e6_path2_0 : pathCheck e6Certificate 2 (thetaIdx e6Certificate e6RhoIdx []) 2
    e6Delta2 e6Paths2_0 = true := by
  decide +kernel

theorem rationalToralSignDiagram_E6 :
    RationalToralSignDiagram .E6 (TwistTag.E6.perm : Equiv.Perm (Fin Tag.E6.rank)) 2
      e6SignDiagramReps := by
  rw [← e6OrbitCert_reps]
  refine RationalToralSignDiagram.of_cert e6OrbitCert_check e6OrbitCert_covers fun e he => ?_
  have hχ := OrbitCert.permChar_eq e6OrbitCert_check e he
  rw [e6OrbitCert_reps] at he
  simp only [e6SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · refine repClaims_of_check e6Certificate_check (TwistTag.cartan_perm .E6) (Matrix.one_mul _)
      (by decide) hχ e6_rhoCheck e6_splus0 e6_delta0 e6_omega0 e6_distinct0
      rfl e6_card0 ?_
    · intro l hl
      simp only [e6OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
      subst hl
      exact ⟨_, e6_orbit0_0, e6_path0_0⟩
  · refine repClaims_of_check e6Certificate_check (TwistTag.cartan_perm .E6) (Matrix.one_mul _)
      (by decide) hχ e6_rhoCheck e6_splus20 e6_delta20 e6_omega20 e6_distinct20
      rfl e6_card20 ?_
    · intro l hl
      simp only [e6OmegaWords20, List.mem_cons, List.mem_nil_iff, or_false] at hl
      subst hl
      exact ⟨_, e6_orbit20_0, e6_path20_0⟩
  · refine repClaims_of_check e6Certificate_check (TwistTag.cartan_perm .E6) (Matrix.one_mul _)
      (by decide) hχ e6_rhoCheck e6_splus2 e6_delta2 e6_omega2 e6_distinct2
      rfl e6_card2 ?_
    · intro l hl
      simp only [e6OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
      subst hl
      exact ⟨_, e6_orbit2_0, e6_path2_0⟩

end CFSG.LieType.Chevalley.ToralSign

