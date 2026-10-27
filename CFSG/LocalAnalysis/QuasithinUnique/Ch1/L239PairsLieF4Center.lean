module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Calc

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

@[expose] def tWord (n : ℕ) : Word := famWord n [[]] [[]]

@[expose] def centerEqs (tests : List ℕ) : List Poly :=
  tests.flatMap fun n => (List.range 24).map fun i =>
    polyAdd ((coordsOf fuel (sylowWord ++ tWord n)).getD i [])
      ((coordsOf fuel (tWord n ++ sylowWord)).getD i [])

@[expose] def testsV0 : List ℕ := [2, 11, 10, 9, 4, 1]

@[expose] def testsV1 : List ℕ := [0, 11, 10, 9, 4, 3, 5]

theorem centerChecks_V0 : ∀ n ∈ testsV0,
    collectCheck fuel (sylowWord ++ tWord n) (coordsOf fuel (sylowWord ++ tWord n)) = true ∧
      collectCheck fuel (tWord n ++ sylowWord) (coordsOf fuel (tWord n ++ sylowWord)) = true := by
  decide +kernel

theorem centerChecks_V1 : ∀ n ∈ testsV1,
    collectCheck fuel (sylowWord ++ tWord n) (coordsOf fuel (sylowWord ++ tWord n)) = true ∧
      collectCheck fuel (tWord n ++ sylowWord) (coordsOf fuel (tWord n ++ sylowWord)) = true := by
  decide +kernel

@[expose] def traceV0 : List (ℕ × ℕ) :=
  [(7, 3), (17, 4), (19, 10), (43, 1), (67, 2), (68, 5), (91, 7), (116, 9), (139, 11)]

@[expose] def traceV1 : List (ℕ × ℕ) :=
  [(17, 21), (14, 17), (12, 7), (20, 6), (44, 3), (86, 12), (92, 4), (140, 11), (164, 10)]

theorem traceV0_ok :
    traceZeros (centerEqs testsV0) [0, 12] traceV0 [1, 2, 3, 4, 5, 7, 9, 10, 11] = true := by
  decide +kernel

theorem traceV1_ok :
    traceZeros (centerEqs testsV1) [1, 2, 13, 14] traceV1 [0, 3, 4, 5, 6, 7, 9, 10, 11] = true := by
  decide +kernel

section Forced

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime]

theorem centerEqs_vanish
    {tests : List ℕ} (htests : ∀ n ∈ tests, n ≤ 11)
    (hchk : ∀ n ∈ tests,
      collectCheck fuel (sylowWord ++ tWord n) (coordsOf fuel (sylowWord ++ tWord n)) = true ∧
        collectCheck fuel (tWord n ++ sylowWord) (coordsOf fuel (tWord n ++ sylowWord)) = true)
    (a b c d e f g h i j k l : K)
    (hcomm : ∀ n ∈ tests, sylowV m K a b c d e f g h i j k l * fam m K n 1 =
      fam m K n 1 * sylowV m K a b c d e f g h i j k l) :
    ∀ p ∈ centerEqs tests, polyEval (coordVal m a b c d e f g h i j k l) p = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  intro p hp
  obtain ⟨n, hn, hp⟩ := List.mem_flatMap.1 hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have hq' : q < 24 := List.mem_range.1 hq
  have ht : wordEval K (coordVal m a b c d e f g h i j k l) (tWord n) = fam m K n 1 := by
    have h1 : polyEval (coordVal m a b c d e f g h i j k l) [[]] = 1 := by
      simp [polyEval, monoEval]
    have := wordEval_famWord (m := m) (htests n hn) (coordVal m a b c d e f g h i j k l)
      [[]] [[]] (by rw [h1, largeReeSigma_one])
    rwa [h1] at this
  have hx : wordEval K (coordVal m a b c d e f g h i j k l) (sylowWord ++ tWord n) =
      wordEval K (coordVal m a b c d e f g h i j k l) (tWord n ++ sylowWord) := by
    rw [wordEval_append, wordEval_append, ht, ← sylowV_eq_wordEval]
    exact hcomm n hn
  exact eqs_of_wordEval_eq (hchk n hn).1 (hchk n hn).2 hx q hq'

theorem center_V0_forced
    (b c d e f g h i j k l : K)
    (hcomm : ∀ n ∈ testsV0, sylowV m K 0 b c d e f g h i j k l * fam m K n 1 =
      fam m K n 1 * sylowV m K 0 b c d e f g h i j k l) :
    b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ h = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hz := traceZeros_sound (m := m) (coordVal m 0 b c d e f g h i j k l)
    (coordVal_add_twelve (m := m) 0 b c d e f g h i j k l) (centerEqs testsV0)
    (centerEqs_vanish (by decide) centerChecks_V0 0 b c d e f g h i j k l hcomm)
    (zs₀ := [0, 12]) (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rfl
      · exact largeReeSigma_zero) traceV0_ok
  exact ⟨hz 1 (by decide), hz 2 (by decide), hz 3 (by decide), hz 4 (by decide),
    hz 5 (by decide), hz 7 (by decide), hz 9 (by decide), hz 10 (by decide), hz 11 (by decide)⟩

theorem center_V1_forced
    (a d e f g h i j k l : K)
    (hcomm : ∀ n ∈ testsV1, sylowV m K a 0 0 d e f g h i j k l * fam m K n 1 =
      fam m K n 1 * sylowV m K a 0 0 d e f g h i j k l) :
    a = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hz := traceZeros_sound (m := m) (coordVal m a 0 0 d e f g h i j k l)
    (coordVal_add_twelve (m := m) a 0 0 d e f g h i j k l) (centerEqs testsV1)
    (centerEqs_vanish (by decide) centerChecks_V1 a 0 0 d e f g h i j k l hcomm)
    (zs₀ := [1, 2, 13, 14]) (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · exact largeReeSigma_zero
      · exact largeReeSigma_zero) traceV1_ok
  exact ⟨hz 0 (by decide), hz 3 (by decide), hz 4 (by decide), hz 5 (by decide),
    hz 6 (by decide), hz 7 (by decide), hz 9 (by decide), hz 10 (by decide), hz 11 (by decide)⟩

end Forced

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4
