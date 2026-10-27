module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Center
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Rel

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.ReeSec8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

@[expose] def testEqs (tws : List Word) : List Poly :=
  tws.flatMap fun tw => (List.range 24).map fun i =>
    polyAdd ((coordsOf fuel (sylowWord ++ tw)).getD i [])
      ((coordsOf fuel (tw ++ sylowWord)).getD i [])

@[expose] def conjWord (u x : ℕ) : Word := tWord u ++ tWord x ++ (tWord u).reverse

@[expose] def testsZ : List Word := [tWord 2, tWord 1, conjWord 0 2]

theorem testsZ_checks : ∀ tw ∈ testsZ,
    collectCheck fuel (sylowWord ++ tw) (coordsOf fuel (sylowWord ++ tw)) = true ∧
      collectCheck fuel (tw ++ sylowWord) (coordsOf fuel (tw ++ sylowWord)) = true := by
  decide +kernel

@[expose] def traceZ : List (ℕ × ℕ) :=
  [(5, 0), (7, 3), (17, 4), (19, 10), (31, 5), (43, 11), (65, 7), (67, 9)]

theorem traceZ_ok :
    traceZeros (testEqs testsZ) [1, 2, 13, 14] traceZ [0, 3, 4, 5, 7, 9, 10, 11] = true := by
  decide +kernel

section Add

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime] [Finite K]

theorem sylowL_mul
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    sylowL m K s * sylowL m K t = sylowL m K (s + t) := by
  obtain ⟨σ, hσ, -⟩ := exists_sigma hK
  have hc := sylowX_commute_of_commFactors (K := K) (i := 41) (j := 45) (by norm_num)
    (by norm_num) (by norm_num) (by decide) t (largeReeSigma m s)
  rw [sylowL, sylowL, sylowL, ← hσ, ← hσ, ← hσ, map_add]
  rw [← hσ] at hc
  simp only [sylowX, pinnedX_add] at hc ⊢
  calc pinnedX F4.tag K (orbitCertRoot F4.tag 41) s *
        pinnedX F4.tag K (orbitCertRoot F4.tag 45) (σ s) *
          (pinnedX F4.tag K (orbitCertRoot F4.tag 41) t *
            pinnedX F4.tag K (orbitCertRoot F4.tag 45) (σ t)) =
      pinnedX F4.tag K (orbitCertRoot F4.tag 41) s *
        (pinnedX F4.tag K (orbitCertRoot F4.tag 45) (σ s) *
          pinnedX F4.tag K (orbitCertRoot F4.tag 41) t) *
            pinnedX F4.tag K (orbitCertRoot F4.tag 45) (σ t) := by group
    _ = pinnedX F4.tag K (orbitCertRoot F4.tag 41) s *
        (pinnedX F4.tag K (orbitCertRoot F4.tag 41) t *
          pinnedX F4.tag K (orbitCertRoot F4.tag 45) (σ s)) *
            pinnedX F4.tag K (orbitCertRoot F4.tag 45) (σ t) := by rw [hc.eq]
    _ = _ := by group

theorem centralZ_mul
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    centralZ K m s * centralZ K m t = centralZ K m (s + t) := by
  rw [← sylowH_zero_eq_centralZ, ← sylowH_zero_eq_centralZ, ← sylowH_zero_eq_centralZ,
    sylowH_mul hK]

end Add

section Forced

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime]

theorem wordEval_tWord {n : ℕ}
    (hn : n ≤ 11) (x : ℕ → K) : wordEval K x (tWord n) = fam m K n 1 := by
  have h1 : polyEval x [[]] = 1 := by simp [polyEval, monoEval]
  have := wordEval_famWord (m := m) hn x [[]] [[]] (by rw [h1, largeReeSigma_one])
  rwa [h1] at this

theorem wordEval_conjWord {u x : ℕ}
    (hu : u ≤ 11) (hx : x ≤ 11) (y : ℕ → K) :
    wordEval K y (conjWord u x) = fam m K u 1 * fam m K x 1 * (fam m K u 1)⁻¹ := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [conjWord, wordEval_append, wordEval_append, wordEval_reverse, wordEval_tWord hu,
    wordEval_tWord hx]

theorem testEqs_vanish
    {tws : List Word}
    (hchk : ∀ tw ∈ tws,
      collectCheck fuel (sylowWord ++ tw) (coordsOf fuel (sylowWord ++ tw)) = true ∧
        collectCheck fuel (tw ++ sylowWord) (coordsOf fuel (tw ++ sylowWord)) = true)
    (a b c d e f g h i j k l : K)
    (hcomm : ∀ tw ∈ tws, sylowV m K a b c d e f g h i j k l *
        wordEval K (coordVal m a b c d e f g h i j k l) tw =
      wordEval K (coordVal m a b c d e f g h i j k l) tw * sylowV m K a b c d e f g h i j k l) :
    ∀ p ∈ testEqs tws, polyEval (coordVal m a b c d e f g h i j k l) p = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  intro p hp
  obtain ⟨tw, htw, hp⟩ := List.mem_flatMap.1 hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have hx : wordEval K (coordVal m a b c d e f g h i j k l) (sylowWord ++ tw) =
      wordEval K (coordVal m a b c d e f g h i j k l) (tw ++ sylowWord) := by
    rw [wordEval_append, wordEval_append, ← sylowV_eq_wordEval]
    exact hcomm tw htw
  exact eqs_of_wordEval_eq (hchk tw htw).1 (hchk tw htw).2 hx q (List.mem_range.1 hq)

theorem zx_forced
    (a d e f g h i j k l : K)
    (h₁ : sylowV m K a 0 0 d e f g h i j k l * sylowB m K 0 1 =
      sylowB m K 0 1 * sylowV m K a 0 0 d e f g h i j k l)
    (h₂ : sylowV m K a 0 0 d e f g h i j k l * sylowB m K 1 0 =
      sylowB m K 1 0 * sylowV m K a 0 0 d e f g h i j k l)
    (h₃ : sylowV m K a 0 0 d e f g h i j k l *
        (sylowA m K 1 * sylowB m K 0 1 * (sylowA m K 1)⁻¹) =
      sylowA m K 1 * sylowB m K 0 1 * (sylowA m K 1)⁻¹ * sylowV m K a 0 0 d e f g h i j k l) :
    a = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ h = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hcomm : ∀ tw ∈ testsZ, sylowV m K a 0 0 d e f g h i j k l *
      wordEval K (coordVal m a 0 0 d e f g h i j k l) tw =
        wordEval K (coordVal m a 0 0 d e f g h i j k l) tw *
          sylowV m K a 0 0 d e f g h i j k l := by
    intro tw htw
    simp only [testsZ, List.mem_cons, List.not_mem_nil, or_false] at htw
    rcases htw with rfl | rfl | rfl
    · rw [wordEval_tWord (by norm_num)]
      exact h₁
    · rw [wordEval_tWord (by norm_num)]
      exact h₂
    · rw [wordEval_conjWord (by norm_num) (by norm_num)]
      exact h₃
  have hz := traceZeros_sound (m := m) (coordVal m a 0 0 d e f g h i j k l)
    (coordVal_add_twelve (m := m) a 0 0 d e f g h i j k l) (testEqs testsZ)
    (testEqs_vanish testsZ_checks a 0 0 d e f g h i j k l hcomm)
    (zs₀ := [1, 2, 13, 14]) (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · exact largeReeSigma_zero
      · exact largeReeSigma_zero) traceZ_ok
  exact ⟨hz 0 (by decide), hz 3 (by decide), hz 4 (by decide), hz 5 (by decide),
    hz 7 (by decide), hz 9 (by decide), hz 10 (by decide), hz 11 (by decide)⟩

end Forced

section Centres

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem eq_centralZ_of_commute
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {w : ModGL F4.tag K}
    (hw : w ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩)
    (h₁ : w * sylowB m K 0 1 = sylowB m K 0 1 * w) (h₂ : w * sylowB m K 1 0 = sylowB m K 1 0 * w)
    (h₃ : w * (sylowA m K 1 * sylowB m K 0 1 * (sylowA m K 1)⁻¹) =
      sylowA m K 1 * sylowB m K 0 1 * (sylowA m K 1)⁻¹ * w)
    (h₄ : weylTwo K * w = w * weylTwo K) : ∃ i : K, centralZ K m i = w := by
  have hwU := reeFixedOrbitComplementUnipotent_le _ hw
  obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hwU
  obtain ⟨hx1, hx2⟩ := coord_one_two_eq hK hw (b := 0) (c := 0)
    (by rw [sylowB_zero_zero, one_mul])
  have e₀ : sylowVec m K x =
      sylowV m K (x 0) 0 0 (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) := by
    rw [sylowVec, hx1, hx2]
  rw [e₀] at h₁ h₂ h₃ h₄
  obtain ⟨ha, hd, he, hf, hh, hj, hk, hl⟩ := zx_forced _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
  rw [ha, hd, he, hf, hh, hj, hk, hl] at h₄
  rw [e₀, ha, hd, he, hf, hh, hj, hk, hl]
  set g := x 6
  set i := x 8
  have ew : sylowV m K 0 0 0 0 0 0 g 0 i 0 0 0 = fam m K 6 g * fam m K 8 i := by
    show _ = sylowF m K 0 g * sylowH m K 0 i
    simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowJ_zero, sylowK_zero,
      sylowL_zero', one_mul, mul_one]
  have ew' : sylowV m K 0 0 0 0 g 0 0 0 i 0 0 0 = fam m K 4 g * fam m K 8 i := by
    show _ = sylowD m K 0 g * sylowH m K 0 i
    simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowF_zero_zero, sylowJ_zero, sylowK_zero,
      sylowL_zero', one_mul, mul_one]
  have hconj : weylTwo K * sylowV m K 0 0 0 0 0 0 g 0 i 0 0 0 * (weylTwo K)⁻¹ =
      sylowV m K 0 0 0 0 g 0 0 0 i 0 0 0 := by
    rw [ew, ew']
    calc weylTwo K * (fam m K 6 g * fam m K 8 i) * (weylTwo K)⁻¹ =
        (weylTwo K * fam m K 6 g * (weylTwo K)⁻¹) * (weylTwo K * fam m K 8 i * (weylTwo K)⁻¹) := by
          group
      _ = fam m K 4 g * fam m K 8 i := by
        rw [weylTwo_conj_fam (n := 6) (n' := 4) (by decide) g,
          weylTwo_conj_fam (n := 8) (n' := 8) (by decide) i]
  have hfix : weylTwo K * sylowV m K 0 0 0 0 0 0 g 0 i 0 0 0 * (weylTwo K)⁻¹ =
      sylowV m K 0 0 0 0 0 0 g 0 i 0 0 0 := by
    rw [h₄, mul_inv_cancel_right]
  have heq : sylowVec m K ![0, 0, 0, 0, g, 0, 0, 0, i, 0, 0, 0] =
      sylowVec m K ![0, 0, 0, 0, 0, 0, g, 0, i, 0, 0, 0] := by
    show sylowV m K 0 0 0 0 g 0 0 0 i 0 0 0 = sylowV m K 0 0 0 0 0 0 g 0 i 0 0 0
    rw [← hconj, hfix]
  have h4 := congrFun ((bijOn_sylowVec hK).injOn (Set.mem_univ _) (Set.mem_univ _) heq) 4
  simp only [Matrix.cons_val] at h4
  rw [h4]
  refine ⟨i, ?_⟩
  rw [← sylowH_zero_eq_centralZ, ← fam_8_eq]
  rfl

theorem eq_sylowL_of_commute
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {w : ModGL F4.tag K} (hw : w ∈ tKernel K m)
    (h₁ : w * sylowA m K 1 = sylowA m K 1 * w) (h₂ : weylOne K * w = w * weylOne K) :
    ∃ l : K, sylowL m K l = w := by
  have hw' : w ∈ (tKernel K m : Set (ModGL F4.tag K)) := hw
  rw [coe_tKernel hK] at hw'
  obtain ⟨x, ⟨hx0, hx1, hx3⟩, rfl⟩ := hw'
  have e₀ : sylowVec m K x =
      sylowV m K 0 0 (x 2) 0 (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) := by
    rw [sylowVec, hx0, hx1, hx3]
  rw [e₀] at h₁ h₂
  obtain ⟨-, hc, hf, hg, hh, hj⟩ := (sylowV_commute_sylowA_one_iff _ _ _ _ _ _ _ _ _ _ _ _).1 h₁
  rw [hc, hf, hg, hh, hj] at h₂
  rw [e₀, hc, hf, hg, hh, hj]
  set e := x 4
  set i := x 8
  set k := x 10
  set l := x 11
  have ew : sylowV m K 0 0 0 0 e 0 0 0 i 0 k l =
      fam m K 4 e * fam m K 8 i * fam m K 10 k * fam m K 11 l := by
    show _ = sylowD m K 0 e * sylowH m K 0 i * sylowK m K k * sylowL m K l
    simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowF_zero_zero, sylowJ_zero, one_mul,
      mul_one]
  have ew' : sylowV m K 0 0 e 0 0 0 i 0 0 k 0 l =
      fam m K 2 e * fam m K 6 i * fam m K 9 k * fam m K 11 l := by
    show _ = sylowB m K 0 e * sylowF m K 0 i * sylowJ m K k * sylowL m K l
    simp only [sylowV, sylowA_zero, sylowD_zero_zero, sylowH_zero_zero', sylowK_zero, one_mul,
      mul_one]
  have hconj : weylOne K * sylowV m K 0 0 0 0 e 0 0 0 i 0 k l * (weylOne K)⁻¹ =
      sylowV m K 0 0 e 0 0 0 i 0 0 k 0 l := by
    rw [ew, ew']
    calc weylOne K * (fam m K 4 e * fam m K 8 i * fam m K 10 k * fam m K 11 l) * (weylOne K)⁻¹ =
        (weylOne K * fam m K 4 e * (weylOne K)⁻¹) * (weylOne K * fam m K 8 i * (weylOne K)⁻¹) *
          (weylOne K * fam m K 10 k * (weylOne K)⁻¹) *
            (weylOne K * fam m K 11 l * (weylOne K)⁻¹) := by group
      _ = fam m K 2 e * fam m K 6 i * fam m K 9 k * fam m K 11 l := by
        rw [weylOne_conj_fam (n := 4) (n' := 2) (by decide) e,
          weylOne_conj_fam (n := 8) (n' := 6) (by decide) i,
          weylOne_conj_fam (n := 10) (n' := 9) (by decide) k,
          weylOne_conj_fam (n := 11) (n' := 11) (by decide) l]
  have hfix : weylOne K * sylowV m K 0 0 0 0 e 0 0 0 i 0 k l * (weylOne K)⁻¹ =
      sylowV m K 0 0 0 0 e 0 0 0 i 0 k l := by
    rw [h₂, mul_inv_cancel_right]
  have heq : sylowVec m K ![0, 0, e, 0, 0, 0, i, 0, 0, k, 0, l] =
      sylowVec m K ![0, 0, 0, 0, e, 0, 0, 0, i, 0, k, l] := by
    show sylowV m K 0 0 e 0 0 0 i 0 0 k 0 l = sylowV m K 0 0 0 0 e 0 0 0 i 0 k l
    rw [← hconj, hfix]
  have hinj := (bijOn_sylowVec hK).injOn (Set.mem_univ _) (Set.mem_univ _) heq
  have h2 := congrFun hinj 2
  have h6 := congrFun hinj 6
  have h9 := congrFun hinj 9
  simp only [Matrix.cons_val] at h2 h6 h9
  rw [h2, h6, h9]
  exact ⟨l, by rw [← fam_11_eq]; rfl⟩

end Centres

end CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
