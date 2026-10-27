module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubLinRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubLinBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup Matrix CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem dvd_of_sq_dvd_mul {z t q : ℕ} (hz : 0 < z) (hzq : z ∣ q) (hq : q ^ 2 ∣ z * t) :
    q ∣ t := by
  obtain ⟨u, rfl⟩ := hzq
  have h1 : z * (z * u ^ 2) ∣ z * t := by
    have : (z * u) ^ 2 = z * (z * u ^ 2) := by ring
    rwa [this] at hq
  have h2 : z * u ^ 2 ∣ t := Nat.dvd_of_mul_dvd_mul_left hz h1
  exact (Dvd.intro u (by ring) : z * u ∣ z * u ^ 2).trans h2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem card_linBlock_eq {I : Set ℕ} (a : Fin n) (hm : 1 ≤ linBlockLen n I a) :
    Nat.card ↥(linBlockSL K n I a) =
      Nat.card K ^ (linBlockLen n I a * (linBlockLen n I a - 1) / 2) *
        ∏ j ∈ Finset.Icc 2 (linBlockLen n I a), (Nat.card K ^ j - 1) := by
  rw [← Nat.card_congr (slEquivToGLRange (K := K) (linBlockLen n I a)).toEquiv]
  exact card_SL_eq hm

theorem card_linBlock_mul {I : Set ℕ} (a : Fin n) :
    Nat.card ↥(linBlockSL K n I a) = Nat.card (blockQuot K n I a) *
      Nat.card (Subgroup.center ↥(linBlockSL K n I a)) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem dvd_card_blockQuot {I : Set ℕ} (a : Fin n) (hm : 2 ≤ linBlockLen n I a) {p j : ℕ}
    (hp : p.Prime) (hj2 : 2 ≤ j) (hjm : j ≤ linBlockLen n I a) (hpj : p ∣ Nat.card K ^ j - 1)
    (hnd : ¬ p ∣ Nat.card K - 1) : p ∣ Nat.card (blockQuot K n I a) := by
  have h1 : p ∣ Nat.card ↥(linBlockSL K n I a) := by
    rw [card_linBlock_eq a (by omega)]
    exact Dvd.dvd.mul_left (hpj.trans (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1)
      (Finset.mem_Icc.2 ⟨hj2, hjm⟩))) _
  rw [card_linBlock_mul a] at h1
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
  · exact h
  · exact absurd (h.trans (card_center_linBlockSL_dvd a (by omega))) hnd

theorem card_center_linBlockSL_eq_one {I : Set ℕ} (a : Fin n)
    (hm : linBlockLen n I a = 2) : Nat.card (Subgroup.center ↥(linBlockSL K n I a)) = 1 := by
  have key : ∀ m : ℕ, m = 2 → scalars m K = ⊥ := by
    rintro m rfl
    exact CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot K
  rw [card_center_linBlockSL_eq, key _ hm, Subgroup.card_bot]

theorem dvd_card_blockQuot_of_dvd_sub_one {I : Set ℕ} (a : Fin n)
    (hm : 2 ≤ linBlockLen n I a) {f : ℕ} (hf : f ∣ Nat.card K - 1) :
    f ∣ Nat.card (blockQuot K n I a) := by
  have hX := card_linBlock_eq (K := K) (I := I) a (by omega)
  have hmul := card_linBlock_mul (K := K) (I := I) a
  have hz := card_center_linBlockSL_dvd (K := K) (I := I) a (by omega)
  have hzpos : 0 < Nat.card (Subgroup.center ↥(linBlockSL K n I a)) := Nat.card_pos
  have hdvdq2 : ∀ j : ℕ, 1 ≤ j → Nat.card K - 1 ∣ Nat.card K ^ j - 1 := by
    intro j _
    exact Nat.sub_one_dvd_pow_sub_one (Nat.card K) j
  rcases Nat.lt_or_ge (linBlockLen n I a) 3 with hlt | hge
  · have hm2 : linBlockLen n I a = 2 := by omega
    have hz1 := card_center_linBlockSL_eq_one (K := K) (I := I) a hm2
    have hXT : Nat.card ↥(linBlockSL K n I a) = Nat.card (blockQuot K n I a) := by
      rw [hmul, hz1, mul_one]
    refine hf.trans ((hdvdq2 2 (by omega)).trans ?_)
    have h2 : Nat.card K ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 (linBlockLen n I a), (Nat.card K ^ j - 1) :=
      Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1) (Finset.mem_Icc.2 ⟨le_rfl, hm⟩)
    rw [← hXT, hX]
    exact Dvd.dvd.mul_left h2 _
  · have hsq : (Nat.card K - 1) ^ 2 ∣ Nat.card ↥(linBlockSL K n I a) := by
      rw [hX]
      refine Dvd.dvd.mul_left ?_ _
      have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (linBlockLen n I a) := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_Icc]
        omega
      have h23 := Finset.prod_dvd_prod_of_subset _ _ (fun j => Nat.card K ^ j - 1) hsub
      rw [Finset.prod_pair (by norm_num)] at h23
      refine (?_ : (Nat.card K - 1) ^ 2 ∣ (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)).trans h23
      rw [pow_two]
      exact mul_dvd_mul (hdvdq2 2 (by omega)) (hdvdq2 3 (by omega))
    rw [hmul, mul_comm] at hsq
    exact hf.trans (dvd_of_sq_dvd_mul hzpos hz hsq)

theorem three_dvd_card_blockQuot {I : Set ℕ} (a : Fin n) (hm : 2 ≤ linBlockLen n I a)
    (hq : Nat.card K = 2) : 3 ∣ Nat.card (blockQuot K n I a) := by
  have hX := card_linBlock_eq (K := K) (I := I) a (by omega)
  have hmul := card_linBlock_mul (K := K) (I := I) a
  have hz := card_center_linBlockSL_dvd (K := K) (I := I) a (by omega)
  rw [hq] at hz
  have hz1 : Nat.card (Subgroup.center ↥(linBlockSL K n I a)) = 1 := Nat.dvd_one.1 hz
  have hXT : Nat.card ↥(linBlockSL K n I a) = Nat.card (blockQuot K n I a) := by
    rw [hmul, hz1, mul_one]
  rw [← hXT, hX, hq]
  refine Dvd.dvd.mul_left ?_ _
  have h2 : 2 ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 (linBlockLen n I a), (2 ^ j - 1) :=
    Finset.dvd_prod_of_mem (fun j => 2 ^ j - 1) (Finset.mem_Icc.2 ⟨le_rfl, hm⟩)
  simpa using h2

theorem leviAt_projectiveSL [CharP K 2] (hn : 3 ≤ n) (K₀ : Subgroup (projectiveSL n K)) (p : ℕ)
    (hNB : projUpperTriangular n K ≤ K₀) : LeviAt K₀ p := by
  intro hB hp h5 hrank hpar hne hsyl
  classical
  have hn1 : 1 ≤ n := by omega
  have hnd : ¬ p ∣ Nat.card K - 1 := not_dvd_sub_one_of_pRank_le_one hn hp h5 hrank
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card K = 2 ^ k := by
    haveI := Fintype.ofFinite K
    obtain ⟨k, -, hk⟩ := FiniteField.card K 2
    exact ⟨k, by rw [Nat.card_eq_fintype_card, hk]⟩
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  set A : Subgroup (SpecialLinearGroup (Fin n) K) := K₀.comap (proj n K) with hAdef
  have hA : upperTriangular n K ≤ A := fun b hb => hNB ⟨b, hb, rfl⟩
  obtain ⟨hAeq, -⟩ := borel_overgroups A hA
  set I := borelOvergroupCuts A with hIdef
  have hK₀ : K₀ = (flagStabilizer n K I).map (proj n K) := by
    rw [← hAeq]
    exact (Subgroup.map_comap_eq_self_of_surjective (proj_surjective n K) K₀).symm
  have hIne : I.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hne
    rw [hK₀, h, flagStabilizer_empty, Subgroup.map_top_of_surjective _ (proj_surjective n K)]
  obtain ⟨c, hcI⟩ := hIne
  have hcI' : c ∈ I := hcI
  obtain ⟨hc1, hcn, -⟩ := hcI
  have hpQ : p ∣ Nat.card ↥(flagStabilizer n K I) := by
    have h1 := dvd_card_of_sylow_hyp hp hsyl
    rw [hK₀] at h1
    exact h1.trans (Subgroup.card_map_dvd _ _)
  obtain ⟨a, j, hj2, hjm, hpj⟩ : ∃ (a : Fin n) (j : ℕ), 2 ≤ j ∧ j ≤ linBlockLen n I a ∧
      p ∣ Nat.card K ^ j - 1 := by
    have hker2 := isPGroup_ker_linLeviHom (K := K) (n := n) (I := I) hn1
    have hcardQ : Nat.card ↥(flagStabilizer n K I) =
        Nat.card ↥(linLeviHom K n I).range * Nat.card ↥(linLeviHom K n I).ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (linLeviHom K n I).ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange (linLeviHom K n I)).toEquiv]
    have hpker : ¬ p ∣ Nat.card ↥(linLeviHom K n I).ker := by
      obtain ⟨k', hk'⟩ := hker2.exists_card_eq
      rw [hk']
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
      omega
    have hprange : p ∣ Nat.card ↥(linLeviHom K n I).range := by
      rw [hcardQ] at hpQ
      exact ((Nat.Prime.dvd_mul hp).1 hpQ).resolve_right hpker
    have hrange_dvd : Nat.card ↥(linLeviHom K n I).range ∣
        ∏ b : Fin n, Nat.card (GL (Fin (linBlockLen n I b)) K) := by
      rw [← Nat.card_pi]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨b, -, hb⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 (hprange.trans hrange_dvd)
    rw [card_GL_eq] at hb
    rcases (Nat.Prime.dvd_mul hp).1 hb with h1 | h1
    · exact absurd (hp.dvd_of_dvd_pow h1) hpq
    · obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h1
      rw [Finset.mem_Icc] at hj
      refine ⟨b, j, ?_, hj.2, hpj⟩
      by_contra hj1
      have : j = 1 := by omega
      rw [this, pow_one] at hpj
      exact hnd hpj
  have hm2 : 2 ≤ linBlockLen n I a := by omega
  have hastart : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I := by
    by_contra hna
    have h0 : linBlockLen n I a = 0 := linBlockLen_of_not_start hna
    omega
  have hqeven : 2 ∣ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      omega
    rw [hk]
    exact dvd_pow_self 2 hk0
  have hstart : ∀ b : Fin n, ((b : ℕ) = 0 ∨ (b : ℕ) ∈ I) → 1 ≤ linBlockLen n I b :=
    fun b hb => (linBlockLen_spec hb).2.1
  have hb : ∃ b : Fin n, b ≠ a ∧ 1 ≤ linBlockLen n I b := by
    by_cases ha0 : (a : ℕ) = 0
    · refine ⟨⟨c, hcn⟩, fun h => ?_, hstart _ (Or.inr hcI')⟩
      have := congrArg Fin.val h
      simp only at this
      omega
    · refine ⟨⟨0, by omega⟩, fun h => ?_, hstart _ (Or.inl rfl)⟩
      have := congrArg Fin.val h
      simp only at this
      omega
  have hmn : linBlockLen n I a + 1 ≤ n := by
    obtain ⟨h1, -, -, h4⟩ := linBlockLen_spec hastart
    by_cases ha0 : (a : ℕ) = 0
    · have h5' := h4 c hcI'
      omega
    · omega
  have hq : 3 ≤ linBlockLen n I a ∨ ∃ s : Finset K, s.card = 4 := by
    by_cases h3 : 3 ≤ linBlockLen n I a
    · exact Or.inl h3
    · right
      have hj : j = 2 := by omega
      subst hj
      have hq4 : 4 ≤ Nat.card K := by
        by_contra hlt
        have h1 : 1 < Nat.card K := Finite.one_lt_card
        have hq2 : Nat.card K = 2 := by omega
        rw [hq2] at hpj
        have h3 : p ∣ 3 := by simpa using hpj
        have := Nat.le_of_dvd (by norm_num) h3
        omega
      haveI := Fintype.ofFinite K
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hq4)
      exact ⟨s, hs⟩
  have hX : CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a) :=
    isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) (linBlockLen n I a))
      ⟨(CFSG.LinearGroups.special_linear_isPerfect hm2 hq).commutator_eq_top,
        (CFSG.LinearGroups.linear_projective_simple hm2 hq).2.1⟩
  obtain ⟨Y, W, hYK, hsec, hrel, hWr⟩ := exists_levi_section_linear (K := K) hn1 I a hm2 hb hX
  have hpW : ¬ p ∣ Nat.card W := hWr p hp (by omega) hnd
  have hpT : p ∣ Nat.card (blockQuot K n I a) := dvd_card_blockQuot a hm2 hp hj2 hjm hpj hnd
  have hYK₀ : Y ≤ K₀ := by rw [hK₀]; exact hYK
  by_cases hq2 : Nat.card K = 2
  ·
    have hj3 : 3 ≤ j := by
      by_contra hj3
      have hj : j = 2 := by omega
      subst hj
      rw [hq2] at hpj
      have h3 : p ∣ 3 := by simpa using hpj
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    have h4 : 4 ≤ n := by omega
    have hrk : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL n K)) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
        (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj n K)]
      exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psl h4
    refine ⟨3, Y, W, Nat.prime_three, by norm_num, by omega, hrk, hYK₀, hsec, ?_, ?_, hpW⟩
    · rw [hrel]
      exact three_dvd_card_blockQuot a hm2 hq2
    · rw [hrel]
      exact hpT
  ·
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have hq4 : 3 ≤ Nat.card K - 1 := by omega
    have hq1 : Nat.card K - 1 ≠ 1 := by omega
    have hf : (Nat.card K - 1).minFac.Prime := Nat.minFac_prime hq1
    have hfq : (Nat.card K - 1).minFac ∣ Nat.card K - 1 := Nat.minFac_dvd _
    have hf2 : (Nat.card K - 1).minFac ≠ 2 := by
      intro h2
      have : 2 ∣ Nat.card K - 1 := h2 ▸ hfq
      omega
    refine ⟨(Nat.card K - 1).minFac, Y, W, hf, hf2, fun h => hnd (h ▸ hfq),
      two_le_pRank_psl_of_dvd_sub_one hn hf hf2 hfq, hYK₀, hsec, ?_, ?_, hpW⟩
    · rw [hrel]
      exact dvd_card_blockQuot_of_dvd_sub_one a hm2 hfq
    · rw [hrel]
      exact hpT

theorem leviSubAt_projectiveSL (hn : 3 ≤ n) : LeviSubAt (projectiveSL n K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := n) (by omega)
  refine leviSubAt_of_standard_sylow T₀ fun K₀ p hN => leviAt_projectiveSL hn K₀ p ?_
  have h1 := normalizer_projUnitriangular (K := K) (n := n) 2
  rw [← hT₀] at h1
  rw [← h1]
  exact hN

theorem leviSubAt_of_psl {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSL n 2 f) : LeviSubAt S := by
  by_cases hn2 : n = 2
  · subst hn2
    intro K₀ p hB
    exact absurd (CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isPSL h) hB
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
    have hn3 : 3 ≤ n := by
      obtain ⟨-, -, h2n, -⟩ := hadm
      omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    exact LeviSubAt.of_mulEquiv
      (e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj n K).symm)
      (leviSubAt_projectiveSL hn3)

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
