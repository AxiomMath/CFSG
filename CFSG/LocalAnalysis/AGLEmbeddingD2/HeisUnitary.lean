module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisUnitaryTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisUnitaryPart
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisUnitaryArith
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareUnitary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisEngine

public section

namespace CFSG.AGLEmbeddingD2.HeisUnitary

open CFSG.SectionRank CFSG.SectionRank.ClassicalEven CFSG.Assembly.LowTwoRank

section Main

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.ParabRankEngine CFSG.AGLEmbeddingD2.SquareGeneric CFSG.LieType.BorelTits
  CFSG.AGLEmbeddingD2.SquareUnitary Matrix

theorem three_le_pRank_five_su {n f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSU n (2 ^ f) F)) {X : Type} [Group X] [Finite X]
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (h5 : 5 ∣ Nat.card ρ.ker → 5 ∣ n ∧ 5 ∣ 2 ^ f + 1) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (P : Subgroup Y) (hPJ : P ≤ J) (hP : IsPGroup 5 P) (hPc : ¬ IsMulCommutative P) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  classical
  have := Fintype.ofFinite F
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hb := borelQuotient_su hF (by omega) ζ hζ e
  obtain ⟨π', hb', hker', hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Q, hQle, hQ5, hQc⟩ := HeisEngine.exists_nonabelian_le_torus_sup_leviM hb' hBJ
    (p := 5) (by norm_num) hPJ hP hPc
  set I := negIndices (rootDatum hF n) (J.comap π') with hI
  have hBJ' : (borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 f))).map π' ≤ J :=
    Subgroup.map_le_iff_le_comap.mpr hBJ
  have hρ5_of : (¬ 5 ∣ n ∨ ¬ 5 ∣ 2 ^ f + 1) → Nat.Coprime 5 (Nat.card ρ.ker) := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 fun hd => by
      obtain ⟨h1, h2⟩ := h5 hd
      rcases h with h | h <;> contradiction
  have hπ5_of : (¬ 5 ∣ n ∨ ¬ 5 ∣ 2 ^ f + 1) → Nat.Coprime 5 (Nat.card π'.ker) := fun h => by
    rw [hker', card_ker_eq_gcd hF (by omega) e]
    rcases h with h | h
    · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h).coprime_dvd_right
        (Nat.gcd_dvd_left _ _)
    · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h).coprime_dvd_right
        (Nat.gcd_dvd_right _ _)
  have hcomm : ∀ a b : Fin (n / 2), a.val + 2 ≤ b.val →
      Commutes (rankOne (rootDatum hF n).rootGroup a) (rankOne (rootDatum hF n).rootGroup b) :=
    fun a b h => commutes_rankOne_of_cartan_eq_zero hb'.extras
      (fun h' => by rw [h'] at h; omega) (cartan_eq_zero_of_two_le hF h)
  have hπJ : ∀ (a : Fin (n / 2)) (x : SU (unitaryInvolution F 2 f) n),
      x ∈ levelTorus (unitaryInvolution F 2 f) a → π' x ∈ J := fun a x hx =>
    hBJ (le_sup_left (a := ⨆ k, levelTorus (unitaryInvolution F 2 f) k)
      (le_iSup (levelTorus (unitaryInvolution F 2 f)) a hx))
  have hQs : Q ≤ partSU (unitaryInvolution F 2 f) (blkOf n (nodeSet I)) :=
    hQle.trans (torus_sup_leviM_le_partSU hF I)
  by_cases hW : (f % 2 = 1 ∧ n < 20) ∨ (f % 4 = 0 ∧ n < 10) ∨ (f % 4 = 2 ∧ n < 5)
  · exact (hQc (isMulCommutative_of_isPGroup_five_SU hF (by omega) (div_orderOf_lt_five hW)
      hQ5)).elim
  by_cases hfo : f % 2 = 1
  ·
    have hn20 : 20 ≤ n := by
      by_contra h
      exact hW (Or.inl ⟨hfo, by omega⟩)
    by_cases htriple : ∃ a b c : ℕ, a + 2 ≤ b ∧ b + 2 ≤ c ∧ c + 1 < n / 2 ∧ nodeSet I a ∧
        nodeSet I b ∧ nodeSet I c
    · obtain ⟨a, b, c, hab, hbc, hcn, ⟨a_lt, haI⟩, ⟨b_lt, hbI⟩, ⟨c_lt, hcI⟩⟩ := htriple
      let a₀ : Fin (n / 2) := ⟨a, a_lt⟩
      let b₀ : Fin (n / 2) := ⟨b, b_lt⟩
      let c₀ : Fin (n / 2) := ⟨c, c_lt⟩
      exact HeisEngine.three_le_pRank_of_triple (by decide : Odd 5)
        (fun z hz => hb'.ker_central z hz) ρ hρ hρker (hcomm a₀ b₀ hab)
        (hcomm a₀ c₀ (by simp only [a₀, c₀]; omega)) (hcomm b₀ c₀ hbc)
        (realOver_interior_su hF (a := a₀) (by simp only [a₀]; omega)
          (fun g hg => rankOne_le_of_mem_negIndices hBJ haI hg))
        (realOver_interior_su hF (a := b₀) (by simp only [b₀]; omega)
          (fun g hg => rankOne_le_of_mem_negIndices hBJ hbI hg))
        (realOver_interior_su hF (a := c₀) hcn
          (fun g hg => rankOne_le_of_mem_negIndices hBJ hcI hg))
    · have hnt : NoTriple (n / 2) (nodeSet I) := fun a b c h1 h2 h3 h4 h5' h6 =>
        htriple ⟨a, b, c, h1, h2, h3, h4, h5', h6⟩
      refine (hQc (isMulCommutative_of_le_partSU hF (blkOf n (nodeSet I)) hQ5 hQs ?_)).elim
      intro c
      by_cases h10 : Fintype.card {i : Fin n // blkOf n (nodeSet I) i = c} < 10
      · exact Or.inl (Or.inl ⟨hfo, h10⟩)
      · right
        rcases class_card_cases hnt c with h | ⟨-, h20, hrev⟩
        · exact (h10 h).elim
        · have h20' : Fintype.card {i : Fin n // blkOf n (nodeSet I) i = c} < 20 := h20
          refine ⟨by omega, ?_, hrev⟩
          rw [orderOf_neg_two_pow_zmod_five_of_odd f hfo]
          omega
  · have hfe : Even f := ⟨f / 2, by omega⟩
    obtain ⟨ω, hω5, hω1⟩ := exists_order_five hF hfe
    have hω5ord : orderOf ω = 5 := orderOf_eq_prime hω5 hω1
    rcases (by omega : f % 4 = 0 ∨ f % 4 = 2) with hf0 | hf2
    ·
      have hn10 : 10 ≤ n := by
        by_contra h
        exact hW (Or.inr (Or.inl ⟨hf0, by omega⟩))
      have hσω : unitaryInvolution F 2 f (ω : F) = ω :=
        unitaryInvolution_eq_self_of_pow_five hω5 hf0
      have hnot5 : ¬ 5 ∣ 2 ^ f + 1 := by rw [five_dvd_two_pow_add_one_iff]; omega
      have hρ5 := hρ5_of (Or.inr hnot5)
      have hπ5 := hπ5_of (Or.inr hnot5)
      let a : Fin (n / 2) := ⟨0, by omega⟩
      let b : Fin (n / 2) := ⟨1, by omega⟩
      let c : Fin (n / 2) := ⟨2, by omega⟩
      obtain ⟨x, hxH, -, hx5, hx1⟩ := exists_levelTorus_pow hF a ω hω5 hω1 (fun _ _ => hσω)
      obtain ⟨y, hyH, -, hy5, hy1⟩ := exists_levelTorus_pow hF b ω hω5 hω1 (fun _ _ => hσω)
      obtain ⟨z, hzH, -, hz5, hz1⟩ := exists_levelTorus_pow hF c ω hω5 hω1 (fun _ _ => hσω)
      exact (HeisEngine.three_le_pRank_of_torus hb'.extras hπ5 hBJ (a := a) (b := b) (c := c)
        (fun h => absurd (congrArg Fin.val h) (by simp [a, b]))
        (fun h => absurd (congrArg Fin.val h) (by simp [a, c]))
        (fun h => absurd (congrArg Fin.val h) (by simp [b, c])) hxH hyH hzH hx5 hy5 hz5 hx1 hy1
        hz1).trans (HeisEngine.pRank_le_pRank_comap_of_coprime hρ hρ5 J)
    ·
      have hn5 : 5 ≤ n := by
        by_contra h
        exact hW (Or.inr (Or.inr ⟨hf2, by omega⟩))
      by_cases hn56 : n = 5 ∨ n = 6
      · obtain ⟨j, hj⟩ := LieOut.exists_node_not_mem_negIndices hb' hBJ' hJ
        refine (hQc (isMulCommutative_of_le_partSU hF (blkOf n (nodeSet I)) hQ5 hQs
          fun c => Or.inl (Or.inr ⟨by omega, ?_⟩))).elim
        exact class_card_small hn56 (j := j.val) j.isLt (fun ⟨_, hjI⟩ => hj hjI) c
      · have hn7 : 7 ≤ n := by omega
        let a : Fin (n / 2) := ⟨0, by omega⟩
        let b : Fin (n / 2) := ⟨1, by omega⟩
        let c : Fin (n / 2) := ⟨2, by omega⟩
        by_cases h5n : 5 ∣ n
        · have hn10 : 10 ≤ n := by omega
          by_cases hk5 : 5 ∣ Nat.card ρ.ker
          · exact HeisEngine.three_le_pRank_of_pair (by decide : Odd 5)
              (fun z hz => hb'.ker_central z hz) ρ hρ hρker hk5 (hcomm a c (by simp [a, c]))
              (realOver_torus_su hF hBJ (a := a) (by simp [a]; omega) hω5 hω1)
              (realOver_torus_su hF hBJ (a := c) (by simp [c]; omega) hω5 hω1)
          · have hρ5 : Nat.Coprime 5 (Nat.card ρ.ker) :=
              (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hk5
            obtain ⟨x, hxH, hxm, hx5, hx1⟩ := exists_levelTorus_pow hF a ω hω5 hω1
              (fun h => absurd (by simp [a]; omega) h)
            obtain ⟨y, hyH, hym, hy5, hy1⟩ := exists_levelTorus_pow hF b ω hω5 hω1
              (fun h => absurd (by simp [b]; omega) h)
            obtain ⟨z, hzH, hzm, hz5, hz1⟩ := exists_levelTorus_pow hF c ω hω5 hω1
              (fun h => absurd (by simp [c]; omega) h)
            refine (three_le_pRank_of_indep_five (π := π') (J := J)
              (hb'.extras.torus_commute a b x hxH y hyH) (hb'.extras.torus_commute a c x hxH z hzH)
              (hb'.extras.torus_commute b c y hyH z hzH) hx5 hy5 hz5 (hπJ a x hxH) (hπJ b y hyH)
              (hπJ c z hzH) (fun p q r hmem => ?_)).trans
              (HeisEngine.pRank_le_pRank_comap_of_coprime hρ hρ5 J)
            exact torus_triple_dvd_of_central_five hF hζ (a := a) (b := b) (c := c) rfl rfl rfl
              (by omega) hω5ord hxm hym hzm (hb'.ker_central _ hmem)
        · have hρ5 := hρ5_of (Or.inl h5n)
          have hπ5 := hπ5_of (Or.inl h5n)
          obtain ⟨x, hxH, -, hx5, hx1⟩ := exists_levelTorus_pow hF a ω hω5 hω1
            (fun h => absurd (by simp [a]; omega) h)
          obtain ⟨y, hyH, -, hy5, hy1⟩ := exists_levelTorus_pow hF b ω hω5 hω1
            (fun h => absurd (by simp [b]; omega) h)
          obtain ⟨z, hzH, -, hz5, hz1⟩ := exists_levelTorus_pow hF c ω hω5 hω1
            (fun h he => by
              exfalso
              obtain ⟨r, hr⟩ := he
              simp only [c] at h
              omega)
          exact (HeisEngine.three_le_pRank_of_torus hb'.extras hπ5 hBJ (a := a) (b := b) (c := c)
            (fun h => absurd (congrArg Fin.val h) (by simp [a, b]))
            (fun h => absurd (congrArg Fin.val h) (by simp [a, c]))
            (fun h => absurd (congrArg Fin.val h) (by simp [b, c])) hxH hyH hzH hx5 hy5 hz5 hx1
            hy1 hz1).trans (HeisEngine.pRank_le_pRank_comap_of_coprime hρ hρ5 J)

end Main

end CFSG.AGLEmbeddingD2.HeisUnitary
