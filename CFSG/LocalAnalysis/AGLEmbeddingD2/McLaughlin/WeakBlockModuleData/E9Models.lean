module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Lie2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieTransfer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieHPFive
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.QuasithinUnique CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

section Models

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_psu_odd {n : ℕ} (hc : StatedClassicalModel Y .PSU n 2 1) (hodd : ¬ Even n)
    (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {E : Subgroup Y} (hEJ : E ≤ J) (hE9 : Nat.card E = 9)
    (hsyl : ¬ 3 ∣ (E.subgroupOf J).index) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨-, -, hn, hne⟩, F, hFf, hFfin, hcard, ⟨e⟩⟩ := id hc
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  have hn5 : 5 ≤ n := by
    by_contra h5
    have : n = 3 ∨ n = 4 := by omega
    rcases this with h | h
    · exact hne (by rw [h]; rfl)
    · exact hodd (by rw [h]; decide)
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have hB := borelQuotient_su hcard (by omega) ζ hζ e
  obtain ⟨π', hπ's, hπ'k, hT⟩ := hB.exists_conj_eq T
  have hQ : BorelQuotient (rootDatum hcard n)
      (levelWeyl (unitaryInvolution_involutive hcard) ζ) (levelTorus (unitaryInvolution F 2 1))
      π' (Nat.card F - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ's, odd := hB.odd,
      torus_pow := hB.torus_pow, ker_central := fun z hz => hB.ker_central z (hπ'k ▸ hz),
      ker_pow := fun z hz => hB.ker_pow z (hπ'k ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : ∀ b ∈ borel (rootDatum hcard n) (levelTorus (unitaryInvolution F 2 1)), π' b ∈ J :=
    fun b hb => hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  have hne' : J.comap π' ≠ borel (rootDatum hcard n) (levelTorus (unitaryInvolution F 2 1)) := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ's]
  obtain ⟨k, hk, hLJ⟩ := exists_last_node_le hcard hQ J hBJ hne' hperf
  set L := rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hcard) n) k
    with hL
  have hL216 : Nat.card L = 216 := su_last_odd_card hcard hodd hk
  have hinj : ∀ z ∈ L, π' z = 1 → z = 1 := fun z hzL hz1 =>
    center_inf_rankOne_last_eq_bot hcard hn5 hodd hk (hQ.ker_central z hz1) hzL
  have hLc : Nat.card (L.map π') = 216 := by
    rw [card_map_eq_of_inj_on π' hinj, hL216]
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(L.map π')) 3 (n := 3) (by
    have : Nat.card ↥(L.map π') = 216 := hLc
    rw [this]; norm_num)
  set V : Subgroup Y := K.map (L.map π').subtype with hV
  have hVc : Nat.card V = 27 := by
    rw [hV, Subgroup.card_map_of_injective (L.map π').subtype_injective, hK]; norm_num
  have hV3 : IsPGroup 3 V := IsPGroup.of_card (n := 3) (by rw [hVc]; norm_num)
  have hVJ : V ≤ J := fun v hv => by
    obtain ⟨w, -, rfl⟩ := hv
    show (w : Y) ∈ J
    obtain ⟨l, hl, hlw⟩ := w.2
    rw [← hlw]
    exact Subgroup.mem_comap.mp (hLJ hl)
  obtain ⟨g, -, hg⟩ := exists_conj_into hEJ hE9 hsyl hVJ hV3
  have := card_le_of_conj_into hg
  rw [hVc, hE9] at this
  omega

theorem separated_pair_of_model {t : StatedLieTag} {n : ℕ} (hc : StatedClassicalModel Y t n 2 1)
    (ht : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU)
    (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {E : Subgroup Y} (hEJ : E ≤ J) (hE9 : Nat.card E = 9)
    (hsyl : ¬ 3 ∣ (E.subgroupOf J).index) :
    ∃ e₁ e₂ : ↥J, (e₁ : Y) ∈ E ∧ (e₂ : Y) ∈ E ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧
      ∀ φ : ↥J ≃* ↥J, φ e₁ ≠ e₂ := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := hc
    have := Fintype.ofFinite F
    have hF2 : Nat.card F = 2 := by simpa using hcard
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine exists_separated_pair_of_threePerfect
      (borelQuotient_sl ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm))
      (by rw [hF2]; norm_num) (twoLevi_sl hF2) (fun _ _ h => h.elim)
      (fun i => (hasSL2Node_sl i).hasOrderThree) (fun i => Or.inr ?_) T J hNJ hJ hperf hEJ hE9 hsyl
    obtain ⟨φ, -, hx, hy⟩ := SL.rankOne (F := F) i
    exact card_rankOne_dvd_six_of_sl2 hF2 SL.isParametrization hx hy
  ·
    obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := hc
    have hK2 : Nat.card K = 2 := by simpa using hcard
    have := Fintype.ofFinite K
    have : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
    refine exists_separated_pair_of_threePerfect (borelQuotient_sp e) (by rw [hK2]; norm_num)
      (twoLevi_sp hK2) (fun (i j : Fin n) hij => ?_) (fun i => (hasSL2Node_sp i).hasOrderThree)
      (fun i => Or.inr ?_) T J hNJ hJ hperf hEJ hE9 hsyl
    · rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hj : j = ⟨i.val + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [hj]
        exact sp_tail_exc_three hK2 h1
      · have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [hi, sup_comm]
        exact sp_tail_exc_three hK2 h1
    · obtain ⟨φ, -, hx, hy⟩ := Sp.rankOne (F := K) i
      exact card_rankOne_dvd_six_of_sl2 hK2 Sp.isParametrization hx hy
  ·
    obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := hc
    have := Fintype.ofFinite F
    have hF2 : Nat.card F = 2 := by simpa using hcard
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
    have hn3 : 3 ≤ n := by omega
    have : NeZero n := ⟨by omega⟩
    have : Finite (spinGroup (quadPlus n F)) :=
      finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
    have hB := borelQuotient_spinPlus hn3 e
    refine exists_separated_pair_of_threePerfect hB (by rw [hF2]; norm_num)
      (twoLevi_spinPlus hF2 hn3 hB.ct hB.extras) (fun _ _ h => h.elim)
      (fun i => (hasSL2Node_spinPlus hn3 i).hasOrderThree) (fun i => Or.inr ?_) T J hNJ hJ hperf
      hEJ hE9 hsyl
    obtain ⟨φ, -, hx, hy⟩ := SpinPlus.rankOne (K := F) hn3 i
    exact card_rankOne_dvd_six_of_sl2 hF2 (SpinPlus.isParametrization hn3) hx hy
  ·
    obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := hc
    have := Fintype.ofFinite F
    have hF2 : Nat.card F = 2 := by simpa using hcard
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
    have : Finite (spinGroup (quadMinus n F b c)) :=
      finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
    have hB := borelQuotient_spinMinus hirr (by omega) e
    refine exists_separated_pair_of_threePerfect hB (by rw [hF2]; norm_num)
      (twoLevi_spinMinus hirr hB.ct hB.extras hF2) (fun _ _ h => h.elim)
      (fun i => hasOrderThree_spinMinus hirr i) (fun i => ?_) T J hNJ hJ hperf hEJ hE9 hsyl
    by_cases hk : i.val + 1 < n - 1
    · exact Or.inr (dvd_of_eq (spinMinus_long_card hirr hF2 hk))
    · exact Or.inl (spinMinus_short_perfect hirr hF2 hk)
  ·
    by_cases hev : Even n
    · obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := id hc
      have := Fintype.ofFinite F
      have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
        (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
      have hn4 : 4 ≤ n := by
        obtain ⟨-, -, hn, hne⟩ := hc.1
        by_contra h4
        have : n = 3 := by omega
        exact hne (by rw [this]; rfl)
      obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
      have hB := borelQuotient_su hcard (by omega) ζ hζ e
      refine exists_separated_pair_of_threePerfect hB (by rw [hcard]; norm_num) (twoLevi_su hcard)
        (fun _ _ h => h.elim) (fun i => hasOrderThree_su hcard i) (fun i => ?_) T J hNJ hJ hperf hEJ
        hE9 hsyl
      by_cases hk : i.val + 1 < n / 2
      · exact Or.inl (commutator_eq_self_of_isPerfect (su_short_isPerfect hcard hk))
      · exact Or.inr (dvd_of_eq (su_last_even_card hcard hev hk))
    · exact (false_of_psu_odd hc hev T J hNJ hJ hperf hEJ hE9 hsyl).elim

end Models

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
