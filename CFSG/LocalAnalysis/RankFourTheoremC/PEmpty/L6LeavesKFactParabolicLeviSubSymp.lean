module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubSympBlocks
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubSection

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} {I : Set ℕ}

theorem dvd_card_of_comp_ne_one {G H E : Type} [Group G] [Group H] [Group E] [Finite H]
    (φ : G →* H) (ε : H →* E) {g : G} {p : ℕ} (hp : p.Prime) (hg : g ^ p = 1)
    (h : ε (φ g) ≠ 1) : p ∣ Nat.card H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : φ g ≠ 1 := fun h' => h (by rw [h', map_one])
  have h2 : (φ g) ^ p = 1 := by rw [← map_pow, hg, map_one]
  rw [← orderOf_eq_prime h2 h1]
  exact orderOf_dvd_natCard _

theorem sp_levi_block_exists (hI : ∀ i ∈ I, i ≤ r) (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card K) (hnd : ¬ p ∣ Nat.card K - 1)
    (hpQ : p ∣ Nat.card ↥(flagStabilizer r K I)) :
    ∃ j : Fin (r + 1), CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := K) hI t j) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) ∧
      p ∣ Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) ∧
      (∀ f : ℕ, f ∣ Nat.card K - 1 → f ∣ Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j))) ∧
      (Nat.card K = 2 → 3 ∣ Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(flagStabilizer r K I)) p hpQ
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  have hker := isPGroup_ker_spFlagLeviHom (K := K) hI htI hI1
  have hβ : spFlagLeviHom hI htI g ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := hker ⟨g, h⟩
    have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2k : p ∣ 2 ^ k := hg ▸ orderOf_dvd_of_pow_eq_one hk'
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2k)
    omega
  obtain ⟨j, hj⟩ : ∃ j, spFlagLeviHom hI htI g j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hβ (funext hcon)
  refine ⟨j, ?_⟩
  by_cases hj0 : (j : ℕ) = 0
  ·
    have h : spFlagResEmb t (spFlagResHom hI htI g) ≠ 1 := by
      have h' := hj
      rw [spFlagLeviHom, MonoidHom.pi_apply, spFlagLeviCoord_of_eq_zero hI htI hj0,
        MonoidHom.comp_apply] at h'
      exact h'
    have hdvd := dvd_card_of_comp_ne_one (spFlagResHom hI htI) (spFlagResEmb t) hp hgp h
    rw [SymplecticFlag.card_statedSp] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
    · exact absurd (hp.dvd_of_dvd_pow h1) hpq
    · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h1
      rw [Finset.mem_Icc] at hi
      exact sp_res_block_data hI t hj0 hp h5 hi.1 hi.2 hpi
  · by_cases hjI : (j : ℕ) ∈ I
    ·
      have h : spFlagCutEmb (spFlagPrev I j) j (hI j hjI)
          (spFlagCutHom hI (spFlagPrev_mem I j) hjI g) ≠ 1 := by
        have h' := hj
        rw [spFlagLeviHom, MonoidHom.pi_apply, spFlagLeviCoord_of_mem hI htI hj0 hjI,
          MonoidHom.comp_apply] at h'
        exact h'
      have hdvd := dvd_card_of_comp_ne_one (spFlagCutHom hI (spFlagPrev_mem I j) hjI)
        (spFlagCutEmb (spFlagPrev I j) j (hI j hjI)) hp hgp h
      rw [LinearFlag.card_GL_eq] at hdvd
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
      · exact absurd (hp.dvd_of_dvd_pow h1) hpq
      · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h1
        rw [Finset.mem_Icc] at hi
        have hi2 : 2 ≤ i := by
          by_contra hlt
          have hi1 : i = 1 := by omega
          rw [hi1, pow_one] at hpi
          exact hnd hpi
        exact sp_mem_block_data hI t hj0 hjI hp h5 hi2 hi.2 hpi hnd
    ·
      exfalso
      apply hj
      rw [spFlagLeviHom, MonoidHom.pi_apply, spFlagLeviCoord_of_not_mem hI htI hj0 hjI,
        MonoidHom.one_apply]

theorem leviAt_sp (hr : 2 ≤ r) (K₀ : Subgroup (StatedSp r K)) (p : ℕ)
    (hNB : SymplecticFlag.borelSubgroup r K ≤ K₀) : LeviAt K₀ p := by
  intro hB hp h5 hrank hpar hne hsyl
  classical
  have hp2 : p ≠ 2 := by omega
  have hnd : ¬ p ∣ Nat.card K - 1 := fun h =>
    absurd hrank (by have := two_le_pRank_sp_of_dvd_sub_one hr hp hp2 h; omega)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card K = 2 ^ k := by
    obtain ⟨f, -, hf⟩ := spFlag_card_eq_two_pow (K := K)
    exact ⟨f, hf⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have := Finite.one_lt_card (α := K)
    omega
  have hqeven : 2 ∣ Nat.card K := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  obtain ⟨I, hI, hK₀⟩ : ∃ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i ≤ r) ∧ K₀ = flagStabilizer r K I :=
    ⟨_, SymplecticHigher.borelCuts_le K₀, (SymplecticHigher.borel_overgroups K₀ hNB).1⟩
  subst hK₀
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hI1 : ∀ i ∈ I, 1 ≤ i := fun i hi => (hI i hi).1
  have hIne : I.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne (by rw [h]; exact SymplecticHigher.flagStabilizer_empty)
  obtain ⟨t, htI, hmax⟩ : ∃ t ∈ I, ∀ c ∈ I, c ≤ t :=
    Set.exists_max_image I id ((Set.finite_Icc 1 r).subset fun i hi => ⟨hI1 i hi, hI' i hi⟩) hIne
  have hpQ : p ∣ Nat.card ↥(flagStabilizer r K I) := dvd_card_of_sylow_hyp hp hsyl
  obtain ⟨j, hq, hpZ, hpT, hfT, h3T⟩ := sp_levi_block_exists hI' hI1 htI hp h5 hpq hnd hpQ
  obtain ⟨Y, W, hYQ, hsec, hrel, hWr⟩ := exists_levi_section_of_blocks
    (isPGroup_ker_spFlagLeviHom (K := K) hI' htI hI1) (pi_le_range_spFlagLeviHom hI' htI hmax) j hq
    (flagStabilizer r K I).subtype (fun y _ h => Subtype.ext h)
  rw [Subgroup.range_subtype] at hYQ
  have hpW : ¬ p ∣ Nat.card W := hWr p hp hp2 hpZ
  by_cases hq2 : Nat.card K = 2
  ·
    haveI : NeZero r := ⟨by omega⟩
    have hrk : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSp r K)) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
        (MulEquiv.ofBijective (SymplecticFlag.proj r K)
          UnitaryHigher.proj_bijective_of_charTwo)]
      exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psp hr
    refine ⟨3, Y, W, Nat.prime_three, by norm_num, by omega, hrk, hYQ, hsec, ?_, ?_, hpW⟩
    · rw [hrel]
      exact h3T hq2
    · rw [hrel]
      exact hpT
  ·
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have hq1 : Nat.card K - 1 ≠ 1 := by omega
    have hf : (Nat.card K - 1).minFac.Prime := Nat.minFac_prime hq1
    have hfq : (Nat.card K - 1).minFac ∣ Nat.card K - 1 := Nat.minFac_dvd _
    have hf2 : (Nat.card K - 1).minFac ≠ 2 := by
      intro h2
      have : 2 ∣ Nat.card K - 1 := h2 ▸ hfq
      omega
    refine ⟨(Nat.card K - 1).minFac, Y, W, hf, hf2, fun h => hnd (h ▸ hfq),
      two_le_pRank_sp_of_dvd_sub_one hr hf hf2 hfq, hYQ, hsec, ?_, ?_, hpW⟩
    · rw [hrel]
      exact hfT _ hfq
    · rw [hrel]
      exact hpT

theorem leviSubAt_sp (hr : 2 ≤ r) : LeviSubAt (StatedSp r K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 r
  refine leviSubAt_of_standard_sylow T₀ fun K₀ p hN => leviAt_sp hr K₀ p ?_
  rw [hT₀, SymplecticHigher.normalizer_unipotent] at hN
  exact hN

theorem leviSubAt_of_psp {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) : LeviSubAt S := by
  obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
  have hn2 : 2 ≤ n := by
    obtain ⟨-, -, h2n, -⟩ := hadm
    exact h2n
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  haveI : NeZero n := ⟨by omega⟩
  exact LeviSubAt.of_mulEquiv
    (e.trans (MulEquiv.ofBijective (SymplecticFlag.proj n K)
      UnitaryHigher.proj_bijective_of_charTwo).symm)
    (leviSubAt_sp hn2)

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
