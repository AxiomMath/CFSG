module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace NoncentralConfig

variable {p : ℕ} {P : Sylow p G} {M D U : Subgroup G} {u : G}
  (hc : NoncentralConfig G p P M D U u)

include hc

theorem PB : (P : Subgroup G) ≤ normalizer ((omegaOneOf p (R P U) : Subgroup G) : Set G) :=
  hc.PR'.trans (normalizer_le_normalizer_omegaOneOf p (R P U))

theorem P_le_M : (P : Subgroup G) ≤ M :=
  (sylow_le_of_isCoreMaxLocal hc.setting hc.sigma hc.ext.obstruction.1).1

theorem commutator_pCore_ne_bot :
    ⁅omegaOneOf p (R P U), pCoreOf 2 M ⊓ centralizer ({u} : Set G)⁆ ≠ ⊥ := by
  classical
  intro H0
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  set B : Subgroup G := omegaOneOf p (R P U) with hBdef
  set T : Subgroup G := pCoreOf 2 M with hTdef
  have hMc := hc.ext.obstruction.1
  have hPM := hc.P_le_M
  have hTnorm : M ≤ normalizer (T : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hBC : B ≤ centralizer ((T ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 H0
  have hconj : ∀ n ∈ (P : Subgroup G), ∀ b ∈ B, ∀ t ∈ T,
      t ∈ centralizer ({n * u * n⁻¹} : Set G) → b * t = t * b := by
    intro n hn b hb t ht htc
    have hn' : n⁻¹ ∈ (P : Subgroup G) := (P : Subgroup G).inv_mem hn
    have hb' : n⁻¹ * b * n ∈ B := by
      have := (mem_normalizer_iff.mp (hc.PB hn') b).mp hb
      simpa using this
    have ht' : n⁻¹ * t * n ∈ T := by
      have := (mem_normalizer_iff.mp (hTnorm (hPM hn')) t).mp ht
      simpa using this
    have htu : n⁻¹ * t * n ∈ centralizer ({u} : Set G) := by
      refine mem_centralizer_singleton_iff.mpr ?_
      have h1 : t * (n * u * n⁻¹) = (n * u * n⁻¹) * t := mem_centralizer_singleton_iff.mp htc
      calc n⁻¹ * t * n * u = n⁻¹ * (t * (n * u * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * u * n⁻¹) * t) * n := by rw [h1]
        _ = u * (n⁻¹ * t * n) := by group
    have h2 := mem_centralizer_iff.mp (hBC hb') (n⁻¹ * t * n) ⟨ht', htu⟩
    calc b * t = n * ((n⁻¹ * b * n) * (n⁻¹ * t * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * t * n) * (n⁻¹ * b * n)) * n⁻¹ := by rw [h2]
      _ = t * b := by group
  obtain ⟨z, hzZ, hz1, hordz, hzeq⟩ := hc.exists_Z_gen
  have hzU : z ∈ U := hc.Z_le_U hzZ
  have hzB : z ∈ B := hc.U_le_B hzU
  have hTp : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hVp : ¬ p ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTp
    rw [hn]
    intro h
    exact hc.odd ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hprime h))
  have : IsElementaryAbelian p U :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).2 hc.Ue
  have : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hc.Uc]
    exact Nat.one_lt_pow (by norm_num) hprime.one_lt)
  have hAV : U ≤ normalizer (T : Set G) := (hc.U_le_P.trans hPM).trans hTnorm
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) hAV hVp
  obtain ⟨x₀, hx₀P, hx₀⟩ := hc.exists_not_comm
  have hx₀C : x₀ ∉ centralizer (U : Set G) := fun h =>
    hx₀ (mem_centralizer_iff.mp h u hc.uU).symm
  have hTz : T ≤ centralizer ({z} : Set G) := by
    refine hgen.trans (iSup₂_le fun B' hB' => ?_)
    set ℓ : Subgroup G := B'.map U.subtype with hℓdef
    by_cases hzℓ : z ∈ ℓ
    · exact inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr hzℓ))
    · have hℓc : Nat.card ℓ = p := by
        have h1 := B'.card_mul_index
        rw [hB', hc.Uc] at h1
        have : Nat.card B' * p = p * p := by rw [h1]; ring
        have h2 : Nat.card B' = p := Nat.eq_of_mul_eq_mul_right hprime.pos this
        rw [hℓdef, card_map_of_injective U.subtype_injective, h2]
      have hℓne : ℓ ≠ ⊥ := (one_lt_card_iff_ne_bot ℓ).1 (hℓc ▸ hprime.one_lt)
      obtain ⟨⟨w, hwℓ⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hℓne
      have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
      have hwU : w ∈ U := map_subtype_le B' hwℓ
      have hwp : w ^ p = 1 := hc.pow_U hwU
      have hordw : orderOf w = p := orderOf_eq_prime hwp hw1'
      have hℓeq : zpowers w = ℓ := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwℓ)
        (by rw [hℓc, Nat.card_zpowers, hordw])
      have hwz : w ∉ zpowers z := by
        intro hwz
        apply hzℓ
        have hle : zpowers w ≤ zpowers z := zpowers_le.mpr hwz
        have heq : zpowers w = zpowers z := Subgroup.eq_of_le_of_card_ge hle
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hordw, hordz])
        rw [← hℓeq, heq]
        exact mem_zpowers z
      have hdz : u ∉ zpowers z := by
        rw [hzeq]
        exact hc.uZ
      obtain ⟨k, hk⟩ := exists_pow_conj_zpowers_eq hc.Ue hc.Uc hzU hz1
        (P.isPGroup' ⟨x₀, hx₀P⟩ |>.imp fun k hk => by simpa using congrArg Subtype.val hk)
        (hc.PU hx₀P) (hc.Z_comm hzZ hx₀P) hx₀C hc.uU hdz hwU hwz
      intro t ht
      obtain ⟨htT, htℓ⟩ := ht
      have hcz : z * t = t * z := by
        refine hconj (x₀ ^ k) (pow_mem hx₀P k) z hzB t htT ?_
        refine mem_centralizer_singleton_iff.mpr ?_
        have hmem : x₀ ^ k * u * (x₀ ^ k)⁻¹ ∈ ℓ := by
          rw [← hℓeq, ← hk]
          exact mem_zpowers _
        exact (mem_centralizer_iff.mp htℓ _ hmem).symm
      exact mem_centralizer_singleton_iff.mpr hcz.symm
  have hzp : IsPGroup p (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordz, pow_one])
  have hzM : zpowers z ≤ M := zpowers_le.mpr (hPM (hc.U_le_P hzU))
  have hcent : zpowers z ≤ centralizer (T : Set G) :=
    zpowers_le.mpr (mem_centralizer_iff.mpr fun t ht =>
      mem_centralizer_singleton_iff.mp (hTz ht))
  have hbot := charTwo_odd_pGroup_centralizing_core_eq_bot hc.setting.charTwo M hMc.1.1 p hprime
    hc.odd (zpowers z) hzp hzM hcent
  exact hz1 (by simpa using (mem_bot.mp (hbot ▸ mem_zpowers z)))

theorem glbPrimeCore_le_M : GLBPrimeCore p (centralizer ({u} : Set G)) ≤ M := by
  have h3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
    rw [hc.inf_centralizer_eq]
    exact hc.rank3
  exact (glbPrimeCore_le_pPrimeCoreIn p _).trans
    (pPrimeCoreIn_centralizer_le hc.setting hc.sigma hc.ext.obstruction.1 h3)

theorem centralizer_le_of_commutator_le (hD1 : TheoremD1 G)
    (hC : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ centralizer ({u} : Set G) →
      omegaOneOf p (R P U) ≤ normalizer (T : Set G) →
        ⁅omegaOneOf p (R P U), T⁆ ≤ GLBPrimeCore p (centralizer ({u} : Set G))) :
    centralizer ({u} : Set G) ≤ M := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  set B : Subgroup G := omegaOneOf p (R P U) with hBdef
  set Cu : Subgroup G := centralizer ({u} : Set G) with hCudef
  set O : Subgroup G := GLBPrimeCore p Cu with hOdef
  have hMc := hc.ext.obstruction.1
  have hPM := hc.P_le_M
  have hOM : O ≤ M := hc.glbPrimeCore_le_M
  have hBe := hc.isElemAbelian_B
  have hBR : B ≤ R P U := B_le_R
  have hBCu : B ≤ Cu := hBR.trans hc.R_le_centralizer
  have hBM : B ≤ M := (B_le_P).trans hPM
  set T₀ : Subgroup G := pCoreOf 2 M ⊓ Cu with hT₀def
  have hT₀2 : IsPGroup 2 T₀ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hBN : B ≤ normalizer (T₀ : Set G) :=
    (le_inf (hBM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (hBCu.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hcomm_le : ⁅B, T₀⁆ ≤ O := hC T₀ hT₀2 inf_le_right hBN
  have hcomm_ne : ⁅B, T₀⁆ ≠ ⊥ := hc.commutator_pCore_ne_bot
  have hcomm_T : ⁅B, T₀⁆ ≤ T₀ := by
    rw [Subgroup.commutator_le]
    intro b hb t ht
    have h1 := (mem_normalizer_iff.mp (hBN hb) t).mp ht
    show b * t * b⁻¹ * t⁻¹ ∈ T₀
    exact T₀.mul_mem h1 (T₀.inv_mem ht)
  have hcomm2 : IsPGroup 2 ↥⁅B, T₀⁆ := hT₀2.to_le hcomm_T
  have h2dvd : 2 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hcomm2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hcomm_ne ((Subgroup.card_eq_one).mp hk)
    exact (dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hcomm_le)
  have hBO : B ≤ normalizer (O : Set G) :=
    hBCu.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p Cu)
  have hcop : Nat.Coprime p (Nat.card O) := CFSG.AGLEmbedding.glbPrimeCore_coprime p Cu
  obtain ⟨S, hSB, hSne⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
    p 2 hprime Nat.prime_two B O (elementary_isPGroup p B hBe) hBO hcop h2dvd
  set S' : Subgroup G := (S : Subgroup O).map O.subtype with hS'def
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map O.subtype
  have hN2 : IsTwoLocal (normalizer (S' : Set G)) := ⟨S', hSne, hS'2, rfl⟩
  have hBcard : 3 ≤ CFSG.Open.pRank p (normalizer (S' : Set G) ⊓ M) := by
    have h3 : 3 ≤ CFSG.Open.pRank p B := by
      unfold CFSG.Open.pRank
      exact (Nat.le_refl 3).trans (le_csSup (pRank_set_bddAbove p hprime.one_lt _)
        ⟨_, le_rfl, hBe, hc.card_B⟩)
    exact h3.trans (pRank_mono p hprime.one_lt (le_inf hSB hBM))
  have hNM := le_of_three_le_pRank_inf hD1 hc.sigma hMc hN2 hBcard
  have hSsyl : IsSylowOf 2 S' O := ⟨S, rfl⟩
  exact (le_sup_normalizer_of_isSylowOf (p := 2) (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p Cu)
    hSsyl).trans (sup_le hOM hNM)

end NoncentralConfig

end CFSG.LocalAnalysis.RankThreeTheoremC
