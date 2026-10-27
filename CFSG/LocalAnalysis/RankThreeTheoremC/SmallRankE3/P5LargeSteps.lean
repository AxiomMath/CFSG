module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5Large
import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
public import CFSG.LocalAnalysis.RankFourTheoremC.Refined
public import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SigmaA

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def SlotP614NormalizerRankLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
    ∀ (p : ℕ), 5 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ¬ HasPrimeConstraint (G := M) p →
        ∀ T : Subgroup G, IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T →
          CFSG.Open.pRank p (P : Subgroup G) ≤ CFSG.Open.pRank p (M ⊓ normalizer (T : Set G))

@[expose] def SlotP614StepL617Large : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
    ∀ (p : ℕ), 5 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ∀ H S : Subgroup G, Fail614OptimalGen p M x z H S → rankThreePrimeCore p H ≤ M

@[expose] def SlotP614OmegaULarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
    ∀ (p : ℕ), 5 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ∀ H S : Subgroup G, Fail614OptimalGen p M x z H S → rankThreePrimeCore p H ≤ M →
          ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
            (∃ q ∈ Q, q ^ p = 1 ∧ q ∉ zpowers x ⊔ zpowers z) →
              ∃ U : Subgroup G, U ≤ Q ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧
                ∀ u ∈ U, u ≠ 1 → 3 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({u} : Set G))

@[expose] def SlotP614LargeD2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
    ∀ (p : ℕ), p ≠ 3 → ∀ (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G p P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
        zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M

variable {G : Type} [Group G] [Finite G]

private theorem three_not_mem_sigmaA_of_five_le (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) (hp5 : 5 ≤ p) : 3 ∉ rankThreeSigmaA G := by
  intro h3
  have hrank := hS.rank
  by_cases h5 : p = 5
  · subst h5
    have := CFSG.LocalAnalysis.RankThreeUC.S15.sigmaA_eq_five hrank hp
    rw [this, Set.mem_singleton_iff] at h3
    omega
  · have h7 : 7 ≤ p := CFSG.LocalAnalysis.RankThreeUC.S15.seven_le_of_mem_sigmaA hrank hp
      (by omega) h5
    have := CFSG.LocalAnalysis.RankThreeUC.S15.seven_le_of_mem_sigmaA_of_seven_le hrank hp h7 3 h3
    omega

private theorem normalizer_zpowers_le_normalizer_centralizer' (u : G) :
    normalizer ((zpowers u : Subgroup G) : Set G) ≤
      normalizer ((centralizer ({u} : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer ((zpowers u : Subgroup G) : Set G), ∀ c ∈ centralizer ({u} : Set G),
      g * c * g⁻¹ ∈ centralizer ({u} : Set G) := by
    intro g hg c hc
    have hgu : g⁻¹ * u * g ∈ zpowers u := (mem_normalizer_iff''.mp hg u).mp (mem_zpowers u)
    obtain ⟨m, hm⟩ := hgu
    have hcu : c * u = u * c := mem_centralizer_singleton_iff.mp hc
    have hcm : c * u ^ m = u ^ m * c := ((Commute.zpow_right (Commute.symm hcu.symm) m) :)
    rw [mem_centralizer_singleton_iff]
    have hum : g⁻¹ * u * g = u ^ m := hm.symm
    calc g * c * g⁻¹ * u = g * c * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = g * (c * u ^ m) * g⁻¹ := by rw [hum]; group
      _ = g * (u ^ m * c) * g⁻¹ := by rw [hcm]
      _ = g * (g⁻¹ * u * g) * c * g⁻¹ := by rw [hum]; group
      _ = u * (g * c * g⁻¹) := by group
  intro g hg
  refine mem_normalizer_iff.mpr fun c => ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  simpa [mul_assoc] using this

private theorem normalizer_zpowers_le_of_centralizer_rank3 (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M : Subgroup G} (hsit : SmallRankSituation G p P M) {u : G}
    (hCM : centralizer ({u} : Set G) ≤ M)
    (hC2 : 2 ≤ CFSG.Open.pRank p (centralizer ({u} : Set G))) :
    normalizer ((zpowers u : Subgroup G) : Set G) ≤ M := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (centralizer ({u} : Set G))
  have hSM : S ≤ M := hSyl.le.trans hCM
  have hS2 : 2 ≤ CFSG.Open.pRank p S := by
    have := pRank_eq_of_isSylowOf3 hp hSyl
    omega
  have hNS : normalizer (S : Set G) ≤ M :=
    normalizer_le_of_gamma_two hS hsit.mem_sigmaA hsit.isCoreMaxLocal hsit.gamma_two_le
      hSyl.isPGroup hSM hS2
  have hnC := normalizer_zpowers_le_normalizer_centralizer' u
  exact (le_sup_normalizer_of_isSylowOf hnC hSyl).trans (sup_le hCM hNS)

theorem omega_le_of_omegaU (hS : Setting G) (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G)
    {p : ℕ} (hp5 : 5 ≤ p) {P : Sylow p G} {M : Subgroup G} (hsit : SmallRankSituation G p P M)
    {x z : G} {H S : Subgroup G} (hopt : Fail614OptimalGen p M x z H S)
    {Q : Subgroup G} (hQH : Q ≤ H) (hQp : IsPGroup p Q) (hBQ : zpowers x ⊔ zpowers z ≤ Q)
    {q : G} (hqQ : q ∈ Q) (hq1 : q ^ p = 1)
    (hΩU : (∃ q ∈ Q, q ^ p = 1 ∧ q ∉ zpowers x ⊔ zpowers z) →
      ∃ U : Subgroup G, U ≤ Q ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧
        ∀ u ∈ U, u ≠ 1 → 3 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({u} : Set G))) :
    q ∈ zpowers x ⊔ zpowers z := by
  by_contra hqB
  obtain ⟨U, hUQ, hUe, hUc, hUr⟩ := hΩU ⟨q, hqQ, hq1, hqB⟩
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hp⟩
  have hQM : Q ≤ M := hopt.sylow_le Q hQp hQH hBQ
  have hUM : U ≤ M := hUQ.trans hQM
  have hUp : IsPGroup p U := elementary_isPGroup p U hUe
  have hUrank : CFSG.Open.pRank p U = 2 :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isElemAbelian hp hUe hUc
  have hcore : rankThreeGamma 1 p U ≤ M := by
    rw [gamma_le_iff]
    intro S' hS'U hrank
    by_cases h2 : 2 ≤ CFSG.Open.pRank p S'
    · exact normalizer_le_of_gamma_two hS hsit.mem_sigmaA hsit.isCoreMaxLocal
        hsit.gamma_two_le (hUp.to_le hS'U) (hS'U.trans hUM) h2
    ·
      have hrk : CFSG.Open.pRank p S' = 1 := by omega
      have hS'e : IsElemAbelian p S' :=
        CFSG.LocalAnalysis.RankFourTheoremC.isElemAbelian_mono hUe hS'U
      obtain ⟨k, hk⟩ := (hUp.to_le hS'U).exists_card_eq
      have hk1 : k = 1 := by
        have := CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isElemAbelian hp hS'e hk
        omega
      subst hk1
      have hne : S' ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hk
        have := hp.one_lt
        simp at hk
        omega
      obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      have hgS' : (g : G) ∈ S' := g.2
      have hg1' : (g : G) ≠ 1 := fun h => hg1 (Subtype.ext h)
      have hgp : (g : G) ^ p = 1 := hUe.2 (g : G) (hS'U hgS')
      have hgo : orderOf (g : G) = p := orderOf_eq_prime hgp hg1'
      have hzS : zpowers (g : G) = S' := by
        refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hgS') ?_
        rw [Nat.card_zpowers, hgo, hk]
        simp
      rw [← hzS]
      have hgM : (g : G) ∈ M := hUM (hS'U hgS')
      have h3 := hUr (g : G) (hS'U hgS') hg1'
      have hCM : centralizer ({(g : G)} : Set G) ≤ M := by
        by_contra hCM
        exact hsit.largeObstruction_empty (g : G)
          ⟨hgM, hg1', hgp, h3.trans (CFSG.SectionRank.pRank_mono hp.one_lt
            (inf_le_right : M ⊓ centralizer ({(g : G)} : Set G) ≤
              centralizer ({(g : G)} : Set G))), hCM⟩
      have hC2 : 2 ≤ CFSG.Open.pRank p (centralizer ({(g : G)} : Set G)) :=
        le_trans (by omega) (le_trans h3
          (CFSG.SectionRank.pRank_mono hp.one_lt (inf_le_right :
            M ⊓ centralizer ({(g : G)} : Set G) ≤ centralizer ({(g : G)} : Set G))))
      exact normalizer_zpowers_le_of_centralizer_rank3 hS hsit hCM hC2
  have h3 := three_not_mem_sigmaA_of_five_le hS hsit.mem_sigmaA hp5
  have hHM : H ≤ M :=
    hD2 M hsit.isCoreMaxLocal.1
      (fun p' hp' P' hcore' => hU0 p' hp' P' M hcore')
      (fun h3' => absurd h3' h3) p hsit.mem_sigmaA P hsit.isCoreMaxLocal H U
      hopt.ext.pair.isTwoLocal (hUQ.trans hQH) hUM hUp
      (not_isCyclic_of_two_le_pRank hp (by omega)) hcore
  exact hopt.ext.pair.not_le hHM

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
