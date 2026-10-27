module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Steps
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem normalizer_zpowers_le_of_centralizer_rank' (hFC : FullCoreLocality G) {f : ℕ}
    {F₀ : Sylow f G} (hloc : D1Local f F₀ M) {u : G} (hCM : centralizer ({u} : Set G) ≤ M)
    (hC2 : 2 ≤ Open.pRank f (centralizer ({u} : Set G))) :
    normalizer ((zpowers u : Subgroup G) : Set G) ≤ M := by
  have hprime := hloc.beta.1
  haveI : Fact f.Prime := ⟨hprime⟩
  set C : Subgroup G := centralizer ({u} : Set G) with hC
  obtain ⟨S, hSyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf f C
  have hSM : S ≤ M := hSyl.le.trans hCM
  have hS2 : 2 ≤ Open.pRank f S := by
    rw [pRank_eq_of_isSylowOf hprime hSyl]
    exact hC2
  have hNS : normalizer (S : Set G) ≤ M :=
    normalizer_le_of_two_le_pRank hFC hloc hSyl.isPGroup hSM hS2
  have hCeq : centralizer ((zpowers u : Subgroup G) : Set G) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hnC : normalizer ((zpowers u : Subgroup G) : Set G) ≤ normalizer (C : Set G) := by
    have := normalizer_le_normalizer_centralizer (zpowers u : Subgroup G)
    rwa [hCeq] at this
  exact (le_sup_normalizer_of_isSylowOf hnC hSyl).trans (sup_le hCM hNS)

theorem normalizer_zpowers_le_of_centralizer_rank (hS : Situation G p P M) {u : G}
    (hCM : centralizer ({u} : Set G) ≤ M)
    (hC2 : 2 ≤ Open.pRank p (centralizer ({u} : Set G))) :
    normalizer ((zpowers u : Subgroup G) : Set G) ≤ M :=
  normalizer_zpowers_le_of_centralizer_rank' hS.toGlobal.fullCore hS.loc hCM hC2

@[expose] def StepOmegaU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → ∀ H S : Subgroup G, Optimal p M x z H S →
      GLBPrimeCore p H ≤ M → ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q →
        zpowers x ⊔ zpowers z ≤ Q → (∃ q ∈ Q, q ^ p = 1 ∧ q ∉ zpowers x ⊔ zpowers z) →
          ∃ U : Subgroup G, U ≤ Q ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧
            ∀ u ∈ U, u ≠ 1 → 3 ≤ Open.pRank p (M ⊓ centralizer ({u} : Set G))

theorem omega_le_of_stepOmegaU (hU : StepOmegaU) {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M : Subgroup G} {x z : G} (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) {H S : Subgroup G} (hopt : Optimal p M x z H S)
    (hO : GLBPrimeCore p H ≤ M) {Q : Subgroup G} (hQH : Q ≤ H) (hQp : IsPGroup p Q)
    (hBQ : zpowers x ⊔ zpowers z ≤ Q) {q : G} (hqQ : q ∈ Q) (hq1 : q ^ p = 1) :
    q ∈ zpowers x ⊔ zpowers z := by
  by_contra hqB
  obtain ⟨U, hUQ, hUe, hUc, hUr⟩ := hU G p P M x z hS hx hz H S hopt hO Q hQH hQp hBQ
    ⟨q, hqQ, hq1, hqB⟩
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hQM : Q ≤ M := hopt.sylow_le Q hQp hQH hBQ
  have hUM : U ≤ M := hUQ.trans hQM
  have hUp : IsPGroup p U := elementary_isPGroup p U hUe
  have hUrank : Open.pRank p U = 2 := pRank_eq_of_isElemAbelian hprime hUe hUc
  have hcore : GLBCore p 1 U ≤ M := by
    rw [CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff]
    intro S' hS'U hrank
    by_cases h2 : 2 ≤ Open.pRank p S'
    · exact hS.normalizer_le (hUp.to_le hS'U) (hS'U.trans hUM) h2
    ·
      have hrk : Open.pRank p S' = 1 := by omega
      have hS'e : IsElemAbelian p S' := isElemAbelian_mono hUe hS'U
      obtain ⟨k, hk⟩ := (hUp.to_le hS'U).exists_card_eq
      have hk1 : k = 1 := by
        have := pRank_eq_of_isElemAbelian hprime hS'e hk
        omega
      subst hk1
      have hne : S' ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hk
        have := hprime.one_lt
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
      have hCM : centralizer ({(g : G)} : Set G) ≤ M :=
        hS.centralizer_le_of_pRank hgM hgo h3
      have hC2 : 2 ≤ Open.pRank p (centralizer ({(g : G)} : Set G)) :=
        le_trans (by omega) (le_trans h3
          (CFSG.SectionRank.pRank_mono hprime.one_lt (inf_le_right :
            M ⊓ centralizer ({(g : G)} : Set G) ≤ centralizer ({(g : G)} : Set G))))
      exact normalizer_zpowers_le_of_centralizer_rank hS hCM hC2
  have hHM : H ≤ M :=
    hS.toGlobal.d2 p hS.loc.beta P M hS.loc.maxLocal (hS.toGlobal.fullCore p P M hS.loc) U hUp
      hUrank hcore H hopt.ext.pair.isTwoLocal (hUQ.trans hQH)
  exact hopt.ext.pair.not_le hHM

theorem Optimal.core_lt {H S : Subgroup G} (hopt : Optimal p M x z H S) : pCoreOf 2 H < S := by
  refine lt_of_le_of_ne hopt.core_le fun h => ?_
  have hS1 : S ≠ ⊥ := hopt.ext.pair.ne_bot
  have hchar : (S.subgroupOf S).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hN := hopt.char_le S le_rfl hS1 hchar
  have hH : H ≤ M :=
    calc H = normalizer (pCoreOf 2 H : Set G) := hopt.eq_normalizer
      _ = normalizer (S : Set G) := by rw [h]
      _ ≤ M := hN
  exact hopt.ext.pair.not_le hH

theorem isPGroup_two_glbPrimeCore (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) {H S : Subgroup G} (hopt : Optimal p M x z H S)
    (hO : GLBPrimeCore p H ≤ M)
    (h65 : ∀ F : Subgroup G, F ≠ ⊥ → F ≤ GLBPrimeCore p H → Odd (Nat.card F) →
      zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M) :
    IsPGroup 2 (GLBPrimeCore p H) := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  obtain ⟨f, hf, hfdvd, hf2⟩ : ∃ f : ℕ, f.Prime ∧ f ∣ Nat.card (GLBPrimeCore p H) ∧ f ≠ 2 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    rw [IsPGroup.iff_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdn => hcon d hd hdn)⟩
  haveI : Fact f.Prime := ⟨hf⟩
  have hpl := plane_of_central hS hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hHO : H ≤ normalizer (GLBPrimeCore p H : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p H
  have hOp : ¬ p ∣ Nat.card (GLBPrimeCore p H) :=
    (Nat.Prime.coprime_iff_not_dvd hprime).mp (CFSG.AGLEmbedding.glbPrimeCore_coprime p H)
  have hbotf : IsPGroup f (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hBbot : zpowers x ⊔ zpowers z ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨F, hFsyl, -, hBF⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hprime hf
    hB3 hOp (hBH.trans hHO) bot_le hbotf hBbot
  have hF1 : F ≠ ⊥ := by
    obtain ⟨P2, hP2⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hFsyl
    intro hF
    have h1 := P2.not_dvd_index
    have hP2bot : (P2 : Subgroup ↥(GLBPrimeCore p H)) = ⊥ := by
      rw [hF] at hP2
      exact (Subgroup.map_eq_bot_iff_of_injective _ (GLBPrimeCore p H).subtype_injective).mp hP2
    rw [hP2bot, Subgroup.index_bot] at h1
    exact h1 hfdvd
  have hodd : Odd (Nat.card F) := by
    obtain ⟨k, hk⟩ := hFsyl.2.1.exists_card_eq
    rw [hk]
    exact Odd.pow (hf.odd_of_ne_two hf2)
  have hN := h65 F hF1 hFsyl.1 hodd hBF
  exact hopt.ext.pair.not_le (p65_le_of_normalizer_le hprime hf hOp hHO hO hFsyl hN)

@[expose] def StepP65Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z →
      ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) →
        ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M → Nat.Coprime p (Nat.card F) → Odd (Nat.card F) →
          zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

@[expose] def StepNotDeltaOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → ∀ H S : Subgroup G, Optimal p M x z H S →
      GLBPrimeCore p H ≤ M →
      (∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
        ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) →
        ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G))

@[expose] def StepKGroupCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → ∀ H S : Subgroup G, Optimal p M x z H S →
      GLBPrimeCore p H ≤ M →
      (∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
        ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) →
      ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) →
      IsPGroup 2 (GLBPrimeCore p H) → False

theorem stepKGroup_of_parts (hΩ : StepOmegaU) (h65 : StepP65Odd) (hδ : StepNotDeltaOmega)
    (hC : StepKGroupCore) : StepKGroup := by
  intro G _ _ p P M x z hS hx hz H S hopt hO
  have hΩ' : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
      ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z :=
    fun Q hQH hQp hBQ q hqQ hq1 => omega_le_of_stepOmegaU hΩ hS hx hz hopt hO hQH hQp hBQ hqQ hq1
  have hnpc := hδ G p P M x z hS hx hz H S hopt hO hΩ'
  have h2 : IsPGroup 2 (GLBPrimeCore p H) := by
    refine isPGroup_two_glbPrimeCore hS hx hz hopt hO fun F hF1 hFO hFo hBF => ?_
    refine h65 G p P M x z hS hx hz hnpc F hF1 (hFO.trans hO) ?_ hFo hBF
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hFO)
      (CFSG.AGLEmbedding.glbPrimeCore_coprime p H)
  exact hC G p P M x z hS hx hz H S hopt hO hΩ' hnpc h2

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
