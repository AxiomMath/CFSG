module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213SigmaWeak
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 Subgroup

@[expose] def KFactLemma213RedC (n : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K],
    CFSG.AGLEmbedding.CatalogSimpleSections K → primeComplementCore (G := K) p = ⊥ →
      (¬ ∃ Q : Subgroup K, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set K) ≤ Q) →
      CFSG.pCore p K = ⊥ →
      ∀ (P : Sylow p K) (z : K) (D : Subgroup K), Lemma212ConfigGe n p P z D →
        (∃ g, IsPlaneDiagonal p D z g) → CentralizerSectionEmbeds p D z →
        (∀ T : Subgroup K, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set K) →
            T ≤ centralizer ({z} : Set K)) ∨
          (∀ y ∈ D, y ≠ 1 → ∃ h ∈ normalizer (D : Set K),
            zpowers y = (zpowers z).map (MulAut.conj h).toMonoidHom)

@[expose] def GL83I294TwoFour : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    centralizer (L : Set X) = ⊥ → ∀ (D : Subgroup X), IsElemAbelian p D → Nat.card D = p ^ 2 →
    CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X)) →
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ z g : X, z ∈ D → z ≠ 1 →
      IsPlaneDiagonal p D z g →
      (∃ x ∈ D, x ≠ 1 ∧ CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) →
      (∀ T : Subgroup X, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set X) → T = ⊥) ∨
        LinesTransitive D

@[expose] def GL83I294Four : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    centralizer (L : Set X) = ⊥ → ∀ (D : Subgroup X), IsElemAbelian p D → Nat.card D = p ^ 2 →
    CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X)) →
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ z g : X, z ∈ D → z ≠ 1 →
      IsPlaneDiagonal p D z g →
      (∃ x ∈ D, x ≠ 1 ∧ CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) → False

theorem GL83I294TwoFour.of_two (h : GL83I294Two) : GL83I294TwoFour :=
  fun p hp h5 X _ _ L _ hs hn hc hcen D hD hDc hSyl hrank z g hz hz1 hg hlow =>
    h p hp h5 X L hs hn hc hcen D hD hDc hSyl (by omega) z g hz hz1 hg hlow

theorem GL83I294TwoFour.of_four (h : GL83I294Four) : GL83I294TwoFour :=
  fun p hp h5 X _ _ L _ hs hn hc hcen D hD hDc hSyl hrank z g hz hz1 hg hlow =>
    (h p hp h5 X L hs hn hc hcen D hD hDc hSyl hrank z g hz hz1 hg hlow).elim

theorem Lemma213.Red.caseA_four {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K}
    {D : Subgroup K} (hI : GL83I294TwoFour) (R : Red n p K P z D) (h5 : 5 ≤ p) (hn : 4 ≤ n)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections K) {g : K} (hg : IsPlaneDiagonal p D z g)
    (hlow : ∃ x ∈ D, x ≠ 1 ∧ CFSG.Open.pRank p (centralizer ({x} : Set K)) ≤ 2)
    (hD : ∀ w ∈ D, ∀ C : ComponentIndex K, w • C = C) :
    (∀ T : Subgroup K, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set K) → T = ⊥) ∨
      LinesTransitive D := by
  haveI := R.fact
  have hS := R.subsingleton_of_normalizes (by omega) hD
  obtain ⟨C₀⟩ := exists_comp R.core R.nc
  obtain ⟨hsimple, hnonab⟩ := R.isSimpleGroup_comp C₀
  haveI : C₀.1.Normal :=
    ⟨fun x hx g => by
      have h1 := mem_cjComp_of_mem g C₀ hx
      rwa [Subsingleton.elim (cjComp g C₀) C₀] at h1⟩
  have hcatL : IsCatalogGroup C₀.1 := hcat.simple_subgroup C₀.1 hsimple hnonab
  have hrank : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) :=
    hn.trans (R.conf.rank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p R.prime le_top))
  exact hI p R.prime h5 K C₀.1 hsimple hnonab hcatL (R.centralizer_eq_bot hS C₀) D R.conf.elem
    R.conf.card R.conf.sylow hrank z g R.conf.mem R.z_ne_one hg hlow

theorem kFactLemma213RedC_four_of_rank4 (hI : GL83I294TwoFour)
    (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) : KFactLemma213RedC 4 := by
  intro p hp hp2 K _ _ hcat hcore hnc hpc P z D hconf hg hemb
  obtain ⟨g, hg⟩ := hg
  have h5 : 5 ≤ p := hconf.five_le hp hp2 le_rfl
  let R : Red 4 p K P z D := ⟨hp, hcore, hnc, hpc, hconf⟩
  by_cases hrk : ∃ d ∈ D, d ∉ zpowers z ∧ 3 ≤ CFSG.Open.pRank p (centralizer ({d} : Set K))
  · obtain ⟨d, hd, hdz, h3⟩ := hrk
    exact Or.inr fun y hy hy1 =>
      hconf.exists_mem_normalizer_zpowers_eq_of_three_le_pRank hp hd hdz h3 y hy hy1
  push Not at hrk
  by_cases hD : ∀ w ∈ D, ∀ C : ComponentIndex K, w • C = C
  · obtain ⟨d, hd, hdz⟩ := hconf.exists_mem_notMem_zpowers hp
    have hlow : ∃ x ∈ D, x ≠ 1 ∧ CFSG.Open.pRank p (centralizer ({x} : Set K)) ≤ 2 :=
      ⟨d, hd, fun h1 => hdz (h1 ▸ one_mem _), by have := hrk d hd hdz; omega⟩
    rcases R.caseA_four hI h5 le_rfl hcat hg hlow hD with h1 | h2
    · exact Or.inl fun T hT hDT => (h1 T hT hDT) ▸ bot_le
    · exact Or.inr fun y hy hy1 => h2 z R.conf.mem R.z_ne_one y hy hy1
  · push Not at hD
    obtain ⟨w, hw, C₀, hmove⟩ := hD
    exact Or.inl (R.caseB_central (R.outer_solvable hS hcat) hemb hw hmove)

theorem kFactLemma213RedC_four (hI : GL83I294Two)
    (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) : KFactLemma213RedC 4 :=
  kFactLemma213RedC_four_of_rank4 (GL83I294TwoFour.of_two hI) hS

@[expose] def KFactLemma213GeC (n : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (H : Type) [Group H] [Finite H],
    CFSG.AGLEmbedding.CatalogSimpleSections H → ¬ HasPrimeConstraint (G := H) p →
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ →
      ∀ (P : Sylow p H) (z : H) (D : Subgroup H), Lemma212ConfigGe n p P z D →
        (∃ g, IsPlaneDiagonal p D z g) → CentralizerEmbeds D z →
        (∀ T : Subgroup H, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set H) →
            T ≤ centralizer ({z} : Set H) ⊔ primeComplementCore (G := H) p) ∨
          (∀ y ∈ D, y ≠ 1 → ∃ h ∈ normalizer (D : Set H),
            zpowers y = (zpowers z).map (MulAut.conj h).toMonoidHom)

theorem KFactLemma213RedC.toGeC {n : ℕ} (h : KFactLemma213RedC n) : KFactLemma213GeC n := by
  intro p hp hp2 H _ _ hcat hcon hpc P z D hconf hg hemb
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hg
  have hN := primeComplementCore_coprime (G := H) p
  have hDp : IsPGroup p D := IsPGroup.of_card hconf.card
  rcases h p hp hp2 (H ⧸ primeComplementCore (G := H) p) (hcat.quotient _)
    (primeComplementCore_quotient_eq_bot p) hcon hpc _ _ _
    (hconf.map_mk _ hN) ⟨_, hg.map _⟩ (hemb.sectionEmbeds_map_mk _ hp hN hDp) with h1 | h2
  · refine Or.inl fun T hT hDT t ht => ?_
    have hbar := h1 (T.map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
      (hT.coprime_dvd_right (card_map_dvd T _)) fun x hx => by
        obtain ⟨d, hd, rfl⟩ := hx
        exact le_normalizer_map _ ⟨d, hDT hd, rfl⟩
    have hz : IsPGroup p (zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hconf.ord, pow_one])
    have htz := hbar (mem_map_of_mem (QuotientGroup.mk' (primeComplementCore (G := H) p)) ht)
    rw [centralizer_singleton_map_mk _ hp hN hz] at htz
    obtain ⟨c, hc, hct⟩ := htz
    have hnc : c⁻¹ * t ∈ primeComplementCore (G := H) p := QuotientGroup.eq.mp hct
    have h1' : c ∈ centralizer ({z} : Set H) ⊔ primeComplementCore (G := H) p :=
      Subgroup.mem_sup_left hc
    have h2' : c⁻¹ * t ∈ centralizer ({z} : Set H) ⊔ primeComplementCore (G := H) p :=
      Subgroup.mem_sup_right hnc
    have h3 := Subgroup.mul_mem _ h1' h2'
    rwa [mul_inv_cancel_left] at h3
  · exact Or.inr (exists_mem_normalizer_zpowers_eq_of_map_mk _ hp hN hDp hconf.mem h2)

end CFSG.LocalAnalysis.RankFourTheoremC
