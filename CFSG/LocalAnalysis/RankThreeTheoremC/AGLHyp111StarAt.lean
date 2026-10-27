module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def AGLCompetitorFactorAt (p : ℕ) (M H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (Q : Subgroup G) : Prop :=
  ∀ N : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → Q ≤ N → AGLCovers p H N K →
    ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y

@[expose] def AGLAbsorbsAt (p : ℕ) (M H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (Q : Subgroup G) : Prop :=
  ∀ N : Subgroup G, IsTwoLocal N → ¬ N ≤ M → Q ≤ N → AGLCovers p H N K → N ≤ H

theorem absorbsAt_of_factorAt {p : ℕ} {M H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hM : IsTwoLocal M)
    (hH : GLBIsMaxTwoLocal H) (hOH : pCoreOf 2 M ≤ pCoreOf 2 H) (hHM : pCoreOf 2 H ≤ M)
    (hOM : (primeComplementCore (G := H) p).map H.subtype ≤ M)
    (hHfac : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H, QuotientGroup.mk' _ k ∈ K ∧ x = m * k)
    {Q : Subgroup G} (hfac : AGLCompetitorFactorAt p M H K Q) :
    AGLAbsorbsAt p M H K Q := by
  intro N hN hNM hQN hcov
  obtain ⟨N', hNN', hN'⟩ := exists_maximal_twoLocal hN
  have hN'M : ¬ N' ≤ M := fun h => hNM (hNN'.trans h)
  have hcov' : AGLCovers p H N' K :=
    hcov.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNN' hx.2⟩)
  have h₁ : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ y ∈ H ⊓ N', x = m * y := by
    intro x hx
    obtain ⟨m, hm, k, hk, rfl⟩ := hHfac x hx
    obtain ⟨n, hn, hnk⟩ := hcov' hk
    have ho : n⁻¹ * k ∈ primeComplementCore (G := H) p := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' (primeComplementCore (G := H) p) (n⁻¹ * k) = 1
      rw [map_mul, map_inv, hnk, inv_mul_cancel]
    set o := n⁻¹ * k with hodef
    have hoM : (o : G) ∈ M := hOM ⟨o, ho, rfl⟩
    have hnoM : ((n * o * n⁻¹ : H) : G) ∈ M := by
      have : n * o * n⁻¹ ∈ primeComplementCore (G := H) p :=
        (primeComplementCore_normal p).conj_mem o ho n
      exact hOM ⟨_, this, rfl⟩
    refine ⟨m * ((n * o * n⁻¹ : H) : G), ⟨H.mul_mem hm.1 (n * o * n⁻¹).2, M.mul_mem hm.2 hnoM⟩,
      (n : G), Subgroup.mem_subgroupOf.mp hn, ?_⟩
    have hk : k = n * o := by rw [hodef]; group
    rw [hk]; push_cast; group
  exact le_of_le_of_eq hNN' (eq_of_factor hM hH hN' (subgroup_normalizes_pCoreOf 2 H) hHM hOH
    h₁ (hfac N' hN' hN'M (hQN.trans hNN') hcov')).symm

theorem star_of_absorbsAt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M H Q R : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hQ : IsAGLQ p M Q) (hQH : Q ≤ H)
    (hKX : ¬ K ≤ d1X0 p M H) (habs : AGLAbsorbsAt p M H K Q)
    (hb3 : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → Q ≤ Subgroup.normalizer (S : Set G) →
      S ≤ d1PlusCore p H K)
    (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K)) (hR1 : R ≠ ⊥) :
    CFSG.Quasithin.CGS R ≤ H ∧ CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo Q R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcov := cover_normalizer hp hp2 hQH hQ.2.1 hR
  obtain ⟨hRX, hR2, hQR, hRmax⟩ := hR
  have hN : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H := by
    intro C hCR hC1 hchar
    have hNRC : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) :=
      CFSG.Semidihedral.PrimeOrderCyclicConfinementLift.normalizer_le_of_characteristic_subgroupOf
        hCR hchar
    have hcovC : AGLCovers p H (Subgroup.normalizer (C : Set G)) K :=
      hcov.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNRC hx.2⟩)
    have hNM : ¬ Subgroup.normalizer (C : Set G) ≤ M := by
      intro hNM
      exact hKX (hcovC.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNM hx.2⟩))
    exact habs _ ⟨C, hC1, hR2.to_le hCR, rfl⟩ hNM (hQR.trans hNRC) hcovC
  have hCGS : CFSG.Quasithin.CGS R ≤ H :=
    iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hchar => hN C hCR hC1 hchar
  refine ⟨hCGS, hR2, hQR, fun S hS2 hQS hRS => ?_⟩
  have hNRH : Subgroup.normalizer (R : Set G) ≤ H := by
    refine hN R le_rfl hR1 ?_
    rw [Subgroup.subgroupOf_self]
    infer_instance
  set T := S ⊓ Subgroup.normalizer (R : Set G) with hT
  have hT2 : IsPGroup 2 T := hS2.to_le inf_le_left
  have hQT : Q ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf hQS (hQR.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hTX := hb3 T hT2 (inf_le_right.trans hNRH) hQT
  have hTR : T = R := hRmax T hTX hT2 hQT (le_inf hRS Subgroup.le_normalizer)
  by_contra hSR
  have hlt : R.subgroupOf S ≠ ⊤ := by
    intro htop
    exact hSR (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hRS)
  haveI : Group.IsNilpotent S := hS2.isNilpotent
  obtain ⟨x, hxN, hxR⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf S) (lt_top_iff_ne_top.mpr hlt))
  have hmapR : (R.subgroupOf S).map S.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRS]
  have hxN' : (x : G) ∈ Subgroup.normalizer (R : Set G) := by
    have := Subgroup.le_normalizer_map S.subtype ⟨x, hxN, rfl⟩
    rwa [hmapR] at this
  have hxT : (x : G) ∈ T := ⟨x.2, hxN'⟩
  rw [hTR] at hxT
  exact hxR hxT

theorem star_of_factorAt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M H Q R : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hM : IsTwoLocal M)
    (hH : GLBIsMaxTwoLocal H) (hKX : ¬ K ≤ d1X0 p M H)
    (hOH : pCoreOf 2 M ≤ pCoreOf 2 H) (hHM : pCoreOf 2 H ≤ M)
    (hOM : (primeComplementCore (G := H) p).map H.subtype ≤ M)
    (hHfac : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H, QuotientGroup.mk' _ k ∈ K ∧ x = m * k)
    (hQ : IsAGLQ p M Q) (hQH : Q ≤ H) (hfac : AGLCompetitorFactorAt p M H K Q)
    (hb3 : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → Q ≤ Subgroup.normalizer (S : Set G) →
      S ≤ d1PlusCore p H K)
    (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K)) (hR1 : R ≠ ⊥) :
    CFSG.Quasithin.CGS R ≤ H ∧ CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo Q R :=
  star_of_absorbsAt hp hp2 hQ hQH hKX (absorbsAt_of_factorAt hM hH hOH hHM hOM hHfac hfac) hb3 hR
    hR1

theorem isAGLQ_of_escape {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1Escape p P M H R) : IsAGLQ p M R :=
  ⟨h.le_M, h.isPGroup,
    Or.inl (by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact h.three_le_pRank)⟩

theorem extremal_of_competitor {p : ℕ} {P : Sylow p G} {M H R N : Subgroup G}
    (h : D1Extremal p P M H R) (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M) (hRN : R ≤ N) :
    D1Extremal p P M N R :=
  h.of_le hN hRN hNM

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
