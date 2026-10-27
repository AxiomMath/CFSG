module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Shape
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma44

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G} {x : G}

theorem not_two_dvd_card_inf_primeCore_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G)
    (hloc : D1Local p P M) (hType : PTypeHyp p P M)
    (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) :
    ¬ 2 ∣ Nat.card (GLBPrimeCore p M ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨R, K, d, n, hf, hn, hd, -, -⟩ := exists_linTwo_p hp5 hK hG hloc hType h
  obtain ⟨eK⟩ := hf.equiv
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  set e : K ≃* PSL2GF p n := eK.trans eP with he
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Ob : Subgroup C := primeComplementCore (G := C) p with hOb
  set ρ : C →* RedCent p x := QuotientGroup.mk' Ob with hρ
  set N : Subgroup G := GLBPrimeCore p M with hNdef
  set Zc : Subgroup C := (N ⊓ C).subgroupOf C with hZc
  set W : Subgroup (RedCent p x) := Zc.map ρ with hW
  have hNM : N ≤ M := glbPrimeCore_le p M
  have hMN : M ≤ normalizer (N : Set G) := le_normalizer_glbPrimeCore p M
  have hred := hf.red
  have hWX₀ : W ≤ redCentM p M x :=
    Subgroup.map_mono fun c hc => mem_subgroupOf.mpr ⟨c.2, hNM (mem_subgroupOf.mp hc).1⟩
  have hX₀W : redCentM p M x ≤ normalizer (W : Set (RedCent p x)) := by
    rintro _ ⟨c, hc, rfl⟩
    have hcM : (c : G) ∈ M := (mem_subgroupOf.mp hc).2
    have hcZ : c ∈ normalizer (Zc : Set C) := by
      rw [mem_normalizer_iff]
      intro z
      have hz := mem_normalizer_iff.mp (hMN hcM) (z : G)
      constructor
      · intro hzZ
        exact mem_subgroupOf.mpr ⟨hz.mp (mem_subgroupOf.mp hzZ).1, (c * z * c⁻¹).2⟩
      · intro hzZ
        exact mem_subgroupOf.mpr ⟨hz.mpr (mem_subgroupOf.mp hzZ).1, z.2⟩
    exact Subgroup.le_normalizer_map ρ ⟨c, hcZ, rfl⟩
  have hWcop : p.Coprime (Nat.card W) := by
    have h1 : Nat.card W ∣ Nat.card Zc := Subgroup.card_map_dvd Zc ρ
    have h2 : Nat.card Zc ∣ Nat.card N := by
      rw [hZc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ C ≤ C)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (glbPrimeCore_coprime p M).coprime_dvd_right (h1.trans h2)
  have hn1 : 1 ≤ n := by omega
  have hKn : K.Normal := hred.normal
  obtain ⟨hTab, hTcard⟩ := isElemAbelian_sylow_inf_of_psl2GF hn1 e R
  have hrank : 3 ≤ Open.pRank p ((R : Subgroup (RedCent p x)) ⊓ K) :=
    hn.trans (le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp.out _)
      ⟨_, le_rfl, hTab, hTcard⟩)
  have hN : normalizer ((((R : Subgroup (RedCent p x)) ⊓ K : Subgroup (RedCent p x))) :
      Set (RedCent p x)) ≤ redCentM p M x :=
    (normalizer_le_glbCore p 2 inf_le_left (by omega)).trans hred.fullCore
  have hWbot : W = ⊥ := eq_bot_of_coprime_of_psl2GF hp2 hn hKn e hf.isPGroup R _ hN
    hred.not_le hWX₀ hX₀W hWcop
  have hZO : Zc ≤ Ob := by
    have := (Subgroup.map_eq_bot_iff (f := ρ) (H := Zc)).mp hWbot
    rwa [hρ, QuotientGroup.ker_mk'] at this
  have hNC : N ⊓ C ≤ GLBPrimeCore p C := fun g hg => by
    have := hZO (mem_subgroupOf.mpr hg : (⟨g, hg.2⟩ : C) ∈ Zc)
    have h3 : (⟨g, hg.2⟩ : C) ∈ (GLBPrimeCore p C).subgroupOf C := by
      rw [glbPrimeCore_subgroupOf]
      exact this
    exact mem_subgroupOf.mp h3
  intro h2
  exact h.not_two_dvd_card_primeCore hG.glob hG.d1 hloc (h2.trans (Subgroup.card_dvd_of_le hNC))

theorem eq_bot_of_two_group_inf_centralizer_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G)
    (hloc : D1Local p P M) (hType : PTypeHyp p P M)
    (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) {X : Subgroup G}
    (hX2 : IsPGroup 2 X) (hXO : X ≤ rankThreePrimeCore p M)
    (hXC : X ≤ centralizer ({x} : Set G)) : X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hX1
  have hodd := not_two_dvd_card_inf_primeCore_p hp5 hK hG hloc hType h
  obtain ⟨k, hk⟩ := hX2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hX1 (Subgroup.card_eq_one.mp (by simpa using hk))
  have hXle : X ≤ GLBPrimeCore p M ⊓ centralizer ({x} : Set G) := le_inf hXO hXC
  exact hodd ((dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hXle))

end CFSG.LocalAnalysis.RankFourTheoremC.P5
