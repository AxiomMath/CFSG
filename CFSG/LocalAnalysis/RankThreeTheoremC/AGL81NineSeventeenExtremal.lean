module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenAtConfig

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms
open Hyp111 CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem kappa_le_or_of_base_ext {P : Sylow p G} {M H R H₀ : Subgroup G}
    (hih : ∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
      d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) (hext : D1Extremal p P M H R) {B : Subgroup G}
    (hBR : B ≤ R) (hidx : Nat.card R = p * Nat.card B)
    (hNorm : ∀ U : Subgroup G, B ≤ U → U ≤ M → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ≤ M)
    (hR3 : Open.pRank p R ≤ 3) {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M)
    (hBN : B ≤ N) :
    ∃ T : Subgroup G, B ≤ T ∧ T ≤ N ∧ T ≤ M ∧ IsPGroup p T ∧
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) ∧
      (T = B ∨ Open.pRank p T ≤ 2 ∨
        ∃ P' : Sylow p G, D1Extremal p P' M N T ∧ d1Kappa p M N ≤ d1Kappa p M H) := by
  have : Fact p.Prime := ⟨hext.prime⟩
  have hB : IsPGroup p B := hext.isPGroup.to_le hBR
  obtain ⟨T, hBT, hTN, hTM, hT, hmax⟩ :=
    exists_maxPSubgroup_of_normalizer_le hB hBN (hBR.trans hext.le_M) hNorm
  refine ⟨T, hBT, hTN, hTM, hT, hmax, ?_⟩
  by_cases hTB : T = B
  · exact Or.inl hTB
  by_cases h2 : Open.pRank p T ≤ 2
  · exact Or.inr (Or.inl h2)
  push Not at h2
  obtain ⟨P', hP'⟩ := exists_d1Extremal_of_maxPSubgroup hext hN hNM hTN hTM hT hmax
    (card_le_of_ne_of_index hT hBT hTB hidx) h2 (hR3.trans h2)
  refine Or.inr (Or.inr ⟨P', hP', ?_⟩)
  by_contra hlt
  exact hih P' N T hP' (lt_of_le_of_lt hk (not_le.mp hlt))

@[expose] def Hyp917Ext (p : ℕ) (M H B : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∀ (P' : Sylow p G) (N T : Subgroup G), D1Extremal p P' M N T → B ≤ T → AGLCovers p H N K →
    d1Kappa p M N ≤ d1Kappa p M H → ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y

theorem Hyp917Ext.of_hyp917R {M H B : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h : Hyp917R p M H B K) :
    Hyp917Ext p M H B K := fun _ N _ hP' hBT hcov hNH =>
  (h N hP'.maxTwoLocal_H hP'.not_le (hBT.trans hP'.le_H) hcov).resolve_right (not_lt.mpr hNH)

theorem factorAt_base_of_ih_ext {P : Sylow p G} {M H R H₀ : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hih : ∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
      d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) (hext : D1Extremal p P M H R) {B : Subgroup G}
    (hBR : B ≤ R) (hidx : Nat.card R = p * Nat.card B)
    (hNorm : ∀ U : Subgroup G, B ≤ U → U ≤ M → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ≤ M)
    (hR3 : Open.pRank p R ≤ 3) (h917 : Hyp917Ext p M H B K)
    (hrank2 : AGLRankTwoFactorAt p M H B K) :
    AGLCompetitorFactorAt p M H K B := by
  intro N hN hNM hBN hcov
  obtain ⟨T, hBT, hTN, hTM, hT, hmax, hor⟩ :=
    kappa_le_or_of_base_ext hih hk hext hBR hidx hNorm hR3 hN hNM hBN
  rcases hor with h | h | ⟨P', hP', hNH⟩
  · exact hrank2 N T hN hNM hBN hcov hBT hTN hTM hT hmax (Or.inl h)
  · exact hrank2 N T hN hNM hBN hcov hBT hTN hTM hT hmax (Or.inr h)
  · exact h917 P' N T hP' hBT hcov hNH

theorem false_of_centralizing_base_of_ih_ext {P : Sylow p G} {M H R H₀ : Subgroup G}
    (h : D1PhaseThree p P M H R) (hext : D1Extremal p P M H R)
    (hih : ∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
      d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : NoXBlockFor G)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKX : ¬ K ≤ d1X0 p M H)
    (hOM : (primeComplementCore (G := H) p).map H.subtype ≤ M)
    (hHfac : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H,
      QuotientGroup.mk' (primeComplementCore (G := H) p) k ∈ K ∧ x = m * k)
    (hXM : d1PlusCore p H K ≤ M)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    {B : Subgroup G} (hBQ : IsAGLQ p M B) (hBR : B ≤ R) (hidx : Nat.card R = p * Nat.card B)
    (hR3 : Open.pRank p R ≤ 3) (h917 : Hyp917Ext p M H B K) (h2 : AGLRankTwoFactorAt p M H B K)
    (hb3 : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → B ≤ Subgroup.normalizer (S : Set G) →
      S ≤ d1PlusCore p H K)
    (hBL : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) : False := by
  have : Fact p.Prime := ⟨hext.prime⟩
  have hfacB : AGLCompetitorFactorAt p M H K B :=
    factorAt_base_of_ih_ext hih hk hext hBR hidx
      (fun U hBU hUM hU => normalizer_le_of_isAGLQ hext (isAGLQ_of_le hBQ hBU hUM hU)) hR3 h917 h2
  exact false_of_centralizing_base_of_factorAtB h hCGT hD2 hKX hOM hHfac hfacB hXM hL hLn
    hBQ.2.1 (hBR.trans hext.le_H) hBQ.1 hb3 hBL

theorem not_isCyclic_map_of_isPGroup [hp : Fact p.Prime] {N B : Subgroup G} (hBN : B ≤ N)
    (hB : IsPGroup p B) (hBnc : ¬ IsCyclic B) :
    ¬ IsCyclic ((B.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) := by
  intro hc
  apply hBnc
  have hSp : IsPGroup p (B.subgroupOf N) := hB.comap_subtype
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp.out
    (primeComplementCore (G := N) p)
    (hp.out.coprime_iff_not_dvd.mp (primeComplementCore_coprime p)) _ hSp
  let e := MulEquiv.ofBijective _ ⟨hinj, (QuotientGroup.mk' _).subgroupMap_surjective _⟩
  have : IsCyclic (B.subgroupOf N) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hBN).toMonoidHom
    (MulEquiv.surjective _)

theorem noPPrime_of_simple {K : Type} [Group K] [Finite K] (hKs : IsSimpleGroup K)
    (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1) :
    ∀ V : Subgroup K, V.Normal → p.Coprime (Nat.card V) → V = ⊥ := by
  intro V hV hcop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with h | h
  · exact h
  exfalso
  obtain ⟨x, hx1, k, hxk⟩ := hKp
  have hxV : x ∈ V := h ▸ Subgroup.mem_top x
  have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
  have h2 : orderOf x ∣ Nat.card V := by
    rw [← Subgroup.orderOf_mk x hxV]
    exact orderOf_dvd_natCard _
  have hc : (orderOf x).Coprime (p ^ k) :=
    Nat.Coprime.pow_right k (hcop.coprime_dvd_right h2).symm
  exact hx1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc h1))

theorem hyp917Ext_of_config (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hS : Setting G) (hpA : p ∈ rankThreeSigmaA G)
    (hind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q)
    {M H B : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hcon : ∀ (P' : Sylow p G) (N T : Subgroup G), D1Extremal p P' M N T → AGLCovers p H N K →
      ¬ HasPrimeConstraint (G := N) p)
    (hKs : IsSimpleGroup K) (hKnab : ∃ a b : K, a * b ≠ b * a)
    (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1) (hκ : d1Kappa p M H ≤ Nat.card K)
    {X : Subgroup G} (hXB : X ≤ B) (hXH : X ≤ H)
    (hXK : ∀ x (hx : x ∈ X), QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hXH hx⟩ ∈ K)
    (hXp : IsPGroup p X) (hXnc : ¬ IsCyclic X) :
    Hyp917Ext p M H B K := by
  intro P' N T hP' hBT hcov hNH
  have : Fact p.Prime := ⟨hP'.prime⟩
  have hXN : X ≤ N := (hXB.trans hBT).trans hP'.le_H
  by_cases hc : HasPrimeConstraint (G := N) p
  · exact (hcon P' N T hP' hcov hc).elim
  obtain ⟨Tbar, hcfg⟩ := exists_componentConfig3 hS hpA ⟨hP'.maxTwoLocal_M, hP'.weakCore_le⟩ hP'
    hc hind
  set πH := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set W : Subgroup G := (H ⊓ N) ⊓ (K.comap πH).map H.subtype with hWdef
  have hW : W ≤ H ⊓ N := inf_le_left
  have hWK : (W.subgroupOf H).map πH = K := by
    apply le_antisymm
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨-, ⟨h', hh', hhh'⟩⟩ := Subgroup.mem_subgroupOf.mp hh
      have : h' = h := Subtype.ext hhh'
      subst this
      exact hh'
    · intro k hk
      obtain ⟨h, hh, rfl⟩ := hcov hk
      have hhN : (h : G) ∈ H ⊓ N := Subgroup.mem_subgroupOf.mp hh
      exact ⟨h, Subgroup.mem_subgroupOf.mpr ⟨hhN, ⟨h, hk, rfl⟩⟩, rfl⟩
  have hXW : X ≤ W := fun x hx => ⟨⟨hXH hx, hXN hx⟩, ⟨⟨x, hXH hx⟩, hXK x hx, rfl⟩⟩
  obtain ⟨h93, W', hW', hW'K, hor⟩ := hcfg.hyp917At_of_cover h3 hother hSch hk hmod hKs hKnab hKp
    hW hWK hXW (hXB.trans hBT) (not_isCyclic_map_of_isPGroup hXN hXp hXnc)
  rcases hor with hle | hfac | hlt
  · exact factor_of_le_d1KBar h93 hW' hW'K (noPPrime_of_simple hKs hKp) hκ hle hNH
  · exact hfac
  · exact absurd hNH (not_le.mpr hlt)

theorem hyp917R_of_ext_self {P : Sylow p G} {M H R : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hext : D1Extremal p P M H R)
    (h : Hyp917Ext p M H R K) : Hyp917R p M H R K := by
  intro N hN hNM hRN hcov
  by_cases hlt : d1Kappa p M H < d1Kappa p M N
  · exact Or.inr hlt
  exact Or.inl (h P N R (extremal_of_competitor hext hN hNM hRN) le_rfl hcov (not_lt.mp hlt))

variable {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmall3Data.hyp917Ext (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hd : D1OneSmall3Data p P M H R Rbar K)
    (hcon : ∀ (P' : Sylow p G) (N T : Subgroup G), D1Extremal p P' M N T → AGLCovers p H N K →
      ¬ HasPrimeConstraint (G := N) p) {B : Subgroup G}
    (hXB : d1LiftX p H R K ≤ B) :
    Hyp917Ext p M H B K := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKs, hKnab⟩ := hd.toCore.isSimpleGroup
  have hXp : IsPGroup p (d1LiftX p H R K) := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hXK : ∀ x (hx : x ∈ d1LiftX p H R K),
      QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, d1LiftX_le_H p H R K hx⟩ ∈ K := by
    rintro _ ⟨y, ⟨-, hyK⟩, rfl⟩
    exact hyK
  have hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1 := by
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hd.toCore.d1LiftX_ne_bot
    obtain ⟨k, hk'⟩ := hXp x
    set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
    refine ⟨⟨π ⟨x, d1LiftX_le_H p H R K x.2⟩, hXK x x.2⟩, fun h1 => hx1 ?_, k, ?_⟩
    · have h1' : π ⟨x, d1LiftX_le_H p H R K x.2⟩ = π 1 := by
        rw [map_one]; exact congrArg Subtype.val h1
      have hxR : (⟨x, d1LiftX_le_H p H R K x.2⟩ : H) ∈ R.subgroupOf H :=
        d1LiftX_le p H R K x.2
      have := eq_of_mk_eq_of_isPGroup hp (primeComplementCore (G := H) p)
        (primeComplementCore_coprime p) hd.cfg.ext.isPGroup.comap_subtype hxR
        (R.subgroupOf H).one_mem h1'
      exact Subtype.ext (congrArg (fun y : H => (y : G)) this)
    · apply Subtype.ext
      have : ((x ^ p ^ k : d1LiftX p H R K) : G) = 1 := by rw [hk']; rfl
      show π ⟨x, _⟩ ^ p ^ k = 1
      rw [← map_pow]
      have h2 : (⟨x, d1LiftX_le_H p H R K x.2⟩ : H) ^ p ^ k = 1 :=
        Subtype.ext (by simpa using this)
      rw [h2, map_one]
  exact hyp917Ext_of_config h3 hother hSch hk hmod hd.cfg.glob hd.cfg.loc.sigma hd.cfg.ind hcon
    hKs hKnab hKp
    (Subgroup.card_le_of_le (iSup₂_le fun _ hL => le_of_not_le_compCore hd.toCore hL.1 hL.2)) hXB
    (d1LiftX_le_H p H R K) hXK hXp hd.toCore.not_isCyclic_d1LiftX

theorem D1OneSmall3Data.hyp917R (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hSch : KFactCatalogSchreier) (hk : KFactKlingenLocal)
    (hmod : StmtKlingenModel) (hd : D1OneSmall3Data p P M H R Rbar K)
    (hcon : ∀ (P' : Sylow p G) (N T : Subgroup G), D1Extremal p P' M N T → AGLCovers p H N K →
      ¬ HasPrimeConstraint (G := N) p) :
    Hyp917R p M H R K :=
  hyp917R_of_ext_self hd.cfg.ext (hd.hyp917Ext h3 hother hSch hk hmod hcon (d1LiftX_le p H R K))

end CFSG.LocalAnalysis.RankThreeTheoremC
