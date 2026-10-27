module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamiliesAux
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentTrichotomy

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G]

@[expose] def d1LiftX (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Subgroup G :=
  ((R.subgroupOf H) ⊓ K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype

omit [Finite G] in
theorem d1LiftX_le (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : d1LiftX p H R K ≤ R := by
  rintro _ ⟨x, ⟨hxR, -⟩, rfl⟩
  exact hxR

omit [Finite G] in
theorem d1LiftX_le_H (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : d1LiftX p H R K ≤ H :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem d1LiftX_subgroupOf (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
    (d1LiftX p H R K).subgroupOf H =
      R.subgroupOf H ⊓ K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

omit [Finite G] in
theorem map_d1LiftX (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
    ((d1LiftX p H R K).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K := by
  rw [d1LiftX_subgroupOf]
  ext y
  constructor
  · rintro ⟨x, ⟨hxR, hxK⟩, rfl⟩
    exact ⟨⟨x, hxR, rfl⟩, hxK⟩
  · rintro ⟨⟨x, hxR, rfl⟩, hyK⟩
    exact ⟨x, ⟨hxR, hyK⟩, rfl⟩

structure D1L2Config (p : ℕ) [Fact p.Prime] (n : ℕ) (P : Sylow p G) (M H R X : Subgroup G) :
    Prop where
  ext : D1Extremal p P M H R
  glob : CFSG.AGLEmbeddingD2.AGLGlobal G
  three_le : 3 ≤ n
  le_R : X ≤ R
  socle : ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), K.Normal ∧
    Nonempty (K ≃* PSL2GF p n) ∧
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ ∧
    (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K
  normal_sup : ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal

end Config

theorem three_le_of_pow_three_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (h : p ^ 3 ∣ p ^ n * n) : 3 ≤ n := by
  by_contra hlt
  have hp1 := hp.two_le
  interval_cases n
  · have h' := Nat.le_of_dvd (by positivity) h
    have h'' := Nat.pow_lt_pow_right hp.one_lt (show 1 < 3 by norm_num)
    simp only [pow_one, mul_one] at h' h''
    linarith
  · have h2 : p ∣ 2 := by
      rw [show p ^ 3 = p ^ 2 * p by ring] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h
    exact hp2 (le_antisymm (Nat.le_of_dvd two_pos h2) hp1)

namespace ReducedNongeneration

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {X₀ : Subgroup (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem nonempty_mulEquiv_psl2GF_and_centralizer_eq_bot
    (hred : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar X₀)
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    {n : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nonempty (K ≃* PSL2GF p n) ∧
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ := by
  obtain ⟨e₁⟩ := e
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hn : n ≠ 0 := by
    obtain ⟨q, -, -, rfl⟩ := hd
    exact q.exponent_pos.ne'
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_center_quotient_psl2 hred.ne_two hn (card_ne_nine_of_isLinTwoIndex hd)
      hK.2.2 (isPGroup_center_of_isComponentOf hred.prime hred.core_eq_bot hK) (e₁.trans e₂)
  exact ⟨⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    (e₁.trans e₂)⟩, centralizer_eq_bot_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot hKn
      (fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rbar hKn
        (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp) hZ⟩

end ReducedNongeneration

section Extremal

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1Extremal.d1L2Config (hext : D1Extremal p P M H R)
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G)
    (hred : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))))
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    {n : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hR1a : ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal) :
    D1L2Config p n P M H R (d1LiftX p H R K) := by
  have hp : p.Prime := Fact.out
  have hn : 1 ≤ n := by
    obtain ⟨q, -, -, rfl⟩ := hd
    exact q.exponent_pos
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  obtain ⟨hKe, hC⟩ := hred.nonempty_mulEquiv_psl2GF_and_centralizer_eq_bot hK huniq hcent hd e
  have hdvd : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ∣ p ^ n * n :=
    card_dvd_of_isPGroup_of_psl2GF kFactL2AutPCard hred.ne_two hn hKn hKe hC _
      Rbar.isPGroup'
  obtain ⟨E, hER, -, hEcard⟩ := SectionRank.exists_pRank hp.one_lt
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))
  have h3 : p ^ 3 ∣ p ^ n * n :=
    ((pow_dvd_pow p hred.three_le_pRank).trans
      (hEcard ▸ Subgroup.card_dvd_of_le hER)).trans hdvd
  exact ⟨hext, hglob, three_le_of_pow_three_dvd hp hred.ne_two hn h3,
    d1LiftX_le p H R K, ⟨K, hKn, hKe, hC, map_d1LiftX p H R K⟩, hR1a⟩

end Extremal

namespace D1ComponentConfig

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

omit [Fact p.Prime] in
theorem map_d1LiftX_eq_inf (hcfg : D1ComponentConfig p P M H R Rbar) :
    ((d1LiftX p H R K).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
  rw [map_d1LiftX, hcfg.rbar]

theorem nonempty_mulEquiv_psl2GF_and_centralizer_eq_bot
    (hcfg : D1ComponentConfig p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    {n : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nonempty (K ≃* PSL2GF p n) ∧
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ :=
  hcfg.red.nonempty_mulEquiv_psl2GF_and_centralizer_eq_bot hK huniq hcent hd e

theorem d1L2Config (hcfg : D1ComponentConfig p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    {n : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hR1a : ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal) :
    D1L2Config p n P M H R (d1LiftX p H R K) :=
  hcfg.ext.d1L2Config hcfg.glob.toAGLGlobal hcfg.red hK huniq hcent hd e hR1a

end D1ComponentConfig

theorem stmtL2ConfigOfComponent :
    ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
      {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}, D1ComponentConfig p P M H R Rbar →
      ∀ {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}, IsComponentOf K ⊤ →
        (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
        (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
            Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
          orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
        ∀ {n : ℕ} {d : TauCeti.ValidLieTypeIndex}, IsLinTwoIndex p n d →
          Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
          ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal →
          D1L2Config p n P M H R (d1LiftX p H R K) := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hcent n d hd e hR1a
  exact hcfg.d1L2Config hK huniq hcent hd e hR1a

end CFSG.AGLEmbedding
