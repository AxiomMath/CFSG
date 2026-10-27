module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatEnd
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1SmallSPLZeroAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    IsSPLFamily p K → D1CzSP p z → D1CzOutside p z → d1MapPCore p M H = ⊥ → False

@[expose] def D1SmallSPLPair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    (IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K)) → D1CzSP p z → D1CzOutside p z →
    d1MapPCore p M H ⊓ K ≠ ⊥ →
    d1MapPCore p M H ⊓ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ →
    (p = 3 ∨ ¬ D1SmallIa p H K) →
    (∀ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1ReducedCentralizer p P' M z Pbar KC → R ≤ (P' : Subgroup G) → (P' : Subgroup G) ≤ M →
      Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = p ^ 6 ∧
      ((d1LiftX p H R K).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
        centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)) → False

@[expose] def KFactSPLNotFi22 : Prop := ∀ (K : Type) [Group K], IsSPLFamily 5 K → ¬ IsFi22 K

theorem card_of_isSmallLinTwo_five {K : Type} [Group K] (h : IsSmallLinTwo 5 K) :
    Finite K ∧ Nat.card K = 7800 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨d, hd, ⟨e₁⟩⟩ := h
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hk : Nat.card (GaloisField 5 2) = 5 ^ 2 := GaloisField.card 5 2 (by norm_num)
  refine ⟨Finite.of_equiv _ (e₁.trans e₂).symm.toEquiv, ?_⟩
  rw [Nat.card_congr (e₁.trans e₂).toEquiv]
  rw [CFSG.SectionRank.OddCover.card_psl_two (by norm_num) (by norm_num) hk]
  norm_num

theorem card_of_isSmallUnitary_five {K : Type} [Group K] (h : IsSmallUnitary 5 K) :
    Finite K ∧ Nat.card K = 126000 := by
  obtain ⟨d, ⟨q, hqp, hqe, hdq⟩, ⟨he⟩⟩ := h
  have hd : IsUnitaryIndex 5 d := ⟨q, hqp, hdq⟩
  obtain ⟨-, -, -, F, _, _, J, -, -, -, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd ⟨he⟩)
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨this, ?_⟩
  have hord := kFactUnitaryOrder K 5 d hd ⟨he⟩
  obtain ⟨q', hq'p, hq'd, hfe, -⟩ := hd.exists_eq
  have hq'e : q'.exponent = 1 := by
    have : q' = q := by
      have h1 : TauCeti.LieTypeIndex.twistedA 2 q' = TauCeti.LieTypeIndex.twistedA 2 q :=
        hq'd.symm.trans hdq
      injection h1
    rw [this, hqe]
  rw [hfe, hq'e] at hord
  norm_num at hord
  omega

theorem kFactSPLNotFi22_of (hFi6 : KFactFi22GuestRank) : KFactSPLNotFi22 := by
  intro K _ hspl hF
  have hfin : Finite K ∧ (Nat.card K = 7800 ∨ Nat.card K = 126000) := by
    rcases hspl with h | h | ⟨h, -⟩
    · obtain ⟨h1, h2⟩ := card_of_isSmallLinTwo_five h
      exact ⟨h1, Or.inl h2⟩
    · obtain ⟨h1, h2⟩ := card_of_isSmallUnitary_five h
      exact ⟨h1, Or.inr h2⟩
    · exact absurd h (by norm_num)
  obtain ⟨hfin, hcard⟩ := hfin
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨T⟩ : Nonempty (Sylow 5 K) := inferInstance
  obtain ⟨E, -, -, hE⟩ := hFi6 K hF T
  have hdvd : 3 ^ 4 ∣ Nat.card K := hE ▸ Subgroup.card_subgroup_dvd_card E
  rcases hcard with h | h <;> rw [h] at hdvd <;> norm_num at hdvd

theorem not_linThreeFour_of_spl (hSTO : KFactSmallThreeOrders) {K : Type} [Group K]
    (hspl : IsSPLFamily 3 K) : ¬ IsLinThreeFour K := by
  intro hL
  have h1 := (hSTO K).2.1 hL
  rcases hspl with h | h | ⟨-, ⟨e⟩⟩
  · rw [(hSTO K).2.2 h] at h1; norm_num at h1
  · rw [(hSTO K).1 h] at h1; norm_num at h1
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h1
    exact absurd h1 (by decide)

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.card_of_isSmallUnitary [Fact p.Prime] (hKU2 : KFactUnitarySylowStructure)
    (hd : D1OneSmallData p P M H R Rbar K) (hU : IsSmallUnitary p K) :
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) =
      p ^ 3 := by
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  obtain ⟨d, ⟨q, hqp, hqe, hdq⟩, ⟨e⟩⟩ := hU
  have hdU : IsUnitaryIndex p d := ⟨q, hqp, hdq⟩
  obtain ⟨q', -, hq'd, hfe, -⟩ := hdU.exists_eq
  have hq'e : q'.exponent = 1 := by
    have : q' = q := by
      have h1 : TauCeti.LieTypeIndex.twistedA 2 q' = TauCeti.LieTypeIndex.twistedA 2 q :=
        hq'd.symm.trans hdq
      injection h1
    rw [this, hqe]
  obtain ⟨hcard, -⟩ := hKU2 K p d hd.cfg.red.ne_two hdU ⟨e⟩ T₁
  rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, hcard, hfe, hq'e]

end Config

theorem d1SmallSPL_of_res (hFi : KFactSPLNotFi22) (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hExp : KFactSmallSylowExp) (hβ : KFactBeta)
    (hKO : KFactOneLie) (hTor : KFactOneLieTorus) (hSch : KFactCatalogSchreier)
    (hKU2 : KFactUnitarySylowStructure) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (h0 : D1SmallSPLZeroAll) (hpair : D1SmallSPLPair) : D1SmallSPL := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hspl hSP hout hOP
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hF : ¬ (p = 5 ∧ IsFi22 K) := by
    rintro ⟨rfl, hF⟩
    exact hFi K hspl hF
  have hL34 : ¬ (p = 3 ∧ IsLinThreeFour K) := by
    rintro ⟨rfl, hL⟩
    exact not_linThreeFour_of_spl hSTO hspl hL
  obtain ⟨h1, h2, h4⟩ := hOP hF
  by_cases hVK : d1MapPCore p M H ⊓ K = ⊥
  · exact h0 G p P M H R Rbar K hd huniq z hz hspl hSP hout (h1 hVK)
  have h3 := hd.toPhaseThree hUP hL34 hF
  obtain ⟨-, hVR, -, -, hiff⟩ := hd.d1MapPCore_facts h3 h84 hD2
  have hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ := hiff.mpr (by
    rwa [← inf_assoc, inf_eq_left.mpr hVR])
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set mk := QuotientGroup.mk' (primeComplementCore (G := C) p) with hmk
  have hOC := primeComplementCore_coprime (G := C) p
  have hRC' : R ≤ C := hd.le_centralizer_czElt hz
  have hN : ∀ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1ReducedCentralizer p P' M z Pbar KC → R ≤ (P' : Subgroup G) → (P' : Subgroup G) ≤ M →
      Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = p ^ 6 ∧
      ((d1LiftX p H R K).subgroupOf C).map mk =
        centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) := by
    intro P' Pbar KC hRC hRP' hP'M
    obtain ⟨TC, e, hTC, hTF, hXeq⟩ :=
      hd.map_d1LiftX_eq_center hExp hβ hKO hTor hSch h84 hD2 hz hout h3 hY hRC hRP' hP'M
    refine ⟨?_, hXeq⟩
    rw [← hTC, Subgroup.card_map_of_injective KC.subtype_injective]
    exact (hTF.pair rfl).1
  obtain ⟨P', Pbar, KC, -, hP'M, hRP', hRC⟩ := hd.exists_reducedCentralizer hz hSP
  obtain ⟨-, hXeq⟩ := hN P' Pbar KC hRC hRP' hP'M
  have hRCp : IsPGroup p (R.subgroupOf C) := hd.cfg.ext.isPGroup.comap_subtype
  have hXab : ∀ a ∈ d1LiftX p H R K, ∀ b ∈ d1LiftX p H R K, a * b = b * a := by
    intro a ha b hb
    have haC : a ∈ C := hRC' (d1LiftX_le p H R K ha)
    have hbC : b ∈ C := hRC' (d1LiftX_le p H R K hb)
    have hma : mk ⟨a, haC⟩ ∈ ((d1LiftX p H R K).subgroupOf C).map mk :=
      ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hmb : mk ⟨b, hbC⟩ ∈ ((d1LiftX p H R K).subgroupOf C).map mk :=
      ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    rw [hXeq] at hma hmb
    have hc : mk ⟨a, haC⟩ * mk ⟨b, hbC⟩ = mk ⟨b, hbC⟩ * mk ⟨a, haC⟩ :=
      Subgroup.mem_centralizer_iff.mp hmb.2 _ hma.1
    have haR : (⟨a, haC⟩ : C) ∈ R.subgroupOf C := d1LiftX_le p H R K ha
    have hbR : (⟨b, hbC⟩ : C) ∈ R.subgroupOf C := d1LiftX_le p H R K hb
    have h5 := eq_of_mk_eq_of_isPGroup hp _ hOC hRCp ((R.subgroupOf C).mul_mem haR hbR)
      ((R.subgroupOf C).mul_mem hbR haR) (by rw [map_mul, map_mul, hc])
    simpa using congrArg Subtype.val h5
  have hTab : ∀ a ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K,
      ∀ b ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K, a * b = b * a := by
    intro a ha b hb
    rw [← hd.cfg.map_d1LiftX_eq_inf] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have h5 : a' * b' = b' * a' := Subtype.ext (by
      simpa using hXab _ (Subgroup.mem_subgroupOf.mp ha') _ (Subgroup.mem_subgroupOf.mp hb'))
    rw [← map_mul, ← map_mul, h5]
  have hnZ : ¬ D1SmallPosZ p M H Rbar K := by
    rintro ⟨-, hne⟩
    apply hne
    refine le_antisymm inf_le_left fun a ha => ⟨ha, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => hTab b hb a ha
  have hXcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2 := by
    obtain ⟨TC, e, hTC, hTF, -⟩ :=
      hd.map_d1LiftX_eq_center hExp hβ hKO hTor hSch h84 hD2 hz hout h3 hY hRC hRP' hP'M
    have hXp : IsPGroup p ((d1LiftX p H R K).subgroupOf C) :=
      (hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)).comap_subtype
    rw [← (hd.d1LiftX_facts hz).2,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((d1LiftX_le p H R K).trans hRC')).toEquiv,
      ← card_map_mk_of_isPGroup hp _ hOC hXp, hXeq, ← hTC, ← map_subtype_centerOf,
      Subgroup.card_map_of_injective KC.subtype_injective]
    exact (card_center_of_torusFacts hTF).1
  have hLA : IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K) := by
    rcases hspl with h | h | h
    · exact Or.inl h
    · have h6 := hd.card_of_isSmallUnitary hKU2 h
      rw [hXcard] at h6
      exact absurd (Nat.pow_right_injective hp.two_le h6) (by norm_num)
    · exact Or.inr h
  by_cases hVC : d1MapPCore p M H ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥
  · have hIa : p = 3 ∨ ¬ D1SmallIa p H K := by
      by_contra hc
      push Not at hc
      obtain ⟨hp3, hIa⟩ := hc
      have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have hne := hd.cfg.red.ne_two
        have h4 : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by decide)
        omega
      have hLU : IsSmallLinTwo p K ∨ IsSmallUnitary p K := by
        rcases hLA with h | ⟨h, -⟩
        · exact Or.inl h
        · exact absurd h hp3
      exact hnZ (h4 hVK hVC hIa hp5 hLU)
    exact hpair G p P M H R Rbar K hd huniq z hz hLA hSP hout hVK hVC hIa hN
  · exact hnZ (h2 hVK hVC)

end CFSG.AGLEmbedding
