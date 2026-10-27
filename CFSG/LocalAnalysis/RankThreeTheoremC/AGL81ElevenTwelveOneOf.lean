module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveOneNormal
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81TwelveCaseNotLe : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (b : G) (L : Subgroup G),
    3 ∈ rankThreeSigmaA G → TwelveCase P M H Q K b L →
    ¬ ⁅jZero H L, Subgroup.zpowers b⁆ ≤ pCoreOf 2 (jZero H L) → False

variable (G) in
@[expose] def AGL81TwelveCaseLe : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (b : G) (L : Subgroup G),
    TwelveCase P M H Q K b L → ⁅jZero H L, Subgroup.zpowers b⁆ ≤ pCoreOf 2 (jZero H L) →
    ¬ ⁅Subgroup.zpowers b, L⁆ ≤ pCoreOf 2 L → False

variable (G) in
@[expose] def AGL81ElevenTwelveShapeNotLe : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (b : G) (L : Subgroup G),
    TwelveCase P M H Q K b L → ¬ ⁅jZero H L, Subgroup.zpowers b⁆ ≤ pCoreOf 2 (jZero H L) →
    ((∃ r, IsLieOver ↥(barM M L) (.A r) 2 1) ∨ (∃ r, IsLieOver ↥(barM M L) (.D r) 2 1) ∨
        Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 8)) ∨
        IsLieOver ↥(barM M L) (.A 1) 7 1) ∧
      3 ≤ Open.pRank 3 L

variable (G) in
@[expose] def AGL81ElevenTwelveShapeLe : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (b : G) (L : Subgroup G),
    TwelveCase P M H Q K b L → ⁅jZero H L, Subgroup.zpowers b⁆ ≤ pCoreOf 2 (jZero H L) →
    ¬ ⁅Subgroup.zpowers b, L⁆ ≤ pCoreOf 2 L →
    (IsLieOver ↥(barM M L) (.D 4) 2 1 ∨ (∃ r, 4 ≤ r ∧ IsLieOver ↥(barM M L) (.twistedD r) 2 1) ∨
        ∃ r, 3 ≤ r ∧
          IsLieOver (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) (.twistedA r) 2 1) ∧
      ∃ t ∈ H ⊓ M, L.map (MulAut.conj t).toMonoidHom = L →
        IsLieOver ↥(barM M L) (.D 4) 2 1 ∨
          ∃ r, 5 ≤ r ∧ IsLieOver ↥(barM M L) (.twistedD r) 2 1

@[expose] def KFactTwelveRanksNotLe : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (∀ r, IsLieOver Y (.D r) 2 1 → Open.pRank 3 (⊤ : Subgroup Y) ≠ 3) ∧
    (Nonempty (Y ≃* alternatingGroup (Fin 8)) ∨ IsLieOver Y (.A 1) 7 1 →
      Open.pRank 3 (⊤ : Subgroup Y) ≤ 2)

@[expose] def KFactTwelveRanksLe : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    ((IsLieOver Y (.D 4) 2 1 ∨ (∃ r, 4 ≤ r ∧ IsLieOver Y (.twistedD r) 2 1) ∨
        ∃ r, 3 ≤ r ∧ IsLieOver (Y ⧸ Subgroup.center Y) (.twistedA r) 2 1) →
      ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ E ⊓ Subgroup.center Y = ⊥) ∧
    ((IsLieOver Y (.D 4) 2 1 ∨ ∃ r, 5 ≤ r ∧ IsLieOver Y (.twistedD r) 2 1) →
      4 ≤ Open.pRank 3 (⊤ : Subgroup Y))

variable (G) in
@[expose] def KFactLnTwoCentralizer : Prop :=
  ∀ (M L : Subgroup G) (b : G) (r : ℕ), IsTwoPrimeComponent M L → 4 ≤ r →
    IsLieOver ↥(barM M L) (.A r) 2 1 → b ∈ M →
    Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G) → orderOf b = 3 →
    ¬ ⁅Subgroup.zpowers b, L⁆ ≤ pCoreOf 2 L →
    ∃ I : Subgroup G, IsTwoPrimeComponent (Subgroup.centralizer ({b} : Set G) ⊓ M) I ∧
      3 ∣ Nat.card I

theorem four_le_of_isLieOver_A {Y : Type} [Group Y] {r : ℕ} (h : IsLieOver Y (.A r) 2 1) :
    4 ≤ r := by
  obtain ⟨⟨d, hv⟩, ⟨q, hp, he, hd⟩, -⟩ := h
  have hc : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hp, he, pow_one]
  simp only at hd
  subst hd
  simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, hc, and_true] at hv
  omega

theorem pRank_top_barM_eq {M L : Subgroup G} (hLM : L ≤ M) :
    Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    CFSG.AGLEmbedding.pRank_barM_eq Nat.prime_three (by norm_num) M L hLM]

theorem four_le_pRank_of_ne_conj {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) {t : G}
    (ht : t ∈ M) (hne : L.map (MulAut.conj t).toMonoidHom ≠ L) {E : Subgroup ↥(barM M L)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hZ : E ⊓ Subgroup.center ↥(barM M L) = ⊥) : 4 ≤ Open.pRank 3 M := by
  set L' := L.map (MulAut.conj t).toMonoidHom with hL'def
  have hL' : IsTwoPrimeComponent M L' := hL.map_conj ht
  set c := MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, ht⟩) with hc
  have hbar : barM M L ≠ barM M L' := fun he => hne (hL.eq_of_barM_eq hL' he).symm
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.component
    hL'.component hbar
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  have hL'bar : barM M L' = (barM M L).map c.toMonoidHom := barM_map_conj ht L
  set A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := E.map (barM M L).subtype with hA
  set B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := A.map c.toMonoidHom with hB
  have hAL : A ≤ barM M L := Subgroup.map_subtype_le E
  have hBL' : B ≤ barM M L' := by
    rw [hL'bar]
    exact Subgroup.map_mono hAL
  have hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hcomm (hAL hx)) y (hBL' hy)).symm
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxB⟩
    obtain ⟨e, he, rfl⟩ := hxA
    have hcen : e ∈ Subgroup.center ↥(barM M L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h := Subgroup.mem_centralizer_iff.mp (hcomm g.2) _ (hBL' hxB)
      simpa using h.symm
    have he1 : e ∈ E ⊓ Subgroup.center ↥(barM M L) := ⟨he, hcen⟩
    rw [hZ, Subgroup.mem_bot] at he1
    rw [he1, map_one]
    exact Subgroup.one_mem _
  have hcop : Nat.Coprime 3 (Nat.card (A ⊓ B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))) := by
    rw [hinf, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have h1 := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime Nat.prime_three hAB hcop
  have hEA : IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hE _
  have hcA : Nat.card A = 3 ^ 2 := by
    rw [hA, Subgroup.card_map_of_injective (barM M L).subtype_injective, hcard]
  have hEB : IsElemAbelian 3 B := CFSG.SectionRank.isElemAbelian_map hEA _
  have hcB : Nat.card B = 3 ^ 2 := by
    rw [hB, Subgroup.card_map_of_injective (fun a b h => c.injective h), hcA]
  have h2A : 2 ≤ Open.pRank 3 A := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hEA hcA
  have h2B : 2 ≤ Open.pRank 3 B := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hEB hcB
  have hsup : A ⊔ B ≤ barM M M := by
    intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) x
    exact ⟨y, y.2, rfl⟩
  have h3 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hsup
  rw [CFSG.AGLEmbedding.pRank_barM_eq Nat.prime_three (by norm_num) M M le_rfl] at h3
  omega

theorem twelve_ranks (hS : Setting G) {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hd : AGL81CfgData 3 P M H Q K)
    {L : Subgroup G} (hL : L ≤ M) : Open.pRank 3 L ≤ Open.pRank 3 M ∧ Open.pRank 3 M ≤ 3 := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have h1 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) M hesc.maxTwoLocal_M.1
  rw [hS.rank] at h1
  exact ⟨CFSG.SectionRank.pRank_mono (by norm_num) hL, h1⟩

theorem agl81TwelveCaseNotLe_of (hsh : AGL81ElevenTwelveShapeNotLe G)
    (hK : KFactTwelveRanksNotLe) (hLn : KFactLnTwoCentralizer G)
    (h42 : AGL81TenFourteenThreeAt G) (hn : AGL81TwelveNormalizes G)
    (h431 : AGL81TenFourteenTwoThree G) : AGL81TwelveCaseNotLe G := by
  intro hS P M H Q K b L h3σ hc hJ
  have hc' : TwelveCase P M H Q K b L := hc
  obtain ⟨hshape, h3L⟩ := hsh hS P M H Q K b L hc hJ
  obtain ⟨hd, -, -, -, ⟨hbHM, -, hob, hCb, hQb⟩, hL, -⟩ := hc
  obtain ⟨hLM, hM3⟩ := twelve_ranks hS hd hL.le
  have hbar := pRank_top_barM_eq hL.le
  rcases hshape with ⟨r, hr⟩ | ⟨r, hr⟩ | hsmall
  · obtain ⟨I, hI, h3⟩ := hLn M L b r hL.toIsTwoPrimeComponent (four_le_of_isLieOver_A hr) hr
      hbHM.2 (hn hS P M H Q K b L hc') hob (h42 hS P M H Q K b L hc')
    obtain ⟨H₁, R₁, hesc⟩ := hd.escape
    exact h431 hS P M H₁ R₁ hesc b hbHM.2 hob hCb ⟨Q, hQb, hd.base⟩ I hI h3
  · exact (hK ↥(barM M L)).1 r hr (by omega)
  · have := (hK ↥(barM M L)).2 hsmall
    omega

theorem agl81TwelveCaseLe_of (hsh : AGL81ElevenTwelveShapeLe G) (hK : KFactTwelveRanksLe) :
    AGL81TwelveCaseLe G := by
  intro hS P M H Q K b L hc hJ hBL
  obtain ⟨hshape, t, htHM, heq⟩ := hsh hS P M H Q K b L hc hJ hBL
  obtain ⟨hd, -, -, -, -, hL, -⟩ := hc
  obtain ⟨hLM, hM3⟩ := twelve_ranks hS hd hL.le
  by_cases ht : L.map (MulAut.conj t).toMonoidHom = L
  · have h4 := (hK ↥(barM M L)).2 (heq ht)
    rw [pRank_top_barM_eq hL.le] at h4
    omega
  · obtain ⟨E, hE, hcard, hZ⟩ := (hK ↥(barM M L)).1 hshape
    have := four_le_pRank_of_ne_conj hL.toIsTwoPrimeComponent htHM.2 ht hE hcard hZ
    omega

theorem agl81ElevenTwelveOne_of (h0 : AGL81TwelveSetup G) (h2 : AGL81TenFourteenThreeAt G)
    (h3 : AGL81TwelveCaseNotLe G) (h4 : AGL81TwelveCaseLe G) : AGL81ElevenTwelveOne G := by
  intro hS P M H Q K h3σ hd hA hnc L hL hI
  by_contra hlt
  push Not at hlt
  obtain ⟨b, hb⟩ := h0 hS P M H Q K hd hA (by omega)
  have hc : TwelveCase P M H Q K b L := ⟨hd, hA, hnc, by omega, hb, hL, hI⟩
  have hBL := h2 hS P M H Q K b L hc
  by_cases hJ : ⁅jZero H L, Subgroup.zpowers b⁆ ≤ pCoreOf 2 (jZero H L)
  · exact h4 hS P M H Q K b L hc hJ hBL
  · exact h3 hS P M H Q K b L h3σ hc hJ

theorem agl81ElevenTwelveOne_of_cited (h9 : AGL81NineCompetitorQ G)
    (h1014 : AGL81TenFourteenThreeCfg G) (h1031 : AGL81TenThreeOneAt G)
    (h2255 : AGL81TenThreeOTwoZ G) (h431 : AGL81TenFourteenTwoThree G)
    (hsN : AGL81ElevenTwelveShapeNotLe G) (hsL : AGL81ElevenTwelveShapeLe G)
    (hKN : KFactTwelveRanksNotLe) (hKL : KFactTwelveRanksLe) (hLn : KFactLnTwoCentralizer G) :
    AGL81ElevenTwelveOne G :=
  have h42 := agl81TenFourteenThreeAt_of h1014 h1031
  agl81ElevenTwelveOne_of (agl81TwelveSetup_of h9) h42
    (agl81TwelveCaseNotLe_of hsN hKN hLn h42 (agl81TwelveNormalizes_of h1031 h2255) h431)
    (agl81TwelveCaseLe_of hsL hKL)

end CFSG.LocalAnalysis.RankThreeTheoremC
