module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCasesN
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveOneOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LnTwoCentralizerLift
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Rank
import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

namespace TwelveLe

section General

variable {A : Type} [Group A] [Finite A]

theorem exists_commutator_not_mem_of_not_isSylow {Y P : Subgroup A} (hpar : IsParabolicTwo Y P)
    (hsyl : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 P) Y) :
    ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P := by
  by_contra hall
  push Not at hall
  obtain ⟨hPY, T, hT, hN⟩ := hpar
  have hTP : T ≤ P := fun t ht => hN ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  set O := CFSG.pCore 2 ↥P with hO
  set φ := QuotientGroup.mk' O with hφ
  have hcomm : ∀ u v : ↥P ⧸ O, u * v = v * u := by
    intro u v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O v
    obtain ⟨z, hz, hzv⟩ :=
      CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.1 (hall x x.2 y y.2)
    have hz' : z = x * y * x⁻¹ * y⁻¹ := Subtype.ext (by simpa using hzv)
    have h1 : φ (x * y * x⁻¹ * y⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr (hz' ▸ hz)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc φ x * φ y = (φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹) * (φ y * φ x) := by group
      _ = φ y * φ x := by rw [h1, one_mul]
  set T' : Subgroup ↥P := T.subgroupOf P with hT'
  have hT'p : IsPGroup 2 T' := hT.2.1.comap_subtype
  haveI hTn : (T'.map φ).Normal :=
    ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  have hNp : IsPGroup 2 ((T'.map φ).comap φ) :=
    (hT'p.map φ).comap_of_ker_isPGroup φ (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
  have hNO : (T'.map φ).comap φ ≤ O :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (Subgroup.Normal.comap hTn φ) hNp
  have hTO : T ≤ pCoreOf 2 P := fun t ht =>
    CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.2
      ⟨⟨t, hTP ht⟩, hNO (Subgroup.le_comap_map φ T' (Subgroup.mem_subgroupOf.mpr ht)), rfl⟩
  apply hsyl
  refine ⟨(Subgroup.map_subtype_le _).trans hPY, CFSG.pCore_isPGroup.map _, fun h2 => hT.2.2 ?_⟩
  exact h2.trans (Subgroup.index_dvd_of_le fun x hx => hTO hx)

theorem centralizes_of_wCent_self {Y : Subgroup A} (hqs : CFSG.Open.IsQuasisimple ↥Y)
    (hO : pCoreOf 2 Y = ⊥) {β : A} (hW : TenThreeThree.ParabComm.WCent Y β) :
    ∀ y ∈ Y, β * y = y * β := by
  have hO' : CFSG.pCore 2 ↥Y = ⊥ := by
    have h := hO
    unfold pCoreOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp h
  have e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot
  have hQ : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv.trans e) hqs
  have htop : (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) ≤
      TenThreeThree.wSup (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    unfold TenThreeThree.wSup
    exact le_iSup₂_of_le (f := fun T _ => T) (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y))
      ⟨.refl _, Or.inl ⟨le_rfl, .refl _, hQ⟩⟩ le_rfl
  intro y hy
  have h := hW y hy (htop (Subgroup.mem_top _))
  rw [hO, Subgroup.mem_bot] at h
  calc β * y = (β * y * β⁻¹ * y⁻¹) * (y * β) := by group
    _ = y * β := by rw [h, one_mul]

end General

variable {G : Type} [Group G] [Finite G]

theorem orderOf_mk'_eq_three {M : Subgroup G} {b : G} (hbM : b ∈ M) (hb : orderOf b = 3) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) = 3 := by
  have hd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) ∣ 3 :=
    (orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk, hb])
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exfalso
    rw [orderOf_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      ⟨_, (QuotientGroup.eq_one_iff _).mp h1⟩
    have hk' : b ^ 2 ^ k = 1 := by
      simpa using congrArg (fun x : ↥(CFSG.pCore 2 ↥M) => ((x : ↥M) : G)) hk
    have h3 := orderOf_dvd_of_pow_eq_one hk'
    rw [hb] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · exact h3

theorem centralizes_barM_of_commutator_mem {M L : Subgroup G} {b : G} (hbM : b ∈ M)
    (h : ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) :
    ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ := by
  intro y hy
  obtain ⟨l, hlM, hlL, rfl⟩ := LnTwoLift.mem_barM_iff.1 hy
  obtain ⟨z, hz, hzv⟩ := CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.1 (h l hlL)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hz' : z = (⟨b, hbM⟩ : ↥M) * ⟨l, hlM⟩ * (⟨b, hbM⟩ : ↥M)⁻¹ * (⟨l, hlM⟩ : ↥M)⁻¹ :=
    Subtype.ext (by simpa using hzv)
  have h1 : π z = 1 := (QuotientGroup.eq_one_iff _).mpr hz
  rw [hz', map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  set x := π ⟨b, hbM⟩
  set w := π ⟨l, hlM⟩
  calc x * w = (x * w * x⁻¹ * w⁻¹) * (w * x) := by group
    _ = w * x := by rw [h1, one_mul]

theorem agl81TwelveCaseLe_of_cartan (hC : AGL81TenThreeThreeCasesNCfg G)
    (hn : AGL81TwelveNormalizes G) (h431 : AGL81TenFourteenTwoThree G)
    (hKL : KFactTwelveRanksLe) (hKC : KFactTwelveLeCartan) (hKE : KFactTwelveLeE27) :
    AGL81TwelveCaseLe G := by
  intro hS P M H Q K b L hc hJ hBL
  have hbz := hn hS P M H Q K b L hc
  obtain ⟨hd, hA6, -, -, ⟨hbHM, hbX, hob, hCb, hQb⟩, hL, -⟩ := hc
  have hbn : b ∈ Subgroup.normalizer (L : Set G) := hbz (Subgroup.mem_zpowers b)
  have hLM : L ≤ M := hL.le
  have hbM : b ∈ M := hbHM.2
  have hbo : Odd (orderOf b) := by rw [hob]; decide
  have hbJ : ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L) := by
    intro x hx
    have h := (pCoreOf 2 (jZero H L)).inv_mem
      (hJ (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers b)))
    rwa [commutatorElement_inv, commutatorElement_def] at h
  obtain ⟨hLr, hMr⟩ := twelve_ranks hS hd hLM
  have hcen : (∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) → False := fun h =>
    hBL (LnTwoLift.commutator_zpowers_le_pCoreOf_of_le_centralizer hLM hbM hbz fun y hy =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact h y hy)
  rcases hC hS 3 P M H Q K hd L hL b hbHM hbn hbo hbJ with hcent | ⟨hcl, hpar, hsyl⟩
  · exact hcen (centralizes_barM_of_commutator_mem hbM hcent)
  obtain ⟨-, hβY, hβP, hW⟩ := TenThreeThree.bar_action_of_mem_normalizer hLM hbHM hbn hbo hbJ
  have hqs : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have hO : pCoreOf 2 (barM M L) = ⊥ :=
    TenThreeThree.pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent
  have hrk : Open.pRank 3 (barM M L) ≤ 3 := by
    rw [pRank_barM_eq Nat.prime_three (by norm_num) M L hLM]
    omega
  by_cases hPY : barM M (H ⊓ L) = barM M L
  · exact hcen (centralizes_of_wCent_self hqs hO (hPY ▸ hW))
  rcases hKC _ (barM M L) (barM M (H ⊓ L)) _ hqs hO hcl hpar hPY hsyl
      (exists_commutator_not_mem_of_not_isSylow hpar hsyl) (orderOf_mk'_eq_three hbM hob) hβY
      hβP hW hrk with h1 | ⟨D, hD, hD3⟩ | ⟨hshape, h9⟩
  · exact hcen h1
  ·
    obtain ⟨I, hI, h3⟩ := LnTwoLift.exists_twoPrimeComponent_of_isComponentOf
      hL.toIsTwoPrimeComponent hbM hbn hob hD hD3
    obtain ⟨H₁, R₁, hesc⟩ := hd.escape
    exact h431 hS P M H₁ R₁ hesc b hbM hob hCb ⟨Q, hQb, hd.base⟩ I hI h3
  obtain ⟨hAX, hAel, hA9⟩ := d1LiftX_facts_cfg hd hA6
  have hAQ : d1LiftX 3 H Q K ≤ Q := d1LiftX_le 3 H Q K
  have hAM : d1LiftX 3 H Q K ≤ M := hAQ.trans hd.base.1
  have hAH : d1LiftX 3 H Q K ≤ H := hAQ.trans hd.le_H
  have hbA : b ∉ d1LiftX 3 H Q K := fun h => by
    have h1 : b ∈ d1LiftX 3 H Q K ⊓ d1PlusCore 3 H K := ⟨h, hbX⟩
    rw [hAX, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hob
    exact absurd hob (by norm_num)
  have hcomm : ∀ e ∈ d1LiftX 3 H Q K, e * b = b * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQb (hAQ he))
  have hb3 : b ^ 3 = 1 := by rw [← hob]; exact pow_orderOf_eq_one b
  obtain ⟨hEel, hE27⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers Nat.prime_three
    (by rw [hA9]; norm_num) hAel.2 hb3 hbA hcomm
  set E := d1LiftX 3 H Q K ⊔ Subgroup.zpowers b with hE
  have hEM : E ≤ M := sup_le hAM (Subgroup.zpowers_le.mpr hbM)
  have hEH : E ≤ H := sup_le hAH (Subgroup.zpowers_le.mpr hbHM.1)
  have hshape' : IsLieOver ↥(barM M L) (.D 4) 2 1 ∨
      (∃ r, 4 ≤ r ∧ IsLieOver ↥(barM M L) (.twistedD r) 2 1) ∨
      ∃ r, 3 ≤ r ∧ IsLieOver (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) (.twistedA r) 2 1 := by
    rcases hshape with h | h
    · exact Or.inr (Or.inr ⟨3, le_rfl, h⟩)
    · exact Or.inr (Or.inl ⟨4, le_rfl, h⟩)
  obtain ⟨E9, hE9, hE9c, hE9Z⟩ := (hKL ↥(barM M L)).1 hshape'
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := fun e he => by
    by_contra hne
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hne
    have := four_le_pRank_of_ne_conj hL.toIsTwoPrimeComponent (hEM he) hne hE9 hE9c hE9Z
    omega
  have hEHL : E ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := fun e he => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hEH he)) x
    have h2 := Subgroup.mem_normalizer_iff.mp (hEL he) x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  have hEbY : barM M E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact LnTwoLift.mem_normalizer_barM x.2 (hEL (Subgroup.mem_subgroupOf.mp hx))
  have hEbP : barM M E ≤
      Subgroup.normalizer (barM M (H ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact LnTwoLift.mem_normalizer_barM x.2 (hEHL (Subgroup.mem_subgroupOf.mp hx))
  have hrkE : Open.pRank 3 (barM M L ⊔ barM M E) ≤ 3 := by
    have hle : barM M L ⊔ barM M E ≤ barM M M := by
      rw [LnTwoLift.barM_self_eq_top']
      exact le_top
    have h := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle
    rw [pRank_barM_eq Nat.prime_three (by norm_num) M M le_rfl] at h
    omega
  exact hKE _ (barM M L) (barM M (H ⊓ L)) (barM M E) hqs hO hshape hpar h9
    (CFSG.LocalAnalysis.RankThreeTheoremC.isElemAbelian_barM hEel)
    (by rw [card_barM_eq_of_isElemAbelian Nat.prime_three (by norm_num) hEel hEM, hE27]; norm_num)
    hEbY hEbP hrkE

end TwelveLe

end CFSG.LocalAnalysis.RankThreeTheoremC
