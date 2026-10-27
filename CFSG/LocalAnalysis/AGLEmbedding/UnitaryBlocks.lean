module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBRel
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryData
import CFSG.LocalAnalysis.AGLEmbedding.ComponentCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.BlockData
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section UnitaryBlocks

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G} {M H R U X : Subgroup G}

theorem D1UnitaryData.barM_le_centralizer_of_weakSBlock (hB3 : StmtBlockThree)
    (hLB : StmtLemmaBRel) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (h : D1UnitaryData p n P M H R U X) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M U ≤ Subgroup.centralizer (barM M L : Set _) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ph3.ne_two
  obtain ⟨r, t, hr, hnr, hrp, hrp1, htK, htU, htr, htrU, htnt, hirr⟩ := h.ppd
  have : Fact r.Prime := ⟨hr⟩
  have hn2 := h.two_le
  have hB3' : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockHasThree M (pCoreOf 2 H) L' := fun L' hL' => hB3 h.ph3 hL'
  have hUK : U ≤ H ⊓ M := h.le_R.trans h.ph3.le_inf
  have hXU : X ≤ U := h.center_eq ▸ inf_le_left
  have hXc : X ≤ Subgroup.centralizer (U : Set G) := h.center_eq ▸ inf_le_right
  have hcase : p = 3 ∨ 5 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 5 with h5 | h5
    · interval_cases p
      · exact absurd rfl hp2
      · exact Or.inl rfl
      · exact absurd hp (by decide)
    · exact Or.inr h5
  have htL : t ∈ Subgroup.normalizer (L : Set G) := by
    by_contra htL
    have hle := h.ph3.le_pRank_three_of_not_mem_normalizer' stmtComponentRank stmtBarPRankLift
      hB3' htK htr hL htL
    rcases hcase with hp3 | hp5
    · have := h.pRank_le
      subst hp3
      omega
    · exact h.ph3.false_of_four_le_pRank' h.ind Nat.prime_three (by decide) (by omega)
        (by omega)
  have htX : t ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htU ⊢
    rw [← h.commutator_eq, Subgroup.map_commutator, htU]
  obtain ⟨φ, -⟩ := h.torus
  have hXcard : Nat.card X = p ^ n := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card p n (by omega)]
  have hrel : X.relIndex U = p ^ (2 * n) := by
    have h1 := Subgroup.relIndex_mul_card X U
    rw [inf_of_le_left hXU, hXcard, h.card_eq] at h1
    have hpn : 0 < p ^ n := pow_pos hp.pos n
    have h2 : p ^ (3 * n) = p ^ (2 * n) * p ^ n := by rw [← pow_add]; congr 1; omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hpn h1
  have hUL : U ≤ Subgroup.normalizer (L : Set G) := by
    rcases hcase with hp3 | hp5
    · have htNUL : t ∈ Subgroup.normalizer
          ((U ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) := by
        have htNL : t ∈ Subgroup.normalizer
            ((Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) :=
          Subgroup.le_normalizer htL
        exact Subgroup.inf_normalizer_le_normalizer_inf ⟨htU, htNL⟩
      rcases eq_or_le_of_mem_normalizer h.commutator_eq hXc htX hirr inf_le_left htNUL with
        heq | hle
      · exact heq ▸ inf_le_right
      · exfalso
        have hidx := h.ph3.relIndex_le_pRank_three hB3' hUK hL
        have hne : (U ⊓ Subgroup.normalizer (L : Set G)).relIndex U ≠ 0 := by
          intro h0
          have h1 := Subgroup.relIndex_mul_card (U ⊓ Subgroup.normalizer (L : Set G)) U
          rw [h0, zero_mul] at h1
          exact Nat.card_pos.ne' h1.symm
        have h1 : X.relIndex U ≤ (U ⊓ Subgroup.normalizer (L : Set G)).relIndex U :=
          Subgroup.relIndex_le_of_le_left hle hne
        rw [hrel] at h1
        have h2 := h.pRank_le
        subst hp3
        have h3 : 2 * n < 3 ^ (2 * n) := Nat.lt_pow_self (by norm_num)
        omega
    · intro u hu
      by_contra huL
      have hup : IsPGroup p (Subgroup.zpowers u) :=
        isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using h.pow_eq_one u hu)
      have hle := h.ph3.le_pRank_three_of_not_mem_normalizer' stmtComponentRank
        stmtBarPRankLift hB3' (hUK hu) hup hL huL
      exact h.ph3.false_of_four_le_pRank' h.ind Nat.prime_three (by decide) (by omega)
        (by omega)
  obtain ⟨hnot1, -⟩ := h.ph3.nineThree_not_one h85 hD2 hL
  have hcop : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) →
      ⁅Y, Y⁆ = Y → p.Coprime (Nat.card Y) := by
    intro Y hY hperf
    have hYN := h.perfect_le Y (h.ph3.inf_eq_inf_normalizer_twoCore ▸ hY) hperf
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hYN)
      (glbPrimeCore_coprime p H)
  have hUp : IsPGroup p U := h.ph3.isPGroup_R.to_le h.le_R
  exact hLB G M (pCoreOf 2 H) L U X p r t h.ph3.isKGroup.1 h.ph3.asc81bHyp hL hnot1
    (h.ph3.not_isSylowTwoOf_inf h85 hD2 hL) hp hp2 hcop
    (h.ph3.inf_eq_inf_normalizer_twoCore ▸ hUK) hUL hUp h.commutator_eq hXc
    (fun u hu => by rw [h.pow_eq_one u hu]; exact X.one_mem)
    (by rw [hrel]; exact Nat.pow_le_pow_right hp.pos (by omega))
    (h.ph3.inf_eq_inf_normalizer_twoCore ▸ htK) htL htU hr (by omega) (by omega) hrp hrp1
    (fun u hu => by rw [htrU u hu, mul_inv_cancel]; exact X.one_mem) htnt hirr

theorem D1UnitaryData.barM_le_pCore (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hLB : StmtLemmaBRel) (hα : KFactThreeOrFiveDvd)
    (hβ : KFactOutElemRank) (h : D1UnitaryData p n P M H R U X) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
  have hX : X ≤ U := h.center_eq ▸ inf_le_left
  have hR1 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M X ≤ Subgroup.centralizer (barM M L : Set _) := fun L hL =>
    (Subgroup.map_mono (Subgroup.subgroupOf_mono M hX)).trans
      (h.barM_le_centralizer_of_weakSBlock hB3 hLB h85 hD2 hL)
  have hp2 : p ≠ 2 := h.ph3.ne_two
  have hp : p.Prime := Fact.out
  rcases (show p = 3 ∨ 5 ≤ p by
      have := hp.two_le
      rcases Nat.lt_or_ge p 5 with h5 | h5
      · interval_cases p
        · exact absurd rfl hp2
        · exact Or.inl rfl
        · exact absurd hp (by decide)
      · exact Or.inr h5) with hp3 | hp5
  · exact h.ph3.barM_le_pCore_of_forall_centralizer h84 hD2 hB3 hp3 (hX.trans h.le_R)
      h.normal_dichotomy hR1
  · exact h.toTorusData.barM_le_pCore h84 hD2 hα hβ hp5 hR1

theorem D1UnitaryData.normal_sup_of_le_pCore (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hLB : StmtLemmaBRel)
    (h : D1UnitaryData p n P M H R U X)
    (hX : barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)) :
    ((U ⊔ pCoreOf 2 M).subgroupOf M).Normal := by
  have hp : p.Prime := Fact.out
  set Y := pCorePreimage p M with hYdef
  set Q := pCoreOf 2 M with hQdef
  set N := GLBPrimeCore p H with hNdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hXU : X ≤ U := h.center_eq ▸ inf_le_left
  have hXc : X ≤ Subgroup.centralizer (U : Set G) := h.center_eq ▸ inf_le_right
  have hUH : U ≤ H := h.le_R.trans h.ph3.le_H
  have hUM : U ≤ M := h.le_R.trans h.ph3.le_M
  have hYK : Y ≤ H ⊓ M := h.ph3.pCorePreimage_le_inf h84 hD2
  have hMY : M ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_pCorePreimage p M
  have hYeq : (R ⊓ Y) ⊔ Q = Y := h.ph3.inf_sup_twoCore_eq h84 hD2
  have hQY : Q ≤ Y := le_sup_right.trans hYeq.le
  have hXY : X ≤ Y := fun x hx =>
    ⟨⟨x, hUM (hXU hx)⟩, hX ⟨⟨x, hUM (hXU hx)⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
  have hYp : ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ N := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ CFSG.pCore 2 ↥M) ⟨mk m, hm⟩
    refine ⟨k, h.ph3.twoCore_M_le_glbPrimeCore ?_⟩
    have hk' : mk (m ^ p ^ k) = 1 := by rw [map_pow]; exact congrArg Subtype.val hk
    simpa using coe_mem_pCoreOf_two_of_mk_eq_one _ hk'
  have hYUN : Y ≤ U ⊔ N := h.pcore_le Y hYK (inf_le_right.trans hMY) hYp
  have hRN : R ⊓ N = ⊥ := inf_eq_bot_of_isPGroup hp h.ph3.isPGroup_R (glbPrimeCore_coprime p H)
  have hRYU : R ⊓ Y ≤ U := by
    rintro a ⟨haR, haY⟩
    have ha : a ∈ ((U ⊔ N : Subgroup G) : Set G) := hYUN haY
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U N
      (hUH.trans (le_normalizer_glbPrimeCore p H))] at ha
    obtain ⟨u, hu, m, hm, hum⟩ := ha
    have hum' : u * m = a := hum
    have hmR : m ∈ R := by
      have : m = u⁻¹ * a := by rw [← hum']; group
      rw [this]
      exact R.mul_mem (R.inv_mem (h.le_R hu)) haR
    have hm1 : m = 1 := by
      have hmem : m ∈ R ⊓ N := ⟨hmR, hm⟩
      rwa [hRN, Subgroup.mem_bot] at hmem
    rw [← hum', hm1, mul_one]
    exact hu
  obtain ⟨r, t, hr, hnr, hrp, hrp1, htK, htU, htr, htrU, htnt, hirr⟩ := h.ppd
  have htUY : t ∈ Subgroup.normalizer ((U ⊓ Y : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htU, hMY htK.2⟩
  rcases hirr (U ⊓ Y) (le_inf hXU hXY) inf_le_left htUY with hUYX | hUYU
  ·
    exfalso
    have hNX : ⁅N, X⁆ ≤ Q :=
      (Subgroup.commutator_mono le_rfl hXY).trans (h.ph3.commutator_pCorePreimage_le h84 hD2)
    have hQS : Q ≤ pCoreOf 2 H := h.ph3.twoCore_M_le h.ph3.twoCore_inf
    have hNJ : ⁅N, nclIn H X⁆ ≤ pCoreOf 2 H :=
      CFSG.AGLEmbedding.commutator_nclIn_le (hXU.trans hUH) (le_normalizer_glbPrimeCore p H)
        (localGroup_le_normalizer_pCoreOf 2 H) (hNX.trans hQS)
    have hNU : ⁅N, U⁆ ≤ pCoreOf 2 H := (Subgroup.commutator_mono le_rfl h.le_nclIn).trans hNJ
    set Sb := barM M (pCoreOf 2 H) with hSb
    set Nb := barM M N with hNb
    set Ub := barM M U with hUb
    have hSbp : IsPGroup 2 Sb :=
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_subtype
        (K := M)).map _
    have hNS : N ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      (glbPrimeCore_le p H).trans (localGroup_le_normalizer_pCoreOf 2 H)
    have hNbS : Nb ≤ Subgroup.normalizer (Sb : Set _) := by
      rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
      exact mem_normalizer_barM hxM (hNS (Subgroup.mem_subgroupOf.mp hx))
    have hcomm : ∀ a ∈ Ub, ∀ x ∈ Nb, a * x * a⁻¹ * x⁻¹ ∈ Sb := by
      rintro _ ⟨⟨u, huM⟩, hu, rfl⟩ _ ⟨⟨m, hmM⟩, hm, rfl⟩
      have hc : u * m * u⁻¹ * m⁻¹ ∈ pCoreOf 2 H := by
        have h1 : ⁅m, u⁆ ∈ ⁅N, U⁆ := Subgroup.commutator_mem_commutator
          (Subgroup.mem_subgroupOf.mp hm) (Subgroup.mem_subgroupOf.mp hu)
        have h2 := (pCoreOf 2 H).inv_mem (hNU h1)
        rw [commutatorElement_def] at h2
        convert h2 using 1
        group
      refine ⟨⟨u, huM⟩ * ⟨m, hmM⟩ * (⟨u, huM⟩)⁻¹ * (⟨m, hmM⟩)⁻¹,
        Subgroup.mem_subgroupOf.mpr (by simpa using hc), ?_⟩
      simp only [map_mul, map_inv]
    have hUcomp : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
        Ub ≤ Subgroup.centralizer (Lb : Set _) := by
      intro Lb hLb
      obtain ⟨L, hL2, rfl, hL'⟩ := h.ph3.exists_weakSBlock_or_le_inf hLb
      rcases hL' with hw | hle
      · exact h.barM_le_centralizer_of_weakSBlock hB3 hLB h85 hD2 hw
      · have hLN : L ≤ N := h.perfect_le L hle hL2.perfect
        exact le_centralizer_of_forall_commutator_mem hLb
          (Subgroup.map_mono (Subgroup.subgroupOf_mono M hLN)) hSbp hNbS hcomm
    have hUcore : ∀ l : ℕ, l.Prime →
        Ub ≤ Subgroup.centralizer (CFSG.pCore l (↥M ⧸ CFSG.pCore 2 ↥M) : Set _) := by
      intro l hl
      by_cases hl2 : l = 2
      · rw [hl2, pCore_quotient_pCore_eq_bot']
        exact Subgroup.le_centralizer_iff.mp bot_le
      by_cases hlp : l = p
      · rw [hlp]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro o ho
        obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) o
        have hmY : (m : G) ∈ Y := ⟨m, ho, rfl⟩
        have hmY' : (m : G) ∈ (((R ⊓ Y) ⊔ Q : Subgroup G) : Set G) := by
          rw [SetLike.mem_coe, hYeq]
          exact hmY
        rw [Subgroup.coe_mul_of_left_le_normalizer_right (R ⊓ Y) Q
          ((inf_le_right.trans hYK).trans (inf_le_right.trans
            (localGroup_le_normalizer_pCoreOf 2 M)))] at hmY'
        obtain ⟨x, hx, q, hq, hxq⟩ := hmY'
        have hxq' : x * q = (m : G) := hxq
        have hxX : x ∈ X := hUYX ▸ ⟨hRYU hx, hx.2⟩
        have hxM : x ∈ M := hUM (hXU hxX)
        have hqM : q ∈ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hq
        have hmeq : m = ⟨x, hxM⟩ * ⟨q, hqM⟩ := Subtype.ext hxq'.symm
        have hq1 : mk ⟨q, hqM⟩ = 1 := (mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq
        rw [hmeq, map_mul, hq1, mul_one]
        obtain ⟨⟨u, huM⟩, hu, rfl⟩ := ha
        have hux : u * x = x * u :=
          Subgroup.mem_centralizer_iff.mp (hXc hxX) u (Subgroup.mem_subgroupOf.mp hu)
        rw [← map_mul, ← map_mul, show (⟨x, hxM⟩ : M) * ⟨u, huM⟩ = ⟨u, huM⟩ * ⟨x, hxM⟩ from
          Subtype.ext hux.symm]
      ·
        have : Fact l.Prime := ⟨hl⟩
        set Ol := CFSG.pCore l (↥M ⧸ CFSG.pCore 2 ↥M) with hOl
        set Sh : Subgroup G := (Ol.comap mk).map M.subtype with hSh
        have hShK : Sh ≤ H ⊓ M := h.ph3.preimage_le_inf (h.ph3.le_barM_inf_of_le_centralizer
          ((pCore_le_pPrimeCore_two hl hl2).trans (h.ph3.oddCore_le_centralizer h84 hD2)))
        have hShn : H ⊓ M ≤ Subgroup.normalizer (Sh : Set G) :=
          inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (Subgroup.map_subtype_le _)).mp (normal_preimage_subgroupOf Ol))
        have hShN : Sh ≤ N := by
          refine (h.normal_dichotomy Sh hShK hShn).resolve_right fun hXSh => ?_
          have hXOl : barM M X ≤ Ol := barM_le_of_le_preimage hXSh
          have hdisj := IsPGroup.disjoint_of_ne l p hlp Ol
            (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)) CFSG.pCore_isPGroup CFSG.pCore_isPGroup
          have hXb : barM M X = ⊥ :=
            le_bot_iff.mp fun x hx => hdisj.le_bot ⟨hXOl hx, hX hx⟩
          obtain ⟨φ, -⟩ := h.torus
          have hXcard : Nat.card X = p ^ n := by
            rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
              GaloisField.card p n (by have := h.two_le; omega)]
          have hXQ : X ≤ Q := by
            intro x hx
            have hxM : x ∈ M := hUM (hXU hx)
            have h1 : mk ⟨x, hxM⟩ = 1 := by
              have : mk ⟨x, hxM⟩ ∈ barM M X :=
                Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
              rw [hXb] at this
              exact this
            exact coe_mem_pCoreOf_two_of_mk_eq_one ⟨x, hxM⟩ h1
          have hXp : IsPGroup p X := h.ph3.isPGroup_R.to_le (hXU.trans h.le_R)
          have hXbot : X = ⊥ := by
            have hdisj2 := IsPGroup.disjoint_of_ne p 2 h.ph3.ne_two X Q hXp
              (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
            exact le_bot_iff.mp fun x hx => hdisj2.le_bot ⟨hx, hXQ hx⟩
          rw [hXbot, Subgroup.card_bot] at hXcard
          have := Nat.one_lt_pow (by have := h.two_le; omega : n ≠ 0) hp.one_lt
          omega
        have hOlN : Ol ≤ Nb := by
          rw [← barM_preimage Ol]
          exact Subgroup.map_mono (Subgroup.subgroupOf_mono M hShN)
        exact le_centralizer_pCore_of_forall_commutator_mem hl hl2 hSbp hOlN hcomm
    have hUbp : IsPGroup p Ub :=
      ((h.ph3.isPGroup_R.to_le h.le_R).comap_subtype (K := M)).map _
    have hUbO := le_pCore_of_le_centralizer_components hUbp hUcomp hUcore
    have hUY : U ≤ Y := fun u hu =>
      ⟨⟨u, hUM hu⟩, hUbO ⟨⟨u, hUM hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩, rfl⟩
    have hUX : U ≤ X := hUYX ▸ le_inf le_rfl hUY
    obtain ⟨φ, -⟩ := h.torus
    have hXcard : Nat.card X = p ^ n := by
      rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
        GaloisField.card p n (by have := h.two_le; omega)]
    have hle := Subgroup.card_le_of_le hUX
    rw [h.card_eq, hXcard] at hle
    have := h.two_le
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    omega
  ·
    have hUY : U ≤ Y := hUYU ▸ inf_le_right
    have heq : U ⊔ Q = Y := by
      refine le_antisymm (sup_le hUY hQY) ?_
      calc Y = (R ⊓ Y) ⊔ Q := hYeq.symm
        _ ≤ U ⊔ Q := sup_le_sup_right hRYU Q
    rw [heq, pCorePreimage_subgroupOf]
    exact Subgroup.Normal.comap inferInstance _

end UnitaryBlocks

end CFSG.AGLEmbedding
