module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112a
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.LinearRank
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA.S10

section Layer

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

private theorem diag_bar {X B L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B) (hBX : B ≤ X)
    (hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B) (hL : GLAPComponent p X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.Open.IsKGroup (↥X ⧸ GLAPPrimeCore p ↥X) ∧
      GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ ∧ IsElemAbelian p (barX p X B) ∧
      GLATwoLocalRank p (↥X ⧸ GLAPPrimeCore p ↥X) ≤ CFSG.Open.pRank p (barX p X B) ∧
      GLAPComponent p ⊤ (barX p X L) ∧
      ¬ barX p X B ≤ Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  have : Fact p.Prime := ⟨hp⟩
  set N : Subgroup ↥X := GLAPPrimeCore p ↥X with hNdef
  have hNc : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hBp : IsPGroup p B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  refine ⟨isKGroup_quotient' hX N, glaPPrimeCore_quotient_eq_bot hp,
    isElemAbelian_barX hB, ?_, i112b_glaPComponent_of_isComponentOf
      (glaPPrimeCore_quotient_eq_bot hp) hL.2.2.1, ?_⟩
  · rw [rank_barX_of_isPGroup hp hBp hBX]
    exact (glaTwoLocalRank_quotient_le hp hp2 N hNc).trans hr
  · intro hle
    apply hnL
    intro b hb
    have h1 : QuotientGroup.mk' N ⟨b, hBX hb⟩ ∈
        Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) :=
      hle ⟨⟨b, hBX hb⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩
    have h2 : (⟨b, hBX hb⟩ : ↥X) ∈ (Subgroup.normalizer (L : Set G)).subgroupOf X := by
      rw [← i112f_comap_normalizer_barX hL]
      exact h1
    exact (Subgroup.mem_subgroupOf).1 h2


private theorem diag_barLayer (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) {X B L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hB : IsElemAbelian 3 B) (hBX : B ≤ X)
    (hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B) (hL : GLAPComponent 3 X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) {y : G} (hyB : y ∈ B)
    (hyn : y ∉ Subgroup.normalizer (L : Set G)) :
    IsSimpleGroup ↥(GLAPLayer 3 (barX 3 X (bClosure B L) ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩} :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ∧
      3 ∣ Nat.card ↥(GLAPLayer 3 (barX 3 X (bClosure B L) ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩} :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ∧
      Nonempty (↥(GLAPLayer 3 (barX 3 X (bClosure B L) ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩} :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ≃*
        (↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L))) := by
  obtain ⟨hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ :=
    diag_bar hX Nat.prime_three (by norm_num) hB hBX hr hL hnL
  obtain ⟨-, hrel, -, -, hZ9, hcase⟩ :=
    i112v_core T TL TT TM hQK Nat.prime_three (by norm_num) hQcore hBel hrankQ hLbar hnLQ
  have hJ : barX 3 X (bClosure B L) = i112J (barX 3 X B) (barX 3 X L) :=
    i112f_barX_bClosure hBX hL.1
  have hyB' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩ ∈ barX 3 X B :=
    ⟨⟨y, hBX hyB⟩, (Subgroup.mem_subgroupOf).2 hyB, rfl⟩
  have hyn' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩ ∉
      Subgroup.normalizer ((barX 3 X L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    intro h
    apply hyn
    have h2 : (⟨y, hBX hyB⟩ : ↥X) ∈ (Subgroup.normalizer (L : Set G)).subgroupOf X := by
      rw [← i112f_comap_normalizer_barX hL]
      exact h
    exact (Subgroup.mem_subgroupOf).1 h2
  have hZL : Nat.card ↥(barX 3 X L ⊓ Subgroup.centralizer
        ((barX 3 X L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) = 1 ∨
      Nat.card ↥(barX 3 X L ⊓ Subgroup.centralizer
        ((barX 3 X L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) = 3 := by
    rw [card_center_eq]
    rcases hcase with ⟨h1, -⟩ | ⟨h3, -⟩
    · exact Or.inl h1
    · exact Or.inr h3
  have hZ : Nat.card ↥(i112J (barX 3 X B) (barX 3 X L) ⊓
      Subgroup.centralizer (i112J (barX 3 X B) (barX 3 X L) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) < 3 ^ 3 :=
    lt_of_le_of_lt hZ9 (by norm_num)
  have h := i112v_layer Nat.prime_three hQcore hBel hLbar hrel hyB' hyn' hZL hZ
  rw [hJ, inf_comm]
  exact h

private theorem diag_layer_G (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) {X B L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hB : IsElemAbelian 3 B) (hBX : B ≤ X)
    (hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B) (hL : GLAPComponent 3 X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) {y : G} (hyB : y ∈ B)
    (hyn : y ∉ Subgroup.normalizer (L : Set G)) :
    GLAPComponent 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))
        (GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ∧
      Nonempty ((↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ⧸
          GLAPPrimeCore 3 ↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G)))) ≃*
        (↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L))) ∧
      IsSimpleGroup (↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ⧸
          GLAPPrimeCore 3 ↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G)))) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hs, hdvd, ⟨e₁⟩⟩ := diag_barLayer T TL TT TM hX hB hBX hr hL hnL hyB hyn
  have hJX : bClosure B L ≤ X := by
    refine iSup₂_le fun b hb => ?_
    rw [← mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBX hb))]
    exact CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono b hL.1
  have hyJ : y ∈ Subgroup.normalizer ((bClosure B L : Subgroup G) : Set G) :=
    i112_B_le_normalizer_J (B := B) (L := L) hyB
  have hy3 : IsPGroup 3 (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    by_cases hy1 : y = 1
    · exact absurd (by rw [hy1]; exact Subgroup.one_mem _) hyn
    · exact orderOf_eq_prime (hB.2 y hyB) hy1
  have hbar := barX_inf_centralizer hp (hBX hyB) hJX hyJ hy3
  have hHX : bClosure B L ⊓ Subgroup.centralizer ({y} : Set G) ≤ X := inf_le_left.trans hJX
  rw [← hbar] at hs e₁ hdvd
  obtain ⟨hc, ⟨e₂⟩⟩ := i112v_layer_lift hp hHX hs
  have : IsSimpleGroup ↥(GLAPLayer 3 (barX 3 X (bClosure B L ⊓
      Subgroup.centralizer ({y} : Set G)))) := hs
  have hO := i112v_glaPPrimeCore_eq_bot hp hdvd
  have eQ := e₂.trans ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
  exact ⟨hc, ⟨e₂.trans ((QuotientGroup.quotientMulEquivOfEq hO).trans
    (QuotientGroup.quotientBot.trans e₁))⟩, eQ.isSimpleGroup⟩

end Layer

section Diag2


theorem i112d_diag2 {G : Type} [Group G] [Finite G] {X K B : Subgroup G}
    (hK : GLAPComponent 3 X K) (hB : IsElemAbelian 3 B) (hchev : IsChevSimple 2 (PSimple 3 K))
    (hinn : InnDiagOn 3 B K) (hcard : 3 ^ 2 * Nat.card ↥(B ⊓ centModSubgroup 3 K) ≤ Nat.card B)
    (hZ : Subgroup.center (PQuot 3 K) = ⊥) {i : TauCeti.CFSGIndex} (hi : weakExcIndex i)
    (e : PQuot 3 K ≃* i.Group) : catalogIs (PSimple 3 K) diag2Index := by
  have eS : PSimple 3 K ≃* PQuot 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hZ' : Subgroup.center (PSimple 3 K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_center_iff] at hx
    have hx' : eS x ∈ Subgroup.center (PQuot 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := eS.surjective y
      rw [← map_mul, ← map_mul, hx y']
    have hx'' : eS x ∈ (⊥ : Subgroup (PQuot 3 K)) := by
      rw [← hZ]
      exact hx'
    rw [Subgroup.mem_bot] at hx'' ⊢
    exact eS.injective (by rw [hx'', map_one])
  have e' : PSimple 3 K ≃* i.Group := eS.trans e
  rcases hi with hi | hi
  · cases i with
    | cyclic p hp => exact hi.elim
    | alternating n hn =>
      have h67 : n = 6 ∨ n = 7 := hi
      rcases h67 with rfl | rfl
      · exact ⟨.alternating 6 hn, Or.inr rfl, ⟨e'⟩⟩
      · exact (i112d_not_chev_alt7 e' hchev).elim
    | sporadic s =>
      have hs : s = .M22 := hi
      subst hs
      exact (i112d_not_chev_m22 e' hchev).elim
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | A r q =>
        match r, hv, hi, e' with
        | 2, hv, hi, e' =>
          have hi' : q.card % 9 = 4 ∨ q.card % 9 = 7 := hi
          have hp2 := i112d_chev_A2_char q hv hi' e' hchev
          have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp2]
          rw [hqc] at hi'
          exact ⟨.lie ⟨.A 2 q, hv⟩, Or.inl ⟨hp2, (i112d_two_pow_mod_nine_A _).1 hi'⟩, ⟨e'⟩⟩
        | 0, _, hi, _ => exact (show False from hi).elim
        | 1, _, hi, _ => exact (show False from hi).elim
        | n + 3, _, hi, _ => exact (show False from hi).elim
      | twistedA r q =>
        match r, hv, hi, e' with
        | 2, hv, hi, e' =>
          have hi' : q.card % 9 = 2 ∨ q.card % 9 = 5 := hi
          have hp2 := i112d_chev_twistedA2_char q hv hi' e' hchev
          have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp2]
          rw [hqc] at hi'
          exact ⟨.lie ⟨.twistedA 2 q, hv⟩, Or.inl ⟨hp2, (i112d_two_pow_mod_nine_U _).1 hi'⟩,
            ⟨e'⟩⟩
        | 0, _, hi, _ => exact (show False from hi).elim
        | 1, _, hi, _ => exact (show False from hi).elim
        | n + 3, _, hi, _ => exact (show False from hi).elim
      | _ => exact (show False from hi).elim
  · exfalso
    cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | A r q =>
        match r, hv, hi, e' with
        | 1, hv, hi, e' =>
          obtain ⟨h2, h3, h4⟩ := hi
          obtain ⟨p, n, hp, hn⟩ := q
          obtain rfl : p = 2 := h2
          have hL2 : IsL2TwoPowOdd (PSimple 3 K) :=
            ⟨n, h3, h4, ⟨e'.trans
              (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨2, n, hp, hn⟩ hv)⟩⟩
          exact i112d_l2_false hK hB hinn hcard hZ' hL2
        | 0, _, hi, _ => exact hi.elim
        | n + 2, _, hi, _ => exact hi.elim
      | _ => exact hi.elim

end Diag2

section Main

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census


theorem i112DiagAt_holds
    (G : Type) [Group G] [Finite G] : I112DiagAt G := by
  intro p X B M K b hp hp2 hX hB hBX hr hM hbB hbn hK hchev hinn hcard
  have hnM : ¬ B ≤ Subgroup.normalizer (M : Set G) := fun h => hbn (h hbB)
  obtain ⟨rfl, hall⟩ := i112StarAt_holds G p hp hp2 X B M hX hBX hB hr hM hnM
  have hcat := hall b hbB hbn K hK
  have hK' : GLAPComponent 3 (bClosure B M ⊓ Subgroup.centralizer ({b} : Set G)) K := by
    rw [← closureIn_eq_bClosure]
    exact hK
  obtain ⟨hcomp, -, hsimp⟩ := diag_layer_G tables112_holds tableL2_unconditional
    tables112Types_holds tables112More_holds hX hB hBX hr hM hnM hbB hbn
  have hKeq : K = GLAPLayer 3 (bClosure B M ⊓ Subgroup.centralizer ({b} : Set G)) :=
    Lemma53Ns.glaPComponent_eq_of_le Nat.prime_three hK' hcomp (le_sSup hK')
  have hQsimp := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hs : IsSimpleGroup (PQuot 3 K) := by
    subst hKeq
    exact hsimp
  have hZ : Subgroup.center (PQuot 3 K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PQuot 3 K)) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (PQuot 3 K ⧸ Subgroup.center (PQuot 3 K)) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      haveI := hQsimp.2.toNontrivial
      exact not_subsingleton _ hsub
  refine ⟨rfl, ?_, hZ⟩
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  exact i112d_diag2 hK hB hchev hinn hcard hZ hi e

end Main

end CFSG.LocalAnalysis.GLTheoremA
