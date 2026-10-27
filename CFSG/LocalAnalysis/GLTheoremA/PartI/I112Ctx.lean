module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VLayer
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem i112c_bar (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {X B L : Subgroup G} (hB : IsElemAbelian p B) (hBX : B ≤ X)
    (hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B) (hL : GLAPComponent p X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    X ≠ ⊤ ∧ CFSG.Open.IsKGroup (↥X ⧸ GLAPPrimeCore p ↥X) ∧
      GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ ∧ IsElemAbelian p (barX p X B) ∧
      GLATwoLocalRank p (↥X ⧸ GLAPPrimeCore p ↥X) ≤ CFSG.Open.pRank p (barX p X B) ∧
      GLAPComponent p ⊤ (barX p X L) ∧
      ¬ barX p X B ≤ Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hXne : X ≠ ⊤ := by
    rintro rfl
    apply hnL
    rcases i112f_eq_bot_or_top_of_isSubnormal hL.2.1 with h | h
    · have hN : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.2 inferInstance
      rw [h, hN]
      exact le_top
    · have hN : Subgroup.normalizer ((⊤ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.2 inferInstance
      rw [h, hN]
      exact le_top
  have hXK : CFSG.Open.IsKGroup ↥X := isKGroup_of_isKProper hKP hXne
  set N : Subgroup ↥X := GLAPPrimeCore p ↥X with hNdef
  have hNc : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hBp : IsPGroup p B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  refine ⟨hXne, isKGroup_quotient' hXK N, glaPPrimeCore_quotient_eq_bot hp,
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

theorem i112c_full (T : Tables112) (TL : TableL2) (TT : Tables112Types) (hsimple : IsSimpleGroup G)
    (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X B L : Subgroup G}
    (hB : IsElemAbelian p B) (hBX : B ≤ X) (hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B)
    (hL : GLAPComponent p X L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    X ≠ ⊤ ∧ p = 3 ∧ (Subgroup.normalizer (L : Set G)).relIndex B = 3 ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 L))) ≤ 2 ∧
      (IsElemAbelian 3 (Subgroup.center ↥(barX 3 X (bClosure B L))) ∧
        Nat.card (Subgroup.center ↥(barX 3 X (bClosure B L))) ≤ 9) ∧
      (IsLTwoOddPow (barOf 3 L) ∨ IsHatSix (barOf 3 L) ∨ IsHatSeven (barOf 3 L) ∨
        IsHatMTwentyTwo (barOf 3 L) ∨ IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L) ∨
        IsSUThreeTwoPow (barOf 3 L)) := by
  obtain ⟨hXne, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ :=
    i112c_bar hsimple hKP hp hp2 hB hBX hr hL hnL
  obtain ⟨h3, hrel, haut, ⟨hZE, hZc⟩, htype⟩ :=
    i112f_core T TL TT hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  subst h3
  have e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp hL.1 hL.2.1
  refine ⟨hXne, rfl, (i112f_relIndex_barX hL hBX).symm.trans hrel, ?_, ?_, ?_⟩
  · rw [i112f_pRank_mulAut_of_mulEquiv e]
    exact haut
  · rw [i112f_barX_bClosure hBX hL.1]
    exact ⟨i112f_isElemAbelian_center hZE, (i112f_card_center _).trans_le hZc⟩
  · rcases htype with h | h | h | h | h | h
    · exact Or.inl (i112f_isLTwoOddPow_of_mulEquiv e.symm h)
    · exact Or.inr (Or.inl (i112f_isHatSix_of_mulEquiv e.symm h))
    · exact Or.inr (Or.inr (Or.inl (i112f_isHatSeven_of_mulEquiv e.symm h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (i112f_isHatMTwentyTwo_of_mulEquiv e.symm h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (i112f_isSLThreeExc_of_mulEquiv e.symm h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (i112f_isSUThreeExc_of_mulEquiv e.symm h))))))

theorem i112c_types (T : Tables112) (TL : TableL2) (TT : Tables112Types) (hsimple : IsSimpleGroup G)
    (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X B L : Subgroup G}
    (hB : IsElemAbelian p B) (hBX : B ≤ X) (hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B)
    (hL : GLAPComponent p X L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    X ≠ ⊤ ∧ p = 3 ∧ (Subgroup.normalizer (L : Set G)).relIndex B = 3 ∧
      (IsLTwoOddPow (barOf 3 L) ∨ IsHatSix (barOf 3 L) ∨ IsHatSeven (barOf 3 L) ∨
        IsHatMTwentyTwo (barOf 3 L) ∨ IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L) ∨
        IsSUThreeTwoPow (barOf 3 L)) := by
  obtain ⟨hXne, h3, hrel, -, -, htype⟩ :=
    i112c_full T TL TT hsimple hKP hp hp2 hB hBX hr hL hnL
  exact ⟨hXne, h3, hrel, htype⟩

theorem i112c_barLayer (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    {X B L : Subgroup G} (hB : IsElemAbelian 3 B) (hBX : B ≤ X)
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
  obtain ⟨-, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ :=
    i112c_bar hsimple hKP Nat.prime_three (by norm_num) hB hBX hr hL hnL
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

theorem i112c_layer_G (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    {X B L : Subgroup G} (hB : IsElemAbelian 3 B) (hBX : B ≤ X)
    (hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B) (hL : GLAPComponent 3 X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) {y : G} (hyB : y ∈ B)
    (hyn : y ∉ Subgroup.normalizer (L : Set G)) :
    GLAPComponent 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))
        (GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ∧
      Nonempty ((↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ⧸
          GLAPPrimeCore 3 ↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G)))) ≃*
        (↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L))) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hs, hdvd, ⟨e₁⟩⟩ := i112c_barLayer T TL TT TM hsimple hKP hB hBX hr hL hnL hyB hyn
  have hJX : bClosure B L ≤ X := by
    refine iSup₂_le fun b hb => ?_
    rw [← mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBX hb))]
    exact gLBConj_mono b hL.1
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
  exact ⟨hc, ⟨e₂.trans ((QuotientGroup.quotientMulEquivOfEq hO).trans
    (QuotientGroup.quotientBot.trans e₁))⟩⟩

end CFSG.LocalAnalysis.GLTheoremA
