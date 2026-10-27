module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89
public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.Adapters.TauCetiExceptional.ReeCatalog
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Core
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7E5Order
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1122

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.LinearRank
  CFSG.Assembly.LowTwoRank

private theorem cat_card_le_nine_of_dvd {M : Type} [Group M] [Finite M] {E : Subgroup M}
    (hE : IsElemAbelian 3 E) {m : ℕ} (hm : ¬ 27 ∣ m) (hdvd : Nat.card E ∣ m) :
    Nat.card E ≤ 9 := by
  have hP : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  rw [hk] at hdvd ⊢
  have hk2 : k ≤ 2 := by
    by_contra h
    apply hm
    have h27 : (27 : ℕ) ∣ 3 ^ k := by
      have := Nat.pow_dvd_pow 3 (show 3 ≤ k by omega)
      norm_num at this
      exact this
    exact h27.trans hdvd
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

private theorem cat_card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem cat_card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem cat_card_m22 : Nat.card TauCeti.SporadicName.M22.Group = 443520 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M22.tauCeti_finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M22.le_card_native
  rw [Nat.card_congr e.toEquiv] at h2
  omega

private theorem cat_excLie_shape {d : TauCeti.LieTypeIndex} {hv : d.Valid}
    (h : excIndex (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    (∃ q : TauCeti.PrimePower, d = .A 2 q ∧ (q.card % 9 = 4 ∨ q.card % 9 = 7)) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedA 2 q ∧ (q.card % 9 = 2 ∨ q.card % 9 = 5)) := by
  cases d with
  | A r q =>
    match r, hv, h with
    | 2, _, h => exact Or.inl ⟨q, rfl, h⟩
    | 0, _, h => exact (show False from h).elim
    | 1, _, h => exact (show False from h).elim
    | n + 3, _, h => exact (show False from h).elim
  | twistedA r q =>
    match r, hv, h with
    | 2, _, h => exact Or.inr ⟨q, rfl, h⟩
    | 0, _, h => exact (show False from h).elim
    | 1, _, h => exact (show False from h).elim
    | n + 3, _, h => exact (show False from h).elim
  | _ => exact (show False from h).elim

private theorem cat_suThree_pRank_le_two (x y : ℕ) [Fact x.Prime] (hy : 0 < y)
    (hq : x ^ y % 9 = 2 ∨ x ^ y % 9 = 5) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU (2 + 1) (x ^ y)
      (GaloisField x (2 * y))))) ≤ 2 := by
  have hc : Nat.card (GaloisField x (2 * y)) = (x ^ y) ^ 2 := by
    rw [GaloisField.card _ _ (by omega), ← pow_mul, mul_comm]
  have hdvd : 3 ∣ x ^ y + 1 := by omega
  have hS := pRank_statedProj_le (K := GaloisField x (2 * y)) (p := 3) (f := y) (r := x) (n := 3)
    Nat.prime_three (by norm_num) (by norm_num)
    (H := StatedSU 3 (x ^ y) (GaloisField x (2 * y))) (Or.inr ⟨hc, rfl, hdvd⟩)
  exact hS

private theorem cat_card_le_nine_of_weakExc {i : TauCeti.CFSGIndex} (hi : weakExcIndex i)
    {M : Type} [Group M] [Finite M] (e : M ≃* i.Group) {E : Subgroup M}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have key : ∀ k : ℕ, CFSG.Open.pRank 3 (⊤ : Subgroup M) ≤ k → Nat.card E ≤ 3 ^ k :=
    fun k hk => card_le_of_pRank_le Nat.prime_three hk E hE
  cases i with
  | cyclic p hp =>
    rcases hi with h | h
    · exact (show False from h).elim
    · exact (show False from h).elim
  | alternating n hn =>
    rcases hi with h | h
    · rcases h with rfl | rfl
      · have hM : Nat.card M = 360 := (Nat.card_congr e.toEquiv).trans cat_card_alt_six
        exact cat_card_le_nine_of_dvd hE (by norm_num) (hM ▸ Subgroup.card_subgroup_dvd_card E)
      · have hM : Nat.card M = 2520 := (Nat.card_congr e.toEquiv).trans cat_card_alt_seven
        exact cat_card_le_nine_of_dvd hE (by norm_num) (hM ▸ Subgroup.card_subgroup_dvd_card E)
    · exact (show False from h).elim
  | sporadic s =>
    rcases hi with h | h
    · obtain rfl : s = .M22 := h
      have hM : Nat.card M = 443520 := (Nat.card_congr e.toEquiv).trans cat_card_m22
      exact cat_card_le_nine_of_dvd hE (by norm_num) (hM ▸ Subgroup.card_subgroup_dvd_card E)
    · exact (show False from h).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    rcases hi with h | h
    · rcases cat_excLie_shape h with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
      ·
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        have eP : M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3)
            (GaloisField q.p q.exponent) :=
          e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)
        have hc : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
          GaloisField.card _ _ q.exponent_pos.ne'
        have hdvd : 3 ∣ q.p ^ q.exponent - 1 := by
          rw [TauCeti.PrimePower.card_def] at hq
          omega
        have hS := pRank_statedProj_le (K := GaloisField q.p q.exponent) (p := 3)
          (f := q.exponent) (r := q.p) (n := 3) Nat.prime_three (by norm_num) (by norm_num)
          (H := StatedSL 3 (GaloisField q.p q.exponent)) (Or.inl ⟨hc, rfl, hdvd⟩)
        have hPSL := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
          (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField q.p q.exponent))
        have hMP := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eP
        have hpr : CFSG.Open.pRank 3 (⊤ : Subgroup M) ≤ 2 := by
          rw [hMP, hPSL]
          exact hS
        have := key 2 hpr
        norm_num at this
        exact this
      ·
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        have eU := e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)
        have hch : TauCeti.ValidLieTypeIndex.characteristic
            (⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) = q.p :=
          TauCeti.LieTypeIndex.characteristic_twistedA 2 q
        have hfe : TauCeti.ValidLieTypeIndex.fieldExponent
            (⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) = q.exponent :=
          TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
        rw [TauCeti.PrimePower.card_def] at hq
        have hq' : TauCeti.ValidLieTypeIndex.characteristic
              (⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) ^
            TauCeti.ValidLieTypeIndex.fieldExponent
              (⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) % 9 = 2 ∨
          TauCeti.ValidLieTypeIndex.characteristic
              (⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) ^
            TauCeti.ValidLieTypeIndex.fieldExponent
              (⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) % 9 = 5 := by
          rw [hch, hfe]
          exact hq
        have hy : 0 < TauCeti.ValidLieTypeIndex.fieldExponent
            (⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) := by
          rw [hfe]
          exact q.exponent_pos
        have hS := cat_suThree_pRank_le_two _ _ hy hq'
        have hMU := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eU
        have hpr : CFSG.Open.pRank 3 (⊤ : Subgroup M) ≤ 2 := by
          rw [hMU]
          exact hS
        have := key 2 hpr
        norm_num at this
        exact this
    ·
      cases d with
      | A r q =>
        match r, hv, h with
        | 1, hv, h =>
          obtain ⟨h2, h3, h4⟩ := h
          obtain ⟨p, n, hp, hn⟩ := q
          obtain rfl : p = 2 := h2
          have hL2 : IsL2TwoPowOdd M :=
            ⟨n, h3, h4, ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨2, n, hp, hn⟩ hv)⟩⟩
          have := key 1 (CFSG.HardMathSupport.Timmesfeld.Tables.Census.pRank_three_le_one_of_isL2TwoPowOdd hL2)
          calc Nat.card E ≤ 3 ^ 1 := this
            _ ≤ 9 := by norm_num
        | 0, _, h => exact (show False from h).elim
        | n + 2, _, h => exact (show False from h).elim
      | _ => exact (show False from h).elim

theorem i112RankAt_holds (G : Type) [Group G] [Finite G] : S8.L89.I112RankAt G := by
  intro J hJ E hEJ hE
  obtain ⟨i, hi, ⟨e⟩⟩ := hJ
  have hEp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  set f : ↥(E.subgroupOf J) →* (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).comp (E.subgroupOf J).subtype with hf
  have hinj : Function.Injective f := injective_barX_comp Nat.prime_three hEp hEJ
  have hrange : barX 3 J E = (⊤ : Subgroup ↥(E.subgroupOf J)).map f := by
    rw [hf, ← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
    rfl
  have hcard : Nat.card (barX 3 J E) = Nat.card E := by
    rw [hrange, Nat.card_congr (Subgroup.equivMapOfInjective _ f hinj).toEquiv.symm,
      Subgroup.card_top, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv]
  have := cat_card_le_nine_of_weakExc hi e (isElemAbelian_barX hE)
  rw [hcard] at this
  norm_num
  exact this


section Star

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

private theorem cat_catalogIs_mono {S : Type} [Group S] {Q Q' : TauCeti.CFSGIndex → Prop}
    (h : catalogIs S Q) (hQ : ∀ i, Q i → Q' i) : catalogIs S Q' := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hQ i hi, ⟨f⟩⟩

private theorem cat_valid_A_one (n : ℕ) (hn : Odd n) (hn1 : 1 < n) (hpos : 0 < n) :
    (TauCeti.LieTypeIndex.A 1 ⟨2, n, Nat.prime_two, hpos⟩).Valid := by
  obtain ⟨k, hk⟩ := hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, TauCeti.PrimePower.card_def]
  have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

private theorem cat_weakExc_of_isL2TwoPowOdd {X : Type} [Group X] (h : IsL2TwoPowOdd X) :
    catalogIs X weakExcIndex := by
  obtain ⟨n, hn, hn1, ⟨e⟩⟩ := h
  have hpos : 0 < n := by omega
  have hv := cat_valid_A_one n hn hn1 hpos
  refine ⟨TauCeti.CFSGIndex.lie ⟨.A 1 ⟨2, n, Nat.prime_two, hpos⟩, hv⟩, ?_,
    ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨2, n, Nat.prime_two, hpos⟩ hv).symm⟩⟩
  exact Or.inr ⟨rfl, hn, hn1⟩

private theorem cat_five_types {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    (h : IsHatSix X ∨ IsHatSeven X ∨ IsHatMTwentyTwo X ∨ IsSLThreeExc X ∨ IsSUThreeExc X) :
    IsExcShape X := by
  refine isExcShape_of_types hX ?_
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private theorem cat_bar {X B L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) {p : ℕ}
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


private theorem cat_barLayer (T : Tables112) (TL : TableL2) (TT : Tables112Types)
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
    cat_bar hX Nat.prime_three (by norm_num) hB hBX hr hL hnL
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

private theorem cat_layer_G (T : Tables112) (TL : TableL2) (TT : Tables112Types)
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
  obtain ⟨hs, hdvd, ⟨e₁⟩⟩ := cat_barLayer T TL TT TM hX hB hBX hr hL hnL hyB hyn
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

end Star

section Tables

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census



theorem i112StarAt_holds
    (G : Type) [Group G] [Finite G] (p : ℕ) : I112StarAt G p := by
  intro hp hp2 X B L hX hBX hB hr hL hnL
  obtain ⟨hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ := cat_bar hX hp hp2 hB hBX hr hL hnL
  obtain ⟨h3, -, -, -, -, hcase⟩ := i112v_core tables112_holds tableL2_unconditional
    tables112Types_holds tables112More_holds hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  subst h3
  refine ⟨rfl, fun b hbB hbn J hJ => ?_⟩
  rw [closureIn_eq_bClosure] at hJ
  obtain ⟨hcomp, ⟨eM⟩, -⟩ := cat_layer_G tables112_holds tableL2_unconditional
    tables112Types_holds tables112More_holds hX hB hBX hr hL hnL hbB hbn
  have hJeq : J = GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({b} : Set G)) :=
    Lemma53Ns.glaPComponent_eq_of_le Nat.prime_three hJ hcomp (le_sSup hJ)
  subst hJeq
  refine (catalogIs_congr eM).2 ?_
  rcases hcase with ⟨h1, -, -, hiso⟩ | ⟨h3, htypes, -⟩
  · have hcen : Subgroup.center ↥(barX 3 X L) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have eZ : ↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L) ≃* ↥(barX 3 X L) :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    exact (catalogIs_congr eZ).2 (cat_weakExc_of_isL2TwoPowOdd (isL2TwoPowOdd_of_isLTwoOddPow hiso))
  · have hQL := i116e_isQuasisimple hQcore hLbar
    exact cat_catalogIs_mono (cat_five_types hQL htypes).2 fun i hi => Or.inl hi

theorem i112RkAt_holds
    (G : Type) [Group G] [Finite G] : I112RkAt G := by
  intro X B L hX hBX hB hr hL hnL b hbB hbn J hJ E hEJ hE
  have h := i112StarAt_holds G 3 Nat.prime_three (by norm_num) X B L hX hBX hB hr hL hnL
  exact i112RankAt_holds G J (h.2 b hbB hbn J hJ) E hEJ hE

section OddModels

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

private theorem cat_of_models
    {S : Type} [Group S] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : CFSG.Models.LieModel S t n p f) :
    ∃ (t' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible t' n' p f' ∧
      CFSG.Blueprint.LieModel S t' n' p f' :=
  ⟨t, n, f, h.1, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel ht h⟩

private theorem cat_lm_A
    {S : Type} [Group S] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f :=
  cat_of_models (by decide) (CFSG.Models.lieModel_A r q hv e)

private theorem cat_lm_twistedA
    {S : Type} [Group S] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f := by
  have h := CFSG.Models.lieModel_twistedA r q hv e
  have hc : ValidLieTypeIndex.characteristic ⟨LieTypeIndex.twistedA r q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA r q
  have hf : ValidLieTypeIndex.fieldExponent ⟨LieTypeIndex.twistedA r q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA r q
  rw [hc, hf] at h
  exact cat_of_models (by decide) h

private theorem cat_lm_B
    {S : Type} [Group S] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f := by
  rcases CFSG.Models.lieModel_B r q hv e with h | h
  · exact cat_of_models (by decide) h
  · exact cat_of_models (by decide) h

private theorem cat_lm_C
    {S : Type} [Group S] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.C r q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f :=
  cat_of_models (by decide) (CFSG.Models.lieModel_C r q hv e)

private theorem cat_lm_D
    {S : Type} [Group S] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f :=
  cat_of_models (by decide) (CFSG.Models.lieModel_D r q hv e)

private theorem cat_lm_twistedD
    {S : Type} [Group S] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f :=
  cat_of_models (by decide) (CFSG.Models.lieModel_twistedD r q hv e)

private theorem cat_lm_E6
    {S : Type} [Group S] (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (hp : q.p ≠ 2) (e : S ≃* ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hp (GaloisField q.p q.exponent)
    (by rw [hK, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .E6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance, inferInstance,
      hK, ⟨e.trans b.symm⟩⟩
  exact ⟨.E6, 0, q.exponent, hC.1, Or.inr (Or.inl ⟨rfl, by decide, hC⟩)⟩

private theorem cat_lm_E7
    {S : Type} [Group S] (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    (hp : q.p ≠ 2) (e : S ≃* ValidLieTypeIndex.Group ⟨.E7 q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hp (GaloisField q.p q.exponent)
    (by rw [hK, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .E7 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance, inferInstance,
      hK, ⟨e.trans b.symm⟩⟩
  exact ⟨.E7, 0, q.exponent, hC.1, Or.inr (Or.inl ⟨rfl, by decide, hC⟩)⟩

private theorem cat_lm_E8
    {S : Type} [Group S] (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    (hp : q.p ≠ 2) (e : S ≃* ValidLieTypeIndex.Group ⟨.E8 q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hp (GaloisField q.p q.exponent)
    (by rw [hK, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .E8 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance, inferInstance,
      hK, ⟨e.trans b.symm⟩⟩
  exact ⟨.E8, 0, q.exponent, hC.1, Or.inr (Or.inl ⟨rfl, by decide, hC⟩)⟩

private theorem cat_lm_F4
    {S : Type} [Group S] (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    (hp : q.p ≠ 2) (e : S ≃* ValidLieTypeIndex.Group ⟨.F4 q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.f4 q hv hp (GaloisField q.p q.exponent)
    (by rw [hK, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .F4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance, inferInstance,
      hK, ⟨e.trans b.symm⟩⟩
  exact ⟨.F4, 0, q.exponent, hC.1, Or.inr (Or.inl ⟨rfl, by decide, hC⟩)⟩

private theorem cat_lm_G2
    {S : Type} [Group S] (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid)
    (hp : q.p ≠ 2) (hr : 3 ≤ q.card) (e : S ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hp (GaloisField q.p q.exponent)
    (by rw [hK, TauCeti.PrimePower.card_def])
  have h3 : 3 ≤ q.p ^ q.exponent := by rw [← TauCeti.PrimePower.card_def]; exact hr
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩, GaloisField q.p q.exponent, inferInstance,
      inferInstance, hK, ⟨e.trans b.symm⟩⟩
  exact ⟨.G2, 0, q.exponent, hC.1, Or.inr (Or.inl ⟨rfl, by decide, hC⟩)⟩

end OddModels

section OddModels2

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

private theorem cat_lm_twistedE6
    {S : Type} [Group S] (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) (hp : q.p ≠ 2)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hto : 0 < (TwistTag.E6).order := by decide
  have hKc : Nat.card (GaloisField q.p (q.exponent * (TwistTag.E6).order)) =
      (q.p ^ q.exponent) ^ (TwistTag.E6).order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hto.ne'), pow_mul]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.twistedE6 q hv hp
    (GaloisField q.p (q.exponent * (TwistTag.E6).order))
    (by rw [hKc, TauCeti.PrimePower.card_def])
    (iterateFrobenius _ q.p q.exponent)
    (fun x => by rw [iterateFrobenius_def, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p (q.exponent * (TwistTag.E6).order),
      inferInstance, inferInstance, hKc, iterateFrobenius _ q.p q.exponent,
      fun x => by rw [iterateFrobenius_def], ⟨e.trans b.symm⟩⟩
  exact ⟨.twistedE6, 0, q.exponent, hC.1, Or.inr (Or.inl ⟨rfl, by decide, hC⟩)⟩

private theorem cat_lm_trialityD4
    {S : Type} [Group S] (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hp : q.p ≠ 2)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n q.p f ∧
      CFSG.Blueprint.LieModel S t n q.p f := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hto : 0 < (TwistTag.D4).order := by decide
  have hKc : Nat.card (GaloisField q.p (q.exponent * (TwistTag.D4).order)) =
      (q.p ^ q.exponent) ^ (TwistTag.D4).order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hto.ne'), pow_mul]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv hp
    (GaloisField q.p (q.exponent * (TwistTag.D4).order))
    (by rw [hKc, TauCeti.PrimePower.card_def])
    (iterateFrobenius _ q.p q.exponent)
    (fun x => by rw [iterateFrobenius_def, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p (q.exponent * (TwistTag.D4).order),
      inferInstance, inferInstance, hKc, iterateFrobenius _ q.p q.exponent,
      fun x => by rw [iterateFrobenius_def], ⟨e.trans b.symm⟩⟩
  exact ⟨.trialityD4, 0, q.exponent, hC.1, Or.inr (Or.inl ⟨rfl, by decide, hC⟩)⟩

private theorem cat_lm_reeG2
    {S : Type} [Group S] (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid)
    (hm : 1 ≤ m) (e : S ≃* ValidLieTypeIndex.Group ⟨.reeG2 m, hv⟩) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 3 f ∧
      CFSG.Blueprint.LieModel S t n 3 f := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card _ _ (by omega)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.typewiseBridges.reeG2 m hv (GaloisField 3 (2 * m + 1)) hK
  have hR : CFSG.Blueprint.ReeTitsModel S .twistedG2 3 (2 * m + 1) :=
    ⟨⟨Nat.prime_three, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩, m, rfl,
      GaloisField 3 (2 * m + 1), inferInstance, inferInstance, hK, ⟨e.trans b.symm⟩⟩
  exact ⟨.twistedG2, 0, 2 * m + 1, hR.1, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))⟩

theorem cat_lieModel_odd
    (d : TauCeti.ValidLieTypeIndex) (hp : d.1.characteristic ≠ 2)
    {S : Type} [Group S] (e : S ≃* d.Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n d.1.characteristic f ∧
      CFSG.Blueprint.LieModel S t n d.1.characteristic f := by
  obtain ⟨d, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q => rw [LieTypeIndex.characteristic_A]; exact cat_lm_A r q hv e
  | twistedA r q =>
    rw [LieTypeIndex.characteristic_twistedA]; exact cat_lm_twistedA r q hv e
  | B r q => rw [LieTypeIndex.characteristic_B]; exact cat_lm_B r q hv e
  | C r q => rw [LieTypeIndex.characteristic_C]; exact cat_lm_C r q hv e
  | D r q => rw [LieTypeIndex.characteristic_D]; exact cat_lm_D r q hv e
  | twistedD r q =>
    rw [LieTypeIndex.characteristic_twistedD]; exact cat_lm_twistedD r q hv e
  | E6 q => rw [LieTypeIndex.characteristic_E6] at hp ⊢; exact cat_lm_E6 q hv hp e
  | E7 q => rw [LieTypeIndex.characteristic_E7] at hp ⊢; exact cat_lm_E7 q hv hp e
  | E8 q => rw [LieTypeIndex.characteristic_E8] at hp ⊢; exact cat_lm_E8 q hv hp e
  | F4 q => rw [LieTypeIndex.characteristic_F4] at hp ⊢; exact cat_lm_F4 q hv hp e
  | G2 q => rw [LieTypeIndex.characteristic_G2] at hp ⊢; exact cat_lm_G2 q hv hp hr e
  | twistedE6 q =>
    rw [LieTypeIndex.characteristic_twistedE6] at hp ⊢; exact cat_lm_twistedE6 q hv hp e
  | trialityD4 q =>
    rw [LieTypeIndex.characteristic_trialityD4] at hp ⊢; exact cat_lm_trialityD4 q hv hp e
  | suzuki m => rw [LieTypeIndex.characteristic_suzuki] at hp; exact absurd rfl hp
  | reeG2 m =>
    rw [LieTypeIndex.characteristic_reeG2] at hp ⊢; exact cat_lm_reeG2 m hv hr e
  | reeF4 m => rw [LieTypeIndex.characteristic_reeF4] at hp; exact absurd rfl hp
  | tits => rw [LieTypeIndex.characteristic_tits] at hp; exact absurd rfl hp

end OddModels2

open CFSG.ComponentClassification.CatLeaf in
private theorem cat_prime_dvd_M22
    {p : ℕ} (hp : p.Prime) (h : p ∣ 443520) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  rw [show (443520 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h11
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
      · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
            (hp.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h11))))

open CFSG.ComponentClassification.CatLeaf in
private theorem cat_lieModel_odd_card_ne_M22
    (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hadm : StatedLieAdmissible t n p f)
    (hX : CFSG.Blueprint.LieModel X t n p f) : Nat.card X ≠ 443520 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 443520 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 443520 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases cat_prime_dvd_M22 hp hpd with rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hp3 rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

private theorem cat_hO
    : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput :=
  CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

private theorem cat_not_alt6_odd
    (d : TauCeti.ValidLieTypeIndex) (hp : d.1.characteristic ≠ 2)
    (hq3 : d.1.characteristic ≠ 3) (e : alternatingGroup (Fin 6) ≃* d.Group) : False := by
  obtain ⟨t, n, f, hadm, hm⟩ := cat_lieModel_odd d hp e
  have h := CFSG.ComponentClassification.CatLeafProof.lieModel_of_card_360 hadm hp hm cat_card_alt_six
  exact hq3 h.2.2.1

private theorem cat_not_alt7_odd
    (d : TauCeti.ValidLieTypeIndex) (hp : d.1.characteristic ≠ 2)
    (e : alternatingGroup (Fin 7) ≃* d.Group) : False := by
  obtain ⟨t, n, f, hadm, hm⟩ := cat_lieModel_odd d hp e
  exact CFSG.ClassicalInvolution.Hat2A7E5.lieModel_odd_card_ne_A7 cat_hO hp hadm hm cat_card_alt_seven

private theorem cat_not_M22_odd
    (d : TauCeti.ValidLieTypeIndex) (hp : d.1.characteristic ≠ 2)
    (hq3 : d.1.characteristic ≠ 3) (e : TauCeti.SporadicName.M22.Group ≃* d.Group) : False := by
  obtain ⟨t, n, f, hadm, hm⟩ := cat_lieModel_odd d hp e
  exact cat_lieModel_odd_card_ne_M22 cat_hO hp hq3 hadm hm cat_card_m22

private theorem cat_not_L2_odd
    (d : TauCeti.ValidLieTypeIndex) (hp : d.1.characteristic ≠ 2)
    {S : Type} [Group S] (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n)
    (e' : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (e : S ≃* d.Group) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, m, f, hadm, hm⟩ := cat_lieModel_odd d hp e
  have hodd : CFSG.Blueprint.OddLieType S :=
    ⟨t, m, d.1.characteristic, f, hadm.1, hp, hadm, hm⟩
  have h5 : 5 ≤ 2 ^ n := by
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hL : CFSG.Blueprint.LieModel S .PSL 2 2 n :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (t := .PSL) (by decide)
      (CFSG.Models.lieModel_of_statedClassicalModel
        (CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv S 2 n h5 e'))
  exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two cat_hO hL
    (by rintro ⟨-, -, h⟩; obtain ⟨k, hk⟩ := hn; omega)
    (by rintro ⟨-, h, -⟩; omega)
    (by rintro ⟨h, -, -⟩; exact absurd h (by decide)) hodd

private theorem cat_amb_lie_false
    {q : ℕ} (hq2 : q ≠ 2) (hq3 : q ≠ 3) (d : TauCeti.ValidLieTypeIndex)
    (h : ambiguousChev q (TauCeti.CFSGIndex.lie d)) : False := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q' =>
    match r, hv, h with
    | 1, _, h =>
      rcases h with ⟨-, h⟩ | ⟨-, h⟩
      · exact hq2 h
      · exact hq3 h
    | 0, _, h => exact (show False from h).elim
    | n + 2, _, h => exact (show False from h).elim
  | twistedA r q' =>
    match r, hv, h with
    | 2, _, h => exact hq2 h.2
    | 3, _, h => exact hq3 h.2
    | 0, _, h => exact (show False from h).elim
    | 1, _, h => exact (show False from h).elim
    | n + 4, _, h => exact (show False from h).elim
  | _ => exact (show False from h).elim

private theorem cat_card_psl_two_char2
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.RankThree.PartTwo.KFacts.card_psl_mul_gcd (K := GaloisField 2 n) (n := 2)
    (by norm_num)
  rw [GaloisField.card _ _ (by omega)] at h
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hg : Nat.gcd (2 ^ n - 1) 2 = 1 := by
    rw [Nat.gcd_comm]
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_
    have hd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  rw [hg] at h
  simpa [Finset.Icc_self] using h.trans (by norm_num)

private theorem cat_card_alt_five
    : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem cat_not_chev
    {q : ℕ} (hq2 : q ≠ 2) (hq3 : q ≠ 3) {S : Type} [Group S] [Finite S]
    (hbad : Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (S ≃* TauCeti.SporadicName.M22.Group) ∨
      ∃ n : ℕ, Odd n ∧ 3 ≤ n ∧
        Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))) :
    ¬ IsChevSimple q S := by
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | cyclic p hp => exact absurd hi (by simp [onLie])
    | alternating n h => exact absurd hi (by simp [onLie])
    | sporadic s => exact absurd hi (by simp [onLie])
    | lie d =>
      have hp : d.1.characteristic ≠ 2 := by
        simp only [onLie] at hi
        rw [hi]
        exact hq2
      have hq3' : d.1.characteristic ≠ 3 := by
        simp only [onLie] at hi
        rw [hi]
        exact hq3
      rcases hbad with h6 | h7 | hM | ⟨n, hn, hn3, ⟨eL⟩⟩
      · obtain ⟨e6⟩ := h6
        exact cat_not_alt6_odd d hp hq3' (e6.symm.trans e)
      · obtain ⟨e7⟩ := h7
        exact cat_not_alt7_odd d hp (e7.symm.trans e)
      · obtain ⟨eM⟩ := hM
        exact cat_not_M22_odd d hp hq3' (eM.symm.trans e)
      · exact cat_not_L2_odd d hp n hn hn3 eL e
  · cases i with
    | cyclic p hp => exact absurd hi (by simp [ambiguousChev])
    | alternating n h =>
      have h5 : n = 5 ∧ q = 5 := by
        simp only [ambiguousChev] at hi
        omega
      obtain ⟨rfl, rfl⟩ := h5
      have hc : Nat.card S = 60 := (Nat.card_congr e.toEquiv).trans cat_card_alt_five
      rcases hbad with h6 | h7 | hM | ⟨n, hn, hn3, ⟨eL⟩⟩
      · obtain ⟨e6⟩ := h6
        have h6' := (Nat.card_congr e6.toEquiv).trans cat_card_alt_six
        omega
      · obtain ⟨e7⟩ := h7
        have h7' := (Nat.card_congr e7.toEquiv).trans cat_card_alt_seven
        omega
      · obtain ⟨eM⟩ := hM
        have hM' := (Nat.card_congr eM.toEquiv).trans cat_card_m22
        omega
      · have hL := (Nat.card_congr eL.toEquiv).trans (cat_card_psl_two_char2 n (by omega))
        have h8 : 8 ≤ 2 ^ n := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
        have hbig : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
          apply Nat.mul_le_mul h8
          have : 64 ≤ (2 ^ n) ^ 2 := by
            calc 64 = 8 ^ 2 := by norm_num
              _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h8 2
          omega
        omega
    | sporadic s => exact absurd hi (by simp [ambiguousChev])
    | lie d => exact cat_amb_lie_false hq2 hq3 d hi

variable {G : Type} [Group G] [Finite G]

private theorem cat_twoLocalRank_le
    {X B : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hB : IsElemAbelian p B)
    (hW : ∀ W U : Subgroup G, W ≤ X → IsElemAbelian p W → U ≤ X → U ≠ ⊥ → IsPGroup 2 U →
      W ≤ Subgroup.normalizer (U : Set G) → Nat.card W ≤ Nat.card B) :
    GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hB
  have hBm : m ≤ CFSG.Open.pRank p B := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB hm
  refine le_trans ?_ hBm
  unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
  refine csSup_le' ?_
  rintro k ⟨H, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E hEH hE
  have hPG1 : P.map X.subtype ≠ ⊥ := fun h =>
    hP1 ((Subgroup.map_eq_bot_iff_of_injective P X.subtype_injective).1 h)
  have hPG2 : IsPGroup 2 (P.map X.subtype) := hP2.map X.subtype
  have hle := Subgroup.le_normalizer_map (H := P) X.subtype
  have hE' : IsElemAbelian p (E.map X.subtype) := CFSG.SectionRank.isElemAbelian_map hE X.subtype
  have hcard : Nat.card ↥(E.map X.subtype) = Nat.card ↥E :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hEX : E.map X.subtype ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hPX : P.map X.subtype ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hEN : E.map X.subtype ≤ Subgroup.normalizer ((P.map X.subtype : Subgroup G) : Set G) :=
    (Subgroup.map_mono hEH).trans hle
  have hb := hW (E.map X.subtype) (P.map X.subtype) hEX hE' hPX hPG1 hPG2 hEN
  rw [hcard, hm] at hb
  exact hb

private theorem cat_sl3_index
    {X : Type} [Group X] (h : IsSLThreeExc X) :
    ∃ (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 Q).Valid),
      Nonempty (X ⧸ Subgroup.center X ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 2 Q, hv⟩) := by
  obtain ⟨F, hF, hfin, h9, ⟨e⟩⟩ := h
  have h3 : 3 ∣ Nat.card F - 1 := by omega
  obtain ⟨q, _, hqc, ⟨φ⟩⟩ := exists_primePower_card_eq F
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hqc]
    omega
  refine ⟨q, hv, ⟨?_⟩⟩
  let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  exact ((QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
    (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) φ)).trans
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm

private theorem cat_su3_index
    {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    (h : IsSUThreeExc X) :
    ∃ (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid),
      Nonempty (X ⧸ Subgroup.center X ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 Q, hv⟩) := by
  obtain ⟨F, hF, hfin, q, hFq, hq9, ⟨e⟩⟩ := h
  have hq2 := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hFq
  have h3 : 3 ∣ q + 1 := by omega
  have hq3 : 3 ≤ q := by
    by_contra hlt
    obtain rfl : q = 2 := by omega
    have hs : Group.IsSolvable (StatedSU 3 (2 ^ 1) F) :=
      CFSG.Quasithin.isSolvable_statedSU_one (by simpa using hFq)
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hX
      (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  obtain ⟨Q, _, hQc, ⟨φ⟩⟩ := exists_primePower_sq_card_eq F hFq hq2
  have hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    have hq3Q : 3 ≤ Q.card := by
      rw [hQc]
      exact hq3
    exact ⟨⟨le_rfl, fun _ => hq3Q⟩, fun h => h⟩
  refine ⟨Q, hv, ?_⟩
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 2 Q, hv⟩ = Q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 Q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 2 Q, hv⟩ =
      Q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 Q
  haveI : Fact (TauCeti.ValidLieTypeIndex.characteristic
      ⟨TauCeti.LieTypeIndex.twistedA 2 Q, hv⟩).Prime :=
    ⟨TauCeti.ValidLieTypeIndex.characteristic_prime _⟩
  set c := TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 2 Q, hv⟩ with hcdef
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 2 Q, hv⟩ with hfdef
  have hf0 : 0 < f := by
    rw [hf]
    exact Q.exponent_pos
  have hKc : Nat.card (GaloisField c (2 * f)) = c ^ (2 * f) :=
    GaloisField.card _ _ (by omega)
  have hcq : c ^ f = q := by
    rw [hc, hf, ← TauCeti.PrimePower.card_def, hQc]
  have hcard : Nat.card F = Nat.card (GaloisField c (2 * f)) := by
    rw [hKc, hFq, ← hcq, ← pow_mul, mul_comm]
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite (GaloisField c (2 * f))
  have φ' : F ≃+* GaloisField c (2 * f) :=
    FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard)
  have e₃ : X ≃* StatedSU 3 q (GaloisField c (2 * f)) :=
    e.trans (CFSG.Open.StatedSUFieldChange.statedSUEquiv φ' 3 q)
  have e₄ : X ≃* StatedSU 3 (c ^ f) (GaloisField c (2 * f)) := by
    rw [hcq]
    exact e₃
  have hF' : Nat.card (GaloisField c (2 * f)) = (c ^ f) ^ 2 := by
    rw [hKc, ← pow_mul, mul_comm]
  have h3' : 3 ∣ c ^ f + 1 := by
    rw [hcq]
    exact h3
  exact ⟨((QuotientGroup.congr _ _ e₄ (Subgroup.map_center_eq e₄)).trans
    (QuotientGroup.quotientMulEquivOfEq (center_statedSU_three_eq hF' h3'))).trans
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 Q hv).symm⟩

theorem i112ChevAt_holds
    (G : Type) [Group G] [Finite G] (p : ℕ) : I112ChevAt G p := by
  intro hp hp2 q hq hq2 hqp X B K L₁ J x hX hBX hB hBmax hL₁ hK hxB hxn hJ hchev
  have hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B := cat_twoLocalRank_le hp hB hBmax
  have hnL : ¬ B ≤ Subgroup.normalizer (L₁ : Set G) := fun h => hxn (h hxB)
  obtain ⟨hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ := cat_bar hX hp hp2 hB hBX hr hL₁ hnL
  obtain ⟨h3, -, -, -, -, hcase⟩ := i112v_core tables112_holds tableL2_unconditional
    tables112Types_holds tables112More_holds hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  subst h3
  have hK' : K = bClosure B L₁ := hK
  subst hK'
  obtain ⟨hcomp, ⟨eM⟩, hsimpQ⟩ := cat_layer_G tables112_holds tableL2_unconditional
    tables112Types_holds tables112More_holds hX hB hBX hr hL₁ hnL hxB hxn
  have hJeq : J = GLAPLayer 3 (bClosure B L₁ ⊓ Subgroup.centralizer ({x} : Set G)) :=
    Lemma53Ns.glaPComponent_eq_of_le Nat.prime_three hJ hcomp (le_sSup hJ)
  subst hJeq
  have hQsimp := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hcomp
  set M := GLAPLayer 3 (bClosure B L₁ ⊓ Subgroup.centralizer ({x} : Set G)) with hMdef
  have hcen : Subgroup.center (PQuot 3 M) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PQuot 3 M)) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (PQuot 3 M ⧸ Subgroup.center (PQuot 3 M)) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      haveI := hQsimp.2.toNontrivial
      exact not_subsingleton _ hsub
  refine ⟨rfl, hcen, ?_⟩
  have eS : PSimple 3 M ≃* PQuot 3 M :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have eSL : PSimple 3 M ≃* (↥(barX 3 X L₁) ⧸ Subgroup.center ↥(barX 3 X L₁)) := eS.trans eM
  rcases hcase with ⟨h1, -, -, hiso⟩ | ⟨h3', htypes, -⟩
  · have hcenL : Subgroup.center ↥(barX 3 X L₁) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have eZ : ↥(barX 3 X L₁) ⧸ Subgroup.center ↥(barX 3 X L₁) ≃* ↥(barX 3 X L₁) :=
      (QuotientGroup.quotientMulEquivOfEq hcenL).trans QuotientGroup.quotientBot
    obtain ⟨n, hn, hn1, ⟨eL⟩⟩ := isL2TwoPowOdd_of_isLTwoOddPow hiso
    have hn3 : 3 ≤ n := by
      obtain ⟨k, hk⟩ := hn
      omega
    exact absurd hchev (cat_not_chev hq2 hqp
      (Or.inr (Or.inr (Or.inr ⟨n, hn, hn3, ⟨eSL.trans (eZ.trans eL)⟩⟩))))
  · rcases htypes with h6 | h7 | hMM | hSL | hSU
    · obtain ⟨-, -, ⟨e6⟩⟩ := h6
      exact absurd hchev (cat_not_chev hq2 hqp (Or.inl ⟨eSL.trans e6⟩))
    · obtain ⟨-, -, ⟨e7⟩⟩ := h7
      exact absurd hchev (cat_not_chev hq2 hqp (Or.inr (Or.inl ⟨eSL.trans e7⟩)))
    · obtain ⟨-, -, ⟨eMM⟩⟩ := hMM
      exact absurd hchev (cat_not_chev hq2 hqp (Or.inr (Or.inr (Or.inl ⟨eSL.trans eMM⟩))))
    · obtain ⟨Q, hv, ⟨eQ⟩⟩ := cat_sl3_index hSL
      exact ⟨Q, Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩, rfl, ⟨eSL.trans eQ⟩⟩⟩
    · obtain ⟨Q, hv, ⟨eQ⟩⟩ := cat_su3_index (i116e_isQuasisimple hQcore hLbar) hSU
      exact ⟨Q, Or.inr ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 Q, hv⟩, rfl, ⟨eSL.trans eQ⟩⟩⟩

end Tables

end CFSG.LocalAnalysis.GLTheoremA
