module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryRank
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsFull
public import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer
public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockCharTwo
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticSixLayer
public import CFSG.GH74.EvenRank
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.LargeEvenClassification.Helpers (pGeneratorRank pGeneratorRank_le_generators)
open CFSG.LocalAnalysis.ComponentInitial (isCharacteristicP_of_mulEquiv
  not_isComponent_of_isCharacteristicP_two centralizer_singleton_eq_normalizer_zpowers)

variable {G : Type*} [Group G]

theorem pow_le_card_frattini_twoCore [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hchar : CFSG.Open.IsCharTwoType G) {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H) :
    2 ^ (orderOf (2 : ZMod p) * CFSG.Open.pRank p H) ≤
      Nat.card (pCoreOf 2 H ⧸ frattini (pCoreOf 2 H)) := by
  let : IsMulCommutative (pCoreOf 2 H ⧸ frattini (pCoreOf 2 H)) :=
    CFSG.PreuniquenessRankFour.Helpers.pGroup_frattini_quotient_isMulCommutative 2
      (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H)
  let : CommGroup (pCoreOf 2 H ⧸ frattini (pCoreOf 2 H)) := IsMulCommutative.instCommGroup
  let := CFSG.PreuniquenessRankFour.Helpers.pGroup_binary_frattini_quotient_module
    (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H)
  have hdim := CFSG.PreuniquenessRankFour.Helpers.local_twoCore_frattini_order_dimension_bound
    p hp hp2 hchar H hH
  have hcard : Nat.card (pCoreOf 2 H ⧸ frattini (pCoreOf 2 H)) =
      2 ^ Module.finrank (ZMod 2) (Additive (pCoreOf 2 H ⧸ frattini (pCoreOf 2 H))) := by
    rw [Nat.card_congr (Additive.ofMul :
      (pCoreOf 2 H ⧸ frattini (pCoreOf 2 H)) ≃ Additive (pCoreOf 2 H ⧸ frattini (pCoreOf 2 H))),
      Module.natCard_eq_pow_finrank (K := ZMod 2)]
    congr 1
    exact (Nat.card_eq_fintype_card.trans (ZMod.card 2))
  rw [hcard]
  exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) hdim

theorem inSubgroup_pCore_eq_pCoreOf (H : Subgroup G) :
    CFSG.inSubgroup (CFSG.pCore 2) H = pCoreOf 2 H := by
  rw [CFSG.inSubgroup]
  rfl

theorem twoCore_frattini_rank_and_eight
    [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hchar : CFSG.Open.IsCharTwoType G) {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H)
    {B : Subgroup G} (hBH : B ≤ H) (hB : IsElemAbelian p B) {r : ℕ} (hBr : Nat.card B = p ^ r) :
    (∃ d : ℕ, Nat.card (CFSG.inSubgroup (CFSG.pCore 2) H ⧸
        frattini (CFSG.inSubgroup (CFSG.pCore 2) H)) = 2 ^ d ∧ orderOf (2 : ZMod p) * r ≤ d) ∧
      (5 ≤ orderOf (2 : ZMod p) * r → ∃ A : Subgroup (CFSG.inSubgroup (CFSG.pCore 2) H),
        A.Normal ∧ IsElemAbelian 2 A ∧ Nat.card A = 8) := by
  rw [inSubgroup_pCore_eq_pCoreOf]
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H
  have hrank : r ≤ CFSG.Open.pRank p H := CFSG.SectionRank.le_pRank hp.one_lt hBH hB hBr
  have hle := pow_le_card_frattini_twoCore hp hp2 hchar hH
  have hd := SymplecticSixLayer.card_frattini_quotient_eq_pow Nat.prime_two hQ2
  have hfr : orderOf (2 : ZMod p) * r ≤ pGeneratorRank 2 (pCoreOf 2 H) := by
    rw [hd] at hle
    exact (Nat.mul_le_mul_left _ hrank).trans ((Nat.pow_le_pow_iff_right (by norm_num)).mp hle)
  refine ⟨⟨_, hd, hfr⟩, fun h5 => ?_⟩
  by_contra hno
  have hnoEight : ∀ E : Subgroup (pCoreOf 2 H), E.Normal → IsElemAbelian 2 E → Nat.card E ≠ 8 :=
    fun E hE hEel hE8 => hno ⟨E, hE, hEel, hE8⟩
  obtain ⟨X, hX4, hX⟩ :=
    CFSG.LargeEvenClassification.Helpers.macwilliams_four_generators hQ2 hnoEight ⊤
  have h1 := pGeneratorRank_le_generators Nat.prime_two hQ2 X hX
  omega

theorem involution_centralizer_core_and_components [Finite G]
    (hchar : CFSG.IsCharacteristicPType G 2) {x : G} (hx : orderOf x = 2) :
    CFSG.IsCharacteristicP 2 (centralizer ({x} : Set G)) ∧
      CFSG.pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ ∧
      ∀ K : Subgroup (centralizer ({x} : Set G)), ¬ CFSG.IsComponent K := by
  have := Fact.mk Nat.prime_two
  have hloc : CFSG.IsPLocal 2 (centralizer ({x} : Set G)) := by
    refine ⟨zpowers x, ?_, ?_, centralizer_singleton_eq_normalizer_zpowers hx⟩
    · intro h
      rw [zpowers_eq_bot] at h
      rw [h, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx, pow_one]
  have hC := hchar _ hloc
  exact ⟨hC, CFSG.pPrimeCore_eq_bot_of_isCharacteristicP _ 2 hC,
    not_isComponent_of_isCharacteristicP_two hC⟩

theorem large_local_rank_core_and_component_reduction
    [Finite G]
    (hchar : CFSG.IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G) :
    3 ≤ CFSG.pRank 2 G ∧ ¬ CFSG.Assembly.IsComponentType G ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (B : Subgroup G) (r : ℕ), IsElemAbelian p B →
        Nat.card B = p ^ r → 3 ≤ r → ∀ T : Subgroup G, T ≠ ⊥ → IsPGroup 2 T →
          B ≤ normalizer (T : Set G) →
          (∃ d : ℕ, Nat.card (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)) ⧸
              frattini (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)))) = 2 ^ d ∧
            orderOf (2 : ZMod p) * r ≤ d) ∧
          6 ≤ orderOf (2 : ZMod p) * r ∧
          ∃ A : Subgroup (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G))),
            A.Normal ∧ IsElemAbelian 2 A ∧ Nat.card A = 8) ∧
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ (B : Subgroup G) (r : ℕ), IsElemAbelian p B ∧
        Nat.card B = p ^ r ∧ 3 ≤ r ∧ ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧
          B ≤ normalizer (T : Set G)) ∧
      (∀ p ∈ GLABeta 4 G, ∀ B : Subgroup G, GLAIsBmax p B → ∀ T : Subgroup G, T ≠ ⊥ →
        IsPGroup 2 T → B ≤ normalizer (T : Set G) →
          (∃ d : ℕ, Nat.card (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)) ⧸
              frattini (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)))) = 2 ^ d ∧
            orderOf (2 : ZMod p) * GLATwoLocalRank p G ≤ d) ∧
          8 ≤ orderOf (2 : ZMod p) * GLATwoLocalRank p G) ∧
      ∀ x : G, orderOf x = 2 → CFSG.pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ ∧
        ∀ K : Subgroup (centralizer ({x} : Set G)), ¬ CFSG.IsComponent K := by
  have := Fact.mk Nat.prime_two
  have hchar' : CFSG.Open.IsCharTwoType G := CFSG.GH74.isCharTwoType_iff.mpr hchar
  have hlocal : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (B : Subgroup G) (r : ℕ), IsElemAbelian p B →
      Nat.card B = p ^ r → 3 ≤ r → ∀ T : Subgroup G, T ≠ ⊥ → IsPGroup 2 T →
        B ≤ normalizer (T : Set G) →
        (∃ d : ℕ, Nat.card (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)) ⧸
            frattini (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)))) = 2 ^ d ∧
          orderOf (2 : ZMod p) * r ≤ d) ∧
        6 ≤ orderOf (2 : ZMod p) * r ∧
        ∃ A : Subgroup (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G))),
          A.Normal ∧ IsElemAbelian 2 A ∧ Nat.card A = 8 := by
    intro p hp hp2 B r hB hBr hr T hT1 hT2 hBT
    have := Fact.mk hp
    have hf := CFSG.PreuniquenessRankFour.Helpers.binary_prime_order_at_least_two p hp2
    have h6 : 6 ≤ orderOf (2 : ZMod p) * r := le_trans (by norm_num) (Nat.mul_le_mul hf hr)
    obtain ⟨hd, h8⟩ :=
      twoCore_frattini_rank_and_eight hp hp2 hchar' ⟨T, hT1, hT2, rfl⟩ hBT hB hBr
    exact ⟨hd, h6, h8 (by omega)⟩
  have hbridge : ∀ (q : ℕ) (K : Subgroup G), CFSG.pRank q K = CFSG.Open.pRank q K :=
    fun q K => (CFSG.SectionRank.pRank_eq_open_pRank_top q K).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
  have htriple : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ (B : Subgroup G) (r : ℕ), IsElemAbelian p B ∧
      Nat.card B = p ^ r ∧ 3 ≤ r ∧ ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧
        B ≤ normalizer (T : Set G) := by
    have hbdd : BddAbove {r : ℕ | ∃ K : Subgroup G, CFSG.IsPLocal 2 K ∧
        ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ r = CFSG.pRank q K} := by
      refine ⟨Nat.card G, ?_⟩
      rintro _ ⟨K, -, q, hq, -, -, rfl⟩
      rw [hbridge]
      obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq.one_lt K
      have h1 : CFSG.Open.pRank q K < q ^ CFSG.Open.pRank q K := Nat.lt_pow_self hq.one_lt
      have h2 : Nat.card E ≤ Nat.card G := card_le_card_group E
      omega
    have hne : {r : ℕ | ∃ K : Subgroup G, CFSG.IsPLocal 2 K ∧
        ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ r = CFSG.pRank q K}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h0 : CFSG.twoLocalOddRank G = 0 := by
        rw [CFSG.twoLocalOddRank, h]
        exact csSup_empty
      omega
    obtain ⟨K, ⟨T, hT1, hT2, rfl⟩, p, hp, hp2, -, hrank⟩ := Nat.sSup_mem hne hbdd
    rw [hbridge] at hrank
    obtain ⟨E, hEK, hE, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt (normalizer (T : Set G))
    refine ⟨p, hp, hp2, E, _, hE, hEcard, ?_, T, hT1, hT2, hEK⟩
    have h1 : CFSG.twoLocalOddRank G = CFSG.Open.pRank p (normalizer (T : Set G)) := hrank
    omega
  have hm2 : 3 ≤ CFSG.pRank 2 G := by
    obtain ⟨p, hp, hp2, B, r, hB, hBr, hr, T, hT1, hT2, hBT⟩ := htriple
    obtain ⟨-, -, A, -, hA, hA8⟩ := hlocal p hp hp2 B r hB hBr hr T hT1 hT2 hBT
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.le_pRank_of_injective (A := A) (by norm_num)
      (fun a b => hA.1.is_comm.comm a b) (fun a => Subtype.ext (by simpa using hA.2 _ a.2))
      (hA8.trans (by norm_num))
      ((CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G))).subtype.comp A.subtype)
      ((Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)) le_top
  have hnotcomp : ¬ CFSG.Assembly.IsComponentType G := by
    rintro ⟨t, ht, L, hL⟩
    obtain ⟨hC, hcore, -⟩ := involution_centralizer_core_and_components hchar ht
    have hodd : CFSG.Assembly.oddCore (centralizer ({t} : Set G)) = ⊥ := by
      rw [CFSG.ComponentClassification.AssemblyBPredicates.oddCore_eq_native,
        CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore (centralizer ({t} : Set G)) 2, hcore]
    let e : (centralizer ({t} : Set G) ⧸ CFSG.Assembly.oddCore (centralizer ({t} : Set G))) ≃*
        centralizer ({t} : Set G) :=
      (QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot
    exact not_isComponent_of_isCharacteristicP_two (isCharacteristicP_of_mulEquiv e.symm hC) L
      ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native L).mp hL)
  have hbeta : ∀ p ∈ GLABeta 4 G, ∀ B : Subgroup G, GLAIsBmax p B → ∀ T : Subgroup G, T ≠ ⊥ →
      IsPGroup 2 T → B ≤ normalizer (T : Set G) →
        (∃ d : ℕ, Nat.card (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)) ⧸
            frattini (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)))) = 2 ^ d ∧
          orderOf (2 : ZMod p) * GLATwoLocalRank p G ≤ d) ∧
        8 ≤ orderOf (2 : ZMod p) * GLATwoLocalRank p G := by
    rintro p ⟨hp, hp2, -, h4⟩ B ⟨hB, hBcard, -⟩ T hT1 hT2 hBT
    have := Fact.mk hp
    have hf := CFSG.PreuniquenessRankFour.Helpers.binary_prime_order_at_least_two p hp2
    obtain ⟨hd, -⟩ :=
      twoCore_frattini_rank_and_eight hp hp2 hchar' ⟨T, hT1, hT2, rfl⟩ hBT hB hBcard
    exact ⟨hd, le_trans (by norm_num) (Nat.mul_le_mul hf h4)⟩
  exact ⟨hm2, hnotcomp, hlocal, htriple, hbeta,
    fun x hx => (involution_centralizer_core_and_components hchar hx).2⟩

end CFSG.LocalAnalysis.GorensteinLyons
