module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairClassSizeIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairClassSizeExclusion

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

universe u

variable {G : Type u} [Group G] [Finite G]

theorem exists_mem_rightPairFlipFiber {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) : ∃ t, t ∈ rightPairFlipFiber H z beta := by
  obtain ⟨hcard, -, -⟩ := involution_point_uniform_pair_flips h beta hbeta
  have hz : z ∈ conjugacyWithin H z := ⟨1, by simp⟩
  have : Nonempty (conjugacyWithin H z) := ⟨⟨z, hz⟩⟩
  have hpos : 0 < Nat.card (rightPairFlipFiber H z beta) := hcard ▸ Nat.card_pos
  obtain ⟨⟨t, ht⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨t, ht⟩

theorem highRankPair_class_size_nine_or_twenty_seven
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    (hW : HighRankPairWitnessTheorem G) (hNC : NoncentralPairActionTheorem G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (hrank : 2 ≤ twoRank (pairPointStabilizer H beta)) :
    Nat.card (conjugacyWithin H z) = 9 ∨ Nat.card (conjugacyWithin H z) = 27 := by
  obtain ⟨t, ht⟩ := exists_mem_rightPairFlipFiber h.local_datum hbeta
  obtain ⟨-, u, v, a, ε, ha, hε, -, -, -, hu, hv, -, hcuv, -, -, hut, hvt, -, -, -, -,
    -, -, -, hm, -, -, s, r, hsr, hs, hprime, hγ⟩ := hW H z h beta hbeta t ht hrank
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · obtain rfl : a = 1 := by omega
    rcases hε with rfl | rfl
    · left
      rw [hm]
      norm_num
    · right
      rw [hm]
      norm_num
  exfalso
  have hz := h.local_datum.distinguished_order
  have htD : t ∈ involutionPointClass z := ht.1
  have htord : orderOf t = 2 := order_two_of_mem_pointClass hz htD
  have ht2 : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp htord).1
  have hq4 : 4 ≤ 2 ^ a :=
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
  have hqeven : Even (2 ^ a) := (Nat.even_pow' (by omega)).mpr even_two
  obtain ⟨p, hp, hp2, hpq, hb⟩ :=
    CFSG.UnitaryInvolutionIndex.exists_odd_prime_dvd_succ_three_lt hqeven hq4
  obtain ⟨A, -, -, -, htA, hAp, -, -, hidx, -, -, -, hAL⟩ := hprime p hp hp2 hpq
  generalize hbdef : p ^ (2 ^ a + 1).factorization p = b at hb hidx
  have hidx' : (A ⊓ Subgroup.centralizer {t}).relIndex A = b ^ 2 := hidx
  have hb1 : b < b ^ 2 := by nlinarith
  have hb3 : 3 * b < b ^ 2 := by nlinarith
  obtain ⟨hst, hsr', hrt, hr⟩ : Commute s t ∧ Commute s r ∧ Commute r t ∧ orderOf r = 2 := by
    rcases hsr with ⟨-, hs', hr'⟩ | ⟨-, hs', hr'⟩
    · rw [hs', hr']
      exact ⟨(hut.mul_left hvt).mul_left (Commute.refl t),
        ((Commute.refl u).mul_left hcuv.symm).mul_left hut.symm, hut, hu⟩
    · rw [hs', hr']
      exact ⟨hut.mul_left (Commute.refl t), hcuv.mul_left hvt.symm, hvt, hv⟩
  obtain ⟨γ, hγfix, -⟩ := ((involution_point_unique_containment_action
    h.local_datum.distinguished_mem hz).2 h.local_datum.unique_containment).2.1 t htD
  have hγfix' : rightCosetTranslate H γ t = γ := by
    rw [← pointRightCosetMul_eq_translate]
    exact hγfix
  obtain ⟨hesc, -, hsub, hX, hrank2⟩ := hγ γ hγfix'
  obtain ⟨h', hclass, -, hfixC⟩ := minimalLocalFailure_fixed_point_transport h htD hγfix'
  set M := rightCosetStabilizer H γ
  have hsM : s ∈ M := hfixC s hst
  have hrM : r ∈ M := hfixC r hrt
  have hLeq : localInvolutionPointHull t s = localInvolutionPointHull z s := by
    rw [localInvolutionPointHull, localInvolutionPointHull, hclass]
  have hAL' : A ≤ localInvolutionPointHull t s := hLeq ▸ hAL
  have htL : t ∈ localInvolutionPointHull t s :=
    mem_localInvolutionPointHull (distinguished_mem_pointClass t) hst.symm
  have hroots : pointRoots M t s =
      involutionPointClass t ∩ (M : Set G) ∩ (Subgroup.centralizer ({s} : Set G) : Set G) :=
    pointRoots_eq_of_localDatum h'.local_datum s
  have hXeq : involutionPointClass t ∩ (M : Set G) ∩
      (Subgroup.centralizer ({s} : Set G) : Set G) ∩
      (Subgroup.centralizer ({r} : Set G) : Set G) =
      involutionPointClass z ∩ (M : Set G) ∩ (Subgroup.centralizer ({r} : Set G) : Set G) ∩
        (Subgroup.centralizer ({s} : Set G) : Set G) := by
    rw [hclass, Set.inter_right_comm]
  have hhull := minimalLocalFailure_arbitrary_involution_centralizer_hull h' hcomm hR1 hsM hs
    hst hesc
  dsimp only at hhull
  obtain ⟨-, -, -, -, -, -, -, hxor⟩ := hhull
  have hrankL : 2 ≤ twoRank (localInvolutionPointHull t s) := by
    rw [hLeq]
    exact hrank2 hq4
  obtain ⟨-, U, hU, -, -, -, -, -, hRL, hmodel, -⟩ := hxor.or.resolve_left fun h1 => by
    omega
  have hcore : CFSG.oddCore (localInvolutionPointHull t s) ≤
      Subgroup.center (localInvolutionPointHull t s) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hRL (Subgroup.mem_map_of_mem _ hx)).2
    rw [← (localInvolutionPointHull t s).subtype_injective hyx]
    exact hy
  by_cases hmove : ∃ x ∈ pointRoots M t s, ¬ Commute r x
  ·
    obtain ⟨k, hk, hkcard, ⟨ψ⟩⟩ := hsub
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hkcard]; positivity)
    have htK : t ∈ localInvolutionPointHull z r ⊓ Subgroup.centralizer ({s} : Set G) :=
      ⟨mem_localInvolutionPointHull htD hrt.symm,
        Subgroup.mem_centralizer_singleton_iff.mpr hst.eq.symm⟩
    obtain ⟨j, hjD, hjr, hjs, hjM⟩ := exists_class_mem_not_mem_of_card_le hkcard ψ htK htD
      htord (inf_le_left.trans (localInvolutionPointHull_le_centralizer z r)) inf_le_right
      hX.le
    obtain ⟨a', -, ⟨F, hF, hFcard, φ, -⟩, -, -, hcount⟩ :=
      squareFieldAction_of_flip hNC h' (hclass ▸ hjD) hjM hsM hrM hs hr hst hjs.symm hjr.symm
        hsr' hmove
    have : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; positivity)
    have hcount' : 2 ^ a' - 1 = 2 ^ a - 1 := by
      rw [← hcount, hroots, hXeq]
      exact hX
    have ha' : a' = a := by
      have h2 : 2 ^ a' = 2 ^ a :=
        calc 2 ^ a' = 2 ^ a' - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
          _ = 2 ^ a - 1 + 1 := by rw [hcount']
          _ = 2 ^ a := Nat.sub_add_cancel Nat.one_le_two_pow
      exact Nat.pow_right_injective le_rfl h2
    subst ha'
    have hFq : Nat.card F = (2 ^ a') ^ 2 := by rw [hFcard, ← pow_mul, mul_comm]
    have hle := relIndex_centralizer_le_of_mulEquiv_specialLinearGroup hAL' hp hp2 hpq hAp
      (Or.inr hFq) φ htL
    rw [hidx', hbdef] at hle
    exact absurd hle (not_le.mpr hb1)
  ·
    push Not at hmove
    have hE : involutionPointClass t ∩ (M : Set G) ∩
        (Subgroup.centralizer ({s} : Set G) : Set G) =
        involutionPointClass z ∩ (M : Set G) ∩ (Subgroup.centralizer ({r} : Set G) : Set G) ∩
          (Subgroup.centralizer ({s} : Set G) : Set G) := by
      rw [← hXeq]
      ext x
      constructor
      · intro hx
        refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← hroots] at hx
        exact (hmove x hx).symm
      · exact fun hx => hx.1
    have hUq : Nat.card U = 2 ^ a := by
      have h1 : (1 : G) ∉ involutionPointClass t ∩ (M : Set G) ∩
          (Subgroup.centralizer ({s} : Set G) : Set G) := fun h1 =>
        one_not_mem_pointClass (order_two_of_mem_pointClass hz htD) h1.1.1
      rw [card_eq_card_add_one_of_coe_eq hU h1, hE, hX]
      exact Nat.sub_add_cancel Nat.one_le_two_pow
    rcases hmodel with ⟨-, f, hf, hUf, E, -⟩ | ⟨-, m, hm1, hUm, E, -⟩ |
      ⟨-, f, -, hUf, K, hK, hKfin, J, -, hKcard, hfix, -, -, E, -⟩
    ·
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hKq : Nat.card (CFSG.BenderSuzuki.PFAppendixIII.BinaryGaloisField f) = 2 ^ a := by
        rw [← hUq, hUf]
        exact GaloisField.card 2 f (by omega)
      have hle := relIndex_centralizer_le_of_quotient_psl2 hAL' hp hp2 hpq hAp _ hcore hKq E htL
      rw [hidx', hbdef] at hle
      exact absurd hle (not_le.mpr hb1)
    ·
      rw [hUq] at hUm
      have hpq' : p ∣ 2 ^ (2 * m + 1) + 1 := hUm ▸ hpq
      have h1 := relIndex_centralizer_eq_one_of_quotient_suzuki hAL' hp hp2 hm1 hpq' hAp _ hcore
        E htL
      rw [hidx'] at h1
      exact absurd h1 (by nlinarith)
    ·
      rw [hUq] at hKcard hfix
      have hqpp : IsPrimePow (2 ^ a) := Nat.prime_two.isPrimePow.pow (by omega)
      have hle := relIndex_centralizer_le_of_quotient_unitary hAL' hqpp hp hp2 hpq hAp _ hcore
        (CFSG.ComponentClassification.OddCore.odd_card _) J hKcard hfix E htL ht2 htA
      rw [hidx', hbdef] at hle
      exact absurd hle (not_le.mpr hb3)

end CFSG.ProperTwoGeneratedCore.HighRankPair
