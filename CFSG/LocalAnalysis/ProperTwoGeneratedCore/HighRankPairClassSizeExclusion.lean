module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairClassSizeSign
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairClassSizeTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open scoped MatrixGroups

universe u

variable {G : Type u} [Group G]

theorem seventyFive_le_class_size {a ε : ℕ} (ha : 2 ≤ a) (hε : ε = 2 ∨ ε = 3) :
    75 ≤ (2 ^ a - 1) * (2 ^ a + 1) ^ ε := by
  have h4 : 4 ≤ 2 ^ a :=
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have h25 : 25 ≤ (2 ^ a + 1) ^ ε := by
    have h5 : 5 ^ 2 ≤ (2 ^ a + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rcases hε with rfl | rfl
    · exact h5
    · calc 25 = 5 ^ 2 := rfl
        _ ≤ (2 ^ a + 1) ^ 2 := h5
        _ ≤ (2 ^ a + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc 75 = 3 * 25 := rfl
    _ ≤ (2 ^ a - 1) * (2 ^ a + 1) ^ ε := Nat.mul_le_mul (by omega) h25

theorem card_eq_card_add_one_of_coe_eq [Finite G] {U : Subgroup G} {E : Set G}
    (hU : (U : Set G) = {1} ∪ E) (h1 : (1 : G) ∉ E) : Nat.card U = Nat.card E + 1 := by
  have hcard : Nat.card U = Nat.card (U : Set G) := rfl
  rw [hcard, hU, Set.singleton_union, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_insert_of_notMem h1 (Set.toFinite E)]

theorem one_not_mem_pointClass {z : G} (hz : orderOf z = 2) : (1 : G) ∉ involutionPointClass z :=
  fun h1 => by
    have := order_two_of_mem_pointClass hz h1
    rw [orderOf_one] at this
    omega

variable [Finite G]

theorem highRankPair_class_size_ne_nine_and_twenty_seven
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    (hW : HighRankPairWitnessTheorem G) (hNC : NoncentralPairActionTheorem G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : 2 ≤ twoRank (pairPointStabilizer H beta)) :
    Nat.card (conjugacyWithin H z) ≠ 9 ∧ Nat.card (conjugacyWithin H z) ≠ 27 := by
  obtain ⟨-, u, v, a, ε, ha, hε, -, huB, -, hu, hv, -, hcuv, -, -, hut, hvt, -, -, -, -,
    hDu, -, -, hm, -, -, s, r, hsr, hs, hprime, hγ⟩ := hW H z h beta hbeta t ht hrank
  have ha1 : ∀ m, m ≤ 27 → Nat.card (conjugacyWithin H z) = m → a = 1 := by
    intro m hm27 hmeq
    by_contra hne
    have := seventyFive_le_class_size (a := a) (by omega) hε
    omega
  have hz := h.local_datum.distinguished_order
  have htD : t ∈ involutionPointClass z := ht.1
  have htord : orderOf t = 2 := order_two_of_mem_pointClass hz htD
  refine ⟨fun h9 => ?_, fun h27 => ?_⟩
  ·
    obtain rfl := ha1 9 (by norm_num) h9
    have huH : u ∈ H := pairPointStabilizer_le_point H beta huB
    have hu2 : u ^ 2 = 1 := (orderOf_eq_prime_iff.mp hu).1
    have hpar := even_half_card_conjugacyWithin_moved
      (minimalLocalFailure_point_stabilizer_no_index_two_subgroup h) z huH hu2
    have hroots : conjugacyWithin H z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) =
        distinguishedRoots H z u := by
      rw [← pointRoots, pointRoots_eq_of_localDatum h.local_datum u]
      rfl
    rw [hroots, hDu, h9] at hpar
    norm_num at hpar
  · obtain rfl := ha1 27 le_rfl h27
    have hε3 : ε = 3 := by
      rcases hε with rfl | rfl
      · rw [h27] at hm
        norm_num at hm
      · rfl
    obtain ⟨rfl, rfl⟩ : s = u * t ∧ r = v := by
      rcases hsr with ⟨h2, -, -⟩ | ⟨-, hs', hr'⟩
      · omega
      · exact ⟨hs', hr'⟩
    obtain ⟨A, -, -, -, -, hA3, hAcyc, -, -, -, -, -, hAL⟩ :=
      hprime 3 Nat.prime_three (by norm_num) (by norm_num)
    obtain ⟨γ, hγfix, -⟩ := ((involution_point_unique_containment_action
      h.local_datum.distinguished_mem hz).2 h.local_datum.unique_containment).2.1 t htD
    have hγfix' : rightCosetTranslate H γ t = γ := by
      rw [← pointRightCosetMul_eq_translate]
      exact hγfix
    obtain ⟨hesc, -, hsub, hX, -⟩ := hγ γ hγfix'
    obtain ⟨h', hclass, hcard', hfixC⟩ := minimalLocalFailure_fixed_point_transport h htD hγfix'
    set M := rightCosetStabilizer H γ
    have hst : Commute (u * t) t := hut.mul_left (Commute.refl t)
    have hsr' : Commute (u * t) r := hcuv.mul_left hvt.symm
    have hsM : u * t ∈ M := hfixC _ hst
    have hrM : r ∈ M := hfixC r hvt
    have hs2 : (u * t) ^ 2 = 1 := (orderOf_eq_prime_iff.mp hs).1
    have hroots : pointRoots M t (u * t) =
        involutionPointClass t ∩ (M : Set G) ∩
          (Subgroup.centralizer ({u * t} : Set G) : Set G) :=
      pointRoots_eq_of_localDatum h'.local_datum (u * t)
    have hXeq : involutionPointClass t ∩ (M : Set G) ∩
        (Subgroup.centralizer ({u * t} : Set G) : Set G) ∩
        (Subgroup.centralizer ({r} : Set G) : Set G) =
        involutionPointClass z ∩ (M : Set G) ∩ (Subgroup.centralizer ({r} : Set G) : Set G) ∩
          (Subgroup.centralizer ({u * t} : Set G) : Set G) := by
      rw [hclass, Set.inter_right_comm]
    have hhull := minimalLocalFailure_arbitrary_involution_centralizer_hull h' hcomm hR1 hsM hs
      hst hesc
    dsimp only at hhull
    obtain ⟨-, -, -, -, -, -, -, hxor⟩ := hhull
    rcases hxor.or with ⟨-, hone, -⟩ | ⟨-, U, hU, -, hU4, -⟩
    ·
      have hpar := even_half_card_conjugacyWithin_moved
        (minimalLocalFailure_point_stabilizer_no_index_two_subgroup h') t hsM hs2
      have hone' : conjugacyWithin M t ∩ (Subgroup.centralizer ({u * t} : Set G) : Set G) =
          {t} := by
        rw [← pointRoots, hroots]
        exact hone
      rw [hone', hcard', h27, Nat.card_coe_set_eq, Set.ncard_singleton] at hpar
      norm_num at hpar
    ·
      have hEcard := card_eq_card_add_one_of_coe_eq hU (one_not_mem_pointClass
        (order_two_of_mem_pointClass hz (hclass ▸ distinguished_mem_pointClass t)) ∘ fun h1 =>
          h1.1.1)
      have hmove : ∃ x ∈ pointRoots M t (u * t), ¬ Commute r x := by
        by_contra hall
        push Not at hall
        have hsubE : pointRoots M t (u * t) ⊆ involutionPointClass z ∩ (M : Set G) ∩
            (Subgroup.centralizer ({r} : Set G) : Set G) ∩
            (Subgroup.centralizer ({u * t} : Set G) : Set G) := by
          intro x hx
          rw [← hXeq, ← hroots]
          exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr (hall x hx).symm⟩
        have hle := Nat.card_mono (Set.toFinite _) hsubE
        rw [hX, hroots] at hle
        omega
      obtain ⟨k, hk, hkcard, ⟨ψ⟩⟩ := hsub
      have : Finite k := Nat.finite_of_card_ne_zero (by rw [hkcard]; norm_num)
      have htK : t ∈ localInvolutionPointHull z r ⊓ Subgroup.centralizer ({u * t} : Set G) :=
        ⟨mem_localInvolutionPointHull htD hvt.symm,
          Subgroup.mem_centralizer_singleton_iff.mpr hst.eq.symm⟩
      obtain ⟨j, hjD, hjr, hjs, hjM⟩ := exists_class_mem_not_mem_of_card_le hkcard ψ htK htD
        htord (inf_le_left.trans (localInvolutionPointHull_le_centralizer z r)) inf_le_right
        (by rw [hX])
      obtain ⟨a', -, ⟨F, hFfield, hFcard, φ, -⟩, -, -, hcount⟩ :=
        squareFieldAction_of_flip hNC h' (hclass ▸ hjD) hjM hsM hrM hs hv hst hjs.symm hjr.symm
          hsr' hmove
      have : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; positivity)
      have hcount' : 2 ^ a' - 1 = 1 := by
        rw [← hcount, hroots, hXeq]
        exact hX
      have ha' : a' = 1 := by
        have h2 : 2 ^ a' = 2 ^ 1 := by omega
        exact Nat.pow_right_injective le_rfl h2
      subst ha'
      have hLeq : localInvolutionPointHull t (u * t) = localInvolutionPointHull z (u * t) := by
        rw [localInvolutionPointHull, localInvolutionPointHull, hclass]
      exact hAcyc (isCyclic_of_isPGroup_three_of_le hFcard φ (hLeq ▸ hAL) hA3)

end CFSG.ProperTwoGeneratedCore.HighRankPair
