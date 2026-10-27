module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeLinModel
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic

public section

namespace CFSG.AGLEmbedding

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

theorem natDegree_le_two_of_dvd_X_pow_three_sub_one {K : Type*} [Field K] {b : K[X]}
    (hb : Irreducible b) (hdvd : b ∣ X ^ 3 - C 1) : b.natDegree ≤ 2 := by
  have h1 : b ∣ (X - C 1) * (X ^ 2 + X + 1) := by
    convert hdvd using 1
    simp only [map_one]
    ring
  have h2 : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  rcases hb.prime.dvd_or_dvd h1 with h | h
  · have := natDegree_le_of_dvd h (X_sub_C_ne_zero 1)
    rw [natDegree_X_sub_C] at this
    omega
  · have hne : (X ^ 2 + X + 1 : K[X]) ≠ 0 := fun h0 => by
      rw [h0, natDegree_zero] at h2
      omega
    exact h2 ▸ natDegree_le_of_dvd h hne

variable {r : ℕ} {K : Type} [Field K]

theorem spProj_injective_of_card_eq_two (hK : Nat.card K = 2) : Function.Injective (proj r K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [SymplecticFlag.proj, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  rw [units_eq_one_of_card_eq_two hK c, map_one] at hc
  exact Subgroup.mem_bot.mpr (Subtype.ext hc.symm)

theorem exists_perfect_le_centralizer_of_isQuasisimple (hK : Nat.card K = 2)
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hcent : Subgroup.centralizer {a} = (Subgroup.centralizer {x}).map (proj r K))
    {P : Type*} [Group P] {ψ : P →* StatedSp r K} (hψ : Function.Injective ψ)
    (hψx : ψ.range ≤ Subgroup.centralizer {x}) {L : Subgroup P} (hL : CFSG.IsQuasisimple L) :
    ∃ Q : Subgroup (StatedProj (StatedSp r K)), Q ≤ Subgroup.centralizer {a} ∧ ⁅Q, Q⁆ = Q ∧
      Q ≠ ⊥ := by
  have hinj : Function.Injective ((proj r K).comp ψ) :=
    (spProj_injective_of_card_eq_two hK).comp hψ
  obtain ⟨h1, h2⟩ := perfect_map_of_isQuasisimple hinj hL
  refine ⟨L.map ((proj r K).comp ψ), ?_, h1, h2⟩
  rw [hcent, ← Subgroup.map_map]
  exact Subgroup.map_mono ((Subgroup.map_le_range ψ L).trans hψx)

open scoped _root_.Classical in
theorem exists_perfect_of_spSupported (hK : Nat.card K = 2) {x : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (hx3 : x ^ 3 = 1) (HB : SpPrimaryBlocks 2 1 3 x a)
    (b : primaryFactors (spEnd x)) {g : StatedSp r K}
    (hg : g ∈ spSupported x {(b : K[X]), reciprocalPolynomial (b : K[X])}) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hgp : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ Q : Subgroup (StatedProj (StatedSp r K)), Q ≤ Subgroup.centralizer {a} ∧ ⁅Q, Q⁆ = Q ∧
      Q ≠ ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fact p.Prime := ⟨hp⟩
  have hsupp : ∀ O : Set K[X], spSupported x O ≤ Subgroup.centralizer {x} := fun O z hz => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mem_spSupported.mp hz).1
  have hdeg : (b : K[X]).natDegree ≤ 2 := by
    refine natDegree_le_two_of_dvd_X_pow_three_sub_one (irreducible_of_mem_primaryFactors b.2)
      ((mem_primaryFactors.mp b.2).2.2.trans (minpoly.dvd K _ ?_))
    simp [spEnd_pow hx3]
  by_cases hX : (b : K[X]) = X - 1
  · rw [hX, reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton] at hg
    obtain ⟨φ, -⟩ := HB.fixedFactor (hX ▸ b.2)
    let g'' : spSupported x {X - 1} := ⟨g, hg⟩
    have hB := HB.fixed_nondegenerate
    have halt : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
      fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
    obtain ⟨Q, hQ, hQ1⟩ := exists_perfect_of_prime_order_alt hK halt hB (g := φ g'') hp hp5
      (by rw [← map_pow, show g'' ^ p = 1 from Subtype.ext (by simpa using hgp), map_one])
      (fun h1 => hg1 (congrArg Subtype.val (φ.injective (h1.trans (map_one φ).symm))))
    let ψ := (proj r K).comp ((spSupported x {X - 1}).subtype.comp φ.symm.toMonoidHom)
    have hψ : Function.Injective ψ := (spProj_injective_of_card_eq_two hK).comp
      ((Subgroup.subtype_injective _).comp φ.symm.injective)
    refine ⟨Q.map ψ, ?_, by rw [← Subgroup.map_commutator, hQ], fun h0 => hQ1
      ((Subgroup.map_eq_bot_iff_of_injective Q hψ).mp h0)⟩
    rw [HB.centralizer_eq]
    rintro _ ⟨q, -, rfl⟩
    exact ⟨_, hsupp _ (φ.symm q).2, rfl⟩
  by_cases hself : reciprocalPolynomial (b : K[X]) = b
  · rw [hself, Set.pair_eq_singleton] at hg
    obtain ⟨d, hd, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
      HB.selfDual b hX hself
    have hd1 : 1 * d = 1 := by
      have := hE.one_le
      omega
    let g'' : spSupported x {(b : K[X])} := ⟨g, hg⟩
    have hq := isQuasisimple_sesqSU_of_prime_order hE (Or.inl hd1) hHf hHfl (g := φ g'') hp hp5
      (by rw [← map_pow, show g'' ^ p = 1 from Subtype.ext (by simpa using hgp), map_one])
      (fun h1 => hg1 (congrArg Subtype.val (φ.injective (h1.trans (map_one φ).symm))))
    have hL : CFSG.IsQuasisimple ((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm hq
    exact exists_perfect_le_centralizer_of_isQuasisimple hK HB.centralizer_eq
      (ψ := (spSupported x {(b : K[X])}).subtype.comp φ.symm.toMonoidHom)
      ((Subgroup.subtype_injective _).comp φ.symm.injective)
      (by rintro _ ⟨q, rfl⟩; exact hsupp _ (φ.symm q).2) hL
  · have HP := HB.paired b (Ne.symm hself)
    obtain ⟨φ⟩ := HP.matrixFactor
    have hcardE := HP.card_field
    set m := primaryMultiplicity (spEnd x) (b : K[X]) with hm
    have : Fintype (AdjoinRoot (b : K[X])) := by
      have : Finite (AdjoinRoot (b : K[X])) :=
        Nat.finite_of_card_ne_zero (by rw [hcardE]; positivity)
      exact Fintype.ofFinite _
    have hE4 : Fintype.card (AdjoinRoot (b : K[X])) ≤ 4 := by
      rw [← Nat.card_eq_fintype_card, hcardE]
      calc (2 ^ 1) ^ (b : K[X]).natDegree ≤ (2 ^ 1) ^ 2 := Nat.pow_le_pow_right (by norm_num) hdeg
        _ = 4 := by norm_num
    by_cases hbig : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset (AdjoinRoot (b : K[X])), s.card = 4)
    · have hq := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hbig.1 hbig.2
      have hL : CFSG.IsQuasisimple (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin m)
          (AdjoinRoot (b : K[X])))) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
      exact exists_perfect_le_centralizer_of_isQuasisimple hK HB.centralizer_eq
        (ψ := ((spSupported x {(b : K[X]), reciprocalPolynomial (b : K[X])}).subtype.comp
          φ.symm.toMonoidHom).comp Matrix.SpecialLinearGroup.toGL)
        (((Subgroup.subtype_injective _).comp φ.symm.injective).comp
          Matrix.SpecialLinearGroup.toGL_injective)
        (by rintro _ ⟨q, rfl⟩; exact hsupp _ (φ.symm _).2) hL
    · exfalso
      let g' : spSupported x {(b : K[X]), reciprocalPolynomial (b : K[X])} := ⟨g, hg⟩
      have hg'p : g' ^ p = 1 := Subtype.ext (by simpa using hgp)
      have hg'1 : g' ≠ 1 := fun h1 => hg1 (congrArg Subtype.val h1)
      have hord : orderOf (φ g') = p := by
        rw [MulEquiv.orderOf_eq]
        exact orderOf_eq_prime hg'p hg'1
      refine not_dvd_card_GL_of_small hp hp5 ?_ (hord ▸ orderOf_dvd_natCard (φ g'))
      rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with h0 | h1 | h2
      · exact Or.inl h0
      · exact Or.inr (Or.inl ⟨h1, hE4⟩)
      · refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · by_contra h3
          exact hbig ⟨h2, Or.inl (by omega)⟩
        · by_contra h3
          obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
            (s := Finset.univ (α := AdjoinRoot (b : K[X]))) (n := 4)
            (by rw [Finset.card_univ]; omega)
          exact hbig ⟨h2, Or.inr ⟨t, ht⟩⟩

open scoped _root_.Classical in
theorem eq_one_of_mem_centralizer_psp_two (hK : Nat.card K = 2) (hr : 1 ≤ r)
    {a : StatedProj (StatedSp r K)} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hfree : ∀ Q : Subgroup (StatedProj (StatedSp r K)), Q ≤ Subgroup.centralizer {a} →
      ⁅Q, Q⁆ = Q → Q = ⊥)
    {y : StatedProj (StatedSp r K)} (hy : y ∈ Subgroup.centralizer {a}) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hyp : y ^ p = 1) : y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  obtain ⟨⟨x, ⟨hxa, hxo⟩, -⟩, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks
    Nat.prime_two le_rfl (by rw [hK]; norm_num : Nat.card K = 2 ^ 1) Nat.prime_three
    (by norm_num) (by norm_num) hr a ha
  have HB := hblocks x hxa hxo
  have hx3 : x ^ 3 = 1 := hxo ▸ pow_orderOf_eq_one x
  by_contra hy1
  rw [HB.centralizer_eq] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hzp : z ^ p = 1 := spProj_injective_of_card_eq_two hK (by rw [map_pow, hyp, map_one])
  have hz1 : z ≠ 1 := fun h => hy1 (by rw [h, map_one])
  obtain ⟨hcomm, hind, hsup⟩ := HB.directProduct
  have : Finite (reciprocalOrbits (spEnd x)) :=
    (((primaryFactors (spEnd x)).finite_toSet).image _).to_subtype
  rw [← hsup] at hz
  obtain ⟨⟨O, hO⟩, g, hgO, hgp, hg1⟩ := exists_ne_one_mem_of_iSupIndep
    (H := fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij u v hu hv => hcomm i i.2 j j.2 (fun h => hij (Subtype.ext h)) u hu v hv)
    hind hz hzp hz1
  obtain ⟨h, hh, rfl⟩ := hO
  obtain ⟨Q, hQa, hQ, hQ1⟩ := exists_perfect_of_spSupported hK hx3 HB ⟨h, hh⟩ hgO hp hp5 hgp hg1
  exact hQ1 (hfree Q hQa hQ)

theorem threeAutFixedTwoThree_of_model_psp_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSp n 2 1) : ThreeAutFixedTwoThree X := by
  have hout := (symplectic_model_outer_two_part_bound X n 2 1 h).2.2.2.2
  obtain ⟨⟨-, -, hn2, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn3 : 3 ≤ n := by
    by_contra h3
    exact hne (by rw [show n = 2 by omega]; rfl)
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have : IsSimpleGroup (StatedProj (StatedSp n K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K n (by omega)
      (Or.inr (Or.inr ⟨hK2, hn3⟩))
  have : Group.IsPerfect (StatedProj (StatedSp n K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect n K
      (Or.inr (Or.inr ⟨hK2, hn3⟩))
  have h1 : Nat.card (Outer X) = 1 := Nat.dvd_one.mp (by simpa using hout hn3)
  refine ThreeAutFixedTwoThree.of_mulEquiv e (threeAutFixedTwoThree_of_inner_prime
    center_eq_bot_of_simple_of_perfect ?_ ?_)
  · rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
      h1]
    norm_num
  · intro a ha3 hfree y hy p hp hp5 hyp
    have ha1 : a ≠ 1 := by
      rintro rfl
      have h1 := hfree ⊤ (fun z _ => by
        rw [Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul])
        Group.IsPerfect.commutator_eq_top
      exact (top_ne_bot (α := Subgroup (StatedProj (StatedSp n K)))) h1
    exact eq_one_of_mem_centralizer_psp_two hK2 (by omega) ha3 ha1 hfree hy hp hp5 hyp

theorem threeAutFixedTwoThree_lie_B_two (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ (r : ℕ) (q : TauCeti.PrimePower), q.card = 2 ∧ d.1 = .B r q) :
    ThreeAutFixedTwoThree (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, hq, hd⟩ := hd
  simp only at hd
  subst hd
  obtain ⟨hp2, hf⟩ := ParabHub.primePower_eq_of_card_eq Nat.prime_two hq
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr3 : 3 ≤ r := by
    by_contra h3
    exact hr.2 ⟨by omega, hq⟩
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp2 hr3
    (MulEquiv.refl _)
  rw [hp2, hf] at h
  exact threeAutFixedTwoThree_of_model_psp_two h

end CFSG.AGLEmbedding
