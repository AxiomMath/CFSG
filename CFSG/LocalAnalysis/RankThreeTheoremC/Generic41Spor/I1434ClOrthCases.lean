module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOrthRank
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenOrthRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.Open
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Block

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem block_component_a5 (hx : OddOrderIsometry Q 5 x) (hℓ5 : ringChar K ≠ 5) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (h60 : Nat.card (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h)) = 60) :
    h = reciprocalPolynomial h ∧ primaryMultiplicity x.toLinearMap h = 2 ∧
      ∃ d, h.natDegree = 2 * d ∧ Nat.card K ^ d = 4 := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hFΩ : specialBlock Q x h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  have h60' : Nat.card (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) = 60 := by
    rw [← h60]
    exact (card_quotient_center_map_projective hFΩ hq.1.commutator_eq_top).symm
  by_cases hself : h = reciprocalPolynomial h
  · exact ⟨hself, selfDual_a5 hx hh hne1 hself hℓ5 hq h60'⟩
  · exact (paired_not_a5 hx hh hne1 hself hq h60').elim

end Block

section Arith

theorem pow_eq_four {q d : ℕ} (hq : 2 ≤ q) (h : q ^ d = 4) :
    (q = 4 ∧ d = 1) ∨ (q = 2 ∧ d = 2) := by
  rcases Nat.lt_or_ge d 3 with hd | hd
  · interval_cases d
    · simp at h
    · left
      exact ⟨by simpa using h, rfl⟩
    · right
      have : q * q = 4 := by simpa [pow_two] using h
      have hq2 : q = 2 := by nlinarith
      exact ⟨hq2, rfl⟩
  · exfalso
    have : 2 ^ 3 ≤ q ^ d := (Nat.pow_le_pow_left hq 3).trans (Nat.pow_le_pow_right (by omega) hd)
    omega

variable {K : Type} [Field K] [Finite K]

theorem card_ne_five (hℓ5 : ringChar K ≠ 5) : Nat.card K ≠ 5 := by
  intro h5
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, h5] at hcard
  have hdvd : ringChar K ∣ 5 := by
    have : ringChar K ∣ ringChar K ^ (n : ℕ) := dvd_pow_self _ n.ne_zero
    rwa [← hcard] at this
  exact hℓ5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hdvd)

theorem charP_two_of_card_four (h : Nat.card K = 4) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, h]; norm_num)

theorem charP_two_of_card_two (h : Nat.card K = 2) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, h]; norm_num)

end Arith

section Cases

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem false_of_two_blocks (hx : OddOrderIsometry Q 5 x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (hℓ5 : ringChar K ≠ 5)
    (hno4 : ∀ E : Subgroup (V ≃ₗ[K] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian 5 E → Nat.card E ≠ 5 ^ 4)
    {h₁ h₂ : K[X]} (hR₁ : h₁ ∈ Rep) (hR₂ : h₂ ∈ Rep) (hne : h₁ ≠ h₂) (hne1₁ : h₁ ≠ X - 1)
    (hne1₂ : h₂ ≠ X - 1) (hq₁ : CFSG.IsQuasisimple ↥(specialBlock Q x h₁))
    (hq₂ : CFSG.IsQuasisimple ↥(specialBlock Q x h₂))
    (h60₁ : Nat.card (↥(componentImage Q x h₁) ⧸ Subgroup.center ↥(componentImage Q x h₁)) = 60)
    (h60₂ : Nat.card (↥(componentImage Q x h₂) ⧸ Subgroup.center ↥(componentImage Q x h₂)) = 60) :
    False := by
  classical
  have hh₁ := hRep.1 hR₁
  have hh₂ := hRep.1 hR₂
  haveI : Fact (Irreducible h₁) := ⟨irreducible_of_mem_primaryFactors hh₁⟩
  haveI : Fact (Irreducible h₂) := ⟨irreducible_of_mem_primaryFactors hh₂⟩
  obtain ⟨hs₁, hm₁, d₁, hdeg₁, hd₁⟩ := block_component_a5 hx hℓ5 hh₁ hne1₁ hq₁ h60₁
  obtain ⟨hs₂, hm₂, d₂, hdeg₂, hd₂⟩ := block_component_a5 hx hℓ5 hh₂ hne1₂ hq₂ h60₂
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rcases pow_eq_four hK2 hd₁ with ⟨hK4, hd1⟩ | ⟨hK2', hd2⟩
  ·
    have hd1' : d₂ = 1 := by
      rcases pow_eq_four hK2 hd₂ with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    obtain ⟨A₁, hA₁, hel₁, hc₁⟩ := exists_block_elemAbelian_two hx hh₁ hne1₁ hs₁ hm₁
    obtain ⟨A₂, hA₂, hel₂, hc₂⟩ := exists_block_elemAbelian_two hx hh₂ hne1₂ hs₂ hm₂
    obtain ⟨E, hE, hel, hcard⟩ := exists_elemAbelian_two_indices hx hRep
      (r₁ := ⟨h₁, hR₁⟩) (r₂ := ⟨h₂, hR₂⟩) (fun h => hne (congrArg Subtype.val h))
      ⟨hA₁, hel₁, hc₁⟩ ⟨hA₂, hel₂, hc₂⟩
    exact hno4 E (hE.trans inf_le_left) hel (by rw [hcard])
  ·
    have hd2' : d₂ = 2 := by
      rcases pow_eq_four hK2 hd₂ with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · exact h
    have hsum := sum_natDegree_le hx
    have h2 : h₁.natDegree + h₂.natDegree ≤ ∑ a ∈ primaryFactors x.toLinearMap, a.natDegree := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset (by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hh₁
        · rw [Finset.mem_singleton.mp ha]
          exact hh₂)
    omega

theorem split_card_four (hx : OddOrderIsometry Q 5 x) (hℓ5 : ringChar K ≠ 5)
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
      DeterminantIsometries K) (hK : 3 < Nat.card K)
    (hF : ∀ i : Fin 2, supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q) (i : Fin 2)
    (h60 : Nat.card (↥(fixedFactorImage hx (splitFourFactors e i)) ⧸
      Subgroup.center ↥(fixedFactorImage hx (splitFourFactors e i))) = 60) : Nat.card K = 4 := by
  rcases split_a5 hx e hK hF i h60 with h | h
  · exact h
  · exact absurd h (card_ne_five hℓ5)

theorem finrank_eq_twelve (hx : OddOrderIsometry Q 5 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) (hdeg : h.natDegree = 4)
    (hm : primaryMultiplicity x.toLinearMap h = 2) (hW : finrank K (fixedSpace x) = 4) :
    finrank K V = 12 := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    by_contra hnot
    have := fixedSpace_eq_bot_of_not_mem hnot
    rw [this] at hW
    simp at hW
  have hXdeg : (X - 1 : K[X]).natDegree = 1 := by
    simpa using natDegree_X_sub_C (1 : K)
  have hsum := sum_natDegree_le hx
  have hall : ∀ a ∈ primaryFactors x.toLinearMap, a = h ∨ a = X - 1 := by
    intro a ha
    by_contra hcon
    push Not at hcon
    have hapos : 1 ≤ a.natDegree := (irreducible_of_mem_primaryFactors ha).natDegree_pos
    have h3 : h.natDegree + ((X - 1 : K[X]).natDegree + a.natDegree) ≤
        ∑ b ∈ primaryFactors x.toLinearMap, b.natDegree := by
      have hn1 : h ∉ ({X - 1, a} : Finset K[X]) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun e => hne1 e, fun e => hcon.1 e.symm⟩
      have hn2 : (X - 1 : K[X]) ∉ ({a} : Finset K[X]) := by
        simp only [Finset.mem_singleton]
        exact fun e => hcon.2 e.symm
      rw [← Finset.sum_singleton (fun b : K[X] => b.natDegree) a,
        ← Finset.sum_insert hn2, ← Finset.sum_insert hn1]
      refine Finset.sum_le_sum_of_subset ?_
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact hh
      · exact hX
      · exact ha
    omega
  have hset : primaryFactors x.toLinearMap = {h, X - 1} := by
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hall a, fun ha => by rcases ha with rfl | rfl; exacts [hh, hX]⟩
  have hdim := finrank_eq_sum_primaryComponent hx.squarefree_minpoly
  rw [Finset.sum_coe_sort (primaryFactors x.toLinearMap)
    (fun a => finrank K (primaryComponent x.toLinearMap a)), hset,
    Finset.sum_pair hne1] at hdim
  have h1 : finrank K (primaryComponent x.toLinearMap h) = 8 := by
    rw [finrank_primaryComponent, hdeg]
    have : primaryMultiplicity x.toLinearMap h = 2 := hm
    rw [show finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 from this]
  have h2 : finrank K (primaryComponent x.toLinearMap (X - 1)) = 4 := by
    rw [← fixedSpace_eq_primaryComponent]
    exact hW
  omega

theorem natDegree_eq_two_of_selfDual (hx : OddOrderIsometry Q 5 x) (hK4 : Nat.card K = 4)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) : h.natDegree = 2 := by
  obtain ⟨d, ℓ, f, hU, B, hdeg, hq0, hchar, h5, -, -, -⟩ := selfDual_unitary_data hx hh hne1 hself
  have hpos := (irreducible_of_mem_primaryFactors hh).natDegree_pos
  have hle : h.natDegree ≤ 5 :=
    (Finset.single_le_sum (f := fun a : K[X] => a.natDegree) (fun a _ => Nat.zero_le _) hh).trans
      (sum_natDegree_le hx)
  rw [hK4] at h5
  have hd2 : d ≤ 2 := by omega
  interval_cases d
  · omega
  · exact hdeg
  · exact absurd h5 (by norm_num)

theorem mem_rep_of_selfDual (hx : OddOrderIsometry Q 5 x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {a : K[X]} (ha : a ∈ primaryFactors x.toLinearMap)
    (hself : a = reciprocalPolynomial a) : a ∈ Rep := by
  obtain ⟨r, ⟨hr, hor⟩, -⟩ := hRep.2 a ha
  rcases hor with h | h
  · rw [h]
    exact hr
  · have h2 := hx.reciprocal_reciprocal_eq (hRep.1 hr)
    rw [← h, ← hself] at h2
    rw [h2]
    exact hr

theorem exists_nonfixed_rank (hx : OddOrderIsometry Q 5 x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (hK4 : Nat.card K = 4)
    (hW4 : finrank K (fixedSpace x) = 4) (hN : 8 ≤ finrank K V) (hN9 : finrank K V ≤ 9) :
    (∃ r : ↥Rep, (r : K[X]) ≠ X - 1 ∧ ∃ A : Subgroup (V ≃ₗ[K] V),
        A ≤ supportedBlock Q x ↑r ∧ IsElemAbelian 5 A ∧ Nat.card A = 5 ^ 2) ∨
      (∃ r₁ r₂ : ↥Rep, r₁ ≠ r₂ ∧ (r₁ : K[X]) ≠ X - 1 ∧ (r₂ : K[X]) ≠ X - 1 ∧
        ∃ A₁ A₂ : Subgroup (V ≃ₗ[K] V),
          (A₁ ≤ supportedBlock Q x ↑r₁ ∧ IsElemAbelian 5 A₁ ∧ Nat.card A₁ = 5 ^ 1) ∧
          (A₂ ≤ supportedBlock Q x ↑r₂ ∧ IsElemAbelian 5 A₂ ∧ Nat.card A₂ = 5 ^ 1)) := by
  classical
  have h5K : 5 ∣ Nat.card K + 1 := by rw [hK4]
  have hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    by_contra hnot
    have := fixedSpace_eq_bot_of_not_mem hnot
    rw [this] at hW4
    simp at hW4
  set S := (primaryFactors x.toLinearMap).erase (X - 1) with hS
  have hSmem : ∀ a ∈ S, a ∈ primaryFactors x.toLinearMap ∧ a ≠ X - 1 := fun a ha =>
    ⟨(Finset.mem_erase.mp ha).2, (Finset.mem_erase.mp ha).1⟩
  have hSself : ∀ a ∈ S, a = reciprocalPolynomial a := fun a ha => by
    haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors (hSmem a ha).1⟩
    exact selfDual_of_dvd_card_add_one hx h5K (hSmem a ha).1 (hSmem a ha).2
  have hSdeg : ∀ a ∈ S, a.natDegree = 2 := fun a ha => by
    haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors (hSmem a ha).1⟩
    exact natDegree_eq_two_of_selfDual hx hK4 (hSmem a ha).1 (hSmem a ha).2 (hSself a ha)
  have hSrep : ∀ a ∈ S, a ∈ Rep := fun a ha =>
    mem_rep_of_selfDual hx hRep (hSmem a ha).1 (hSself a ha)
  have hdim := finrank_eq_sum_primaryComponent hx.squarefree_minpoly
  rw [Finset.sum_coe_sort (primaryFactors x.toLinearMap)
    (fun a => finrank K (primaryComponent x.toLinearMap a)),
    ← Finset.sum_erase_add _ _ hX] at hdim
  have hfix : finrank K (primaryComponent x.toLinearMap (X - 1)) = 4 := by
    rw [← fixedSpace_eq_primaryComponent]
    exact hW4
  have hterm : ∀ a ∈ S, finrank K (primaryComponent x.toLinearMap a) =
      2 * primaryMultiplicity x.toLinearMap a := fun a ha => by
    haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors (hSmem a ha).1⟩
    rw [finrank_primaryComponent, hSdeg a ha]
  rw [Finset.sum_congr rfl hterm, hfix] at hdim
  have hpos : ∀ a ∈ S, 1 ≤ primaryMultiplicity x.toLinearMap a := fun a ha => by
    haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors (hSmem a ha).1⟩
    exact hx.primaryMultiplicity_pos (hSmem a ha).1
  by_cases hbig : ∃ a ∈ S, 2 ≤ primaryMultiplicity x.toLinearMap a
  · obtain ⟨a, haS, hma⟩ := hbig
    have hle : 2 * primaryMultiplicity x.toLinearMap a ≤
        ∑ b ∈ S, 2 * primaryMultiplicity x.toLinearMap b :=
      Finset.single_le_sum (f := fun b => 2 * primaryMultiplicity x.toLinearMap b)
        (fun b _ => Nat.zero_le _) haS
    have hm2 : primaryMultiplicity x.toLinearMap a = 2 := by omega
    haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors (hSmem a haS).1⟩
    obtain ⟨A, hA, hel, hcard⟩ := exists_block_elemAbelian_two hx (hSmem a haS).1
      (hSmem a haS).2 (hSself a haS) hm2
    exact Or.inl ⟨⟨a, hSrep a haS⟩, (hSmem a haS).2, A, hA, hel, hcard⟩
  · push Not at hbig
    have hm1 : ∀ a ∈ S, primaryMultiplicity x.toLinearMap a = 1 := fun a ha => by
      have := hbig a ha
      have := hpos a ha
      omega
    have hsum : ∑ b ∈ S, 2 * primaryMultiplicity x.toLinearMap b = 2 * S.card := by
      rw [Finset.sum_congr rfl (fun b hb => by rw [hm1 b hb]), Finset.sum_const, smul_eq_mul]
      ring
    have hcard : 1 < S.card := by omega
    obtain ⟨a, haS, b, hbS, hab⟩ := Finset.one_lt_card.1 hcard
    haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors (hSmem a haS).1⟩
    haveI : Fact (Irreducible b) := ⟨irreducible_of_mem_primaryFactors (hSmem b hbS).1⟩
    obtain ⟨A₁, hA₁, hel₁, hc₁⟩ := exists_block_elemAbelian_one hx (hSmem a haS).1
      (hSmem a haS).2 (hSself a haS) (by rw [hm1 a haS]; norm_num)
    obtain ⟨A₂, hA₂, hel₂, hc₂⟩ := exists_block_elemAbelian_one hx (hSmem b hbS).1
      (hSmem b hbS).2 (hSself b hbS) (by rw [hm1 b hbS]; norm_num)
    exact Or.inr ⟨⟨a, hSrep a haS⟩, ⟨b, hSrep b hbS⟩, fun h => hab (congrArg Subtype.val h),
      (hSmem a haS).2, (hSmem b hbS).2, A₁, A₂, ⟨hA₁, hel₁, hc₁⟩, ⟨hA₂, hel₂, hc₂⟩⟩

theorem finrank_le_nine (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hK4 : Nat.card K = 4)
    (hno4 : ∀ E : Subgroup (V ≃ₗ[K] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian 5 E → Nat.card E ≠ 5 ^ 4) : finrank K V ≤ 9 := by
  by_contra hlt
  push Not at hlt
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h4 : 4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) :=
    CFSG.LocalAnalysis.RankFourTheoremC.BCDEven.le_pRank_orth (by norm_num)
      (by rw [hK4]; norm_num) (e := 2) (by norm_num) (by decide) (by rw [hK4]; norm_num) Q hQ
      (k := 4) (Or.inl (by omega))
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h4
  exact hno4 (E.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype)
    (Subgroup.map_subtype_le _) (CFSG.SectionRank.isElemAbelian_map hE _)
    (by rw [Subgroup.card_map_of_injective
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective, hcard])

theorem false_of_two_split (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q 5 x) {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep)
    (hℓ5 : ringChar K ≠ 5)
    (hno4 : ∀ E : Subgroup (V ≃ₗ[K] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian 5 E → Nat.card E ≠ 5 ^ 4)
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
      DeterminantIsometries K) (hK : 3 < Nat.card K) (hW4 : finrank K (fixedSpace x) = 4)
    (hF : ∀ i : Fin 2, supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q) (i : Fin 2)
    (h60 : Nat.card (↥(fixedFactorImage hx (splitFourFactors e i)) ⧸
      Subgroup.center ↥(fixedFactorImage hx (splitFourFactors e i))) = 60)
    (hN7 : 7 ≤ finrank K V) : False := by
  classical
  have hK4 := split_card_four hx hℓ5 e hK hF i h60
  haveI := charP_two_of_card_four hK4
  have hN : 8 ≤ finrank K V := by
    obtain ⟨⟨n, hn⟩, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
        Q hQ |>.imp_right fun h => h.1
    omega
  have hN9 := finrank_le_nine hQ hK4 hno4
  obtain ⟨A_W, hAW, helW, hcW⟩ := exists_fixed_elemAbelian hx e hK4
  have hW : fixedSpace x ≠ ⊥ := by
    intro hb
    rw [hb] at hW4
    simp at hW4
  obtain ⟨rF, hrF⟩ := exists_rep_X_sub_one hx hRep hW
  have hAW' : A_W ≤ supportedBlock Q x ↑rF := by rw [hrF]; exact hAW
  rcases exists_nonfixed_rank hx hRep hK4 hW4 hN hN9 with
    ⟨r, hr1, A, hA, hel, hc⟩ | ⟨r₁, r₂, hne, hr1, hr2, A₁, A₂, h₁, h₂⟩
  · have hne : r ≠ rF := fun he => hr1 (by rw [he, hrF])
    obtain ⟨E, hE, hel', hcard⟩ := exists_elemAbelian_two_indices hx hRep hne
      ⟨hA, hel, hc⟩ ⟨hAW', helW, hcW⟩
    exact hno4 E (hE.trans inf_le_left) hel' (by rw [hcard])
  · have h13 : r₁ ≠ rF := fun he => hr1 (by rw [he, hrF])
    have h23 : r₂ ≠ rF := fun he => hr2 (by rw [he, hrF])
    obtain ⟨E, hE, hel', hcard⟩ := exists_elemAbelian_three_indices hx hRep hne h13 h23
      h₁ h₂ ⟨hAW', helW, hcW⟩
    exact hno4 E (hE.trans inf_le_left) hel' (by rw [hcard])

theorem fixed_component_cases (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q 5 x) {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep)
    (hℓ5 : ringChar K ≠ 5)
    (hno4 : ∀ E : Subgroup (V ≃ₗ[K] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian 5 E → Nat.card E ≠ 5 ^ 4)
    (hN7 : 7 ≤ finrank K V) {Cset : Set (Subgroup (ProjOrthDerived Q))}
    (htype : (¬ FixedLayerListed Q x ∧ Cset = ∅) ∨
      (FixedLayerListed Q x ∧
        ¬ (finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
          ∀ s ∈ S, (Q.comp (fixedSpace x).subtype) s = 0) ∧
        CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (fixedSpace x).subtype))) ∧ Cset = {fixedComponentImage Q x}) ∨
      (FixedLayerListed Q x ∧
        ∃ e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
            DeterminantIsometries K,
          finrank K (fixedSpace x) = 4 ∧
          (∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
            ∀ s ∈ S, (Q.comp (fixedSpace x).subtype) s = 0) ∧
          3 < Nat.card K ∧
          (∀ i : Fin 2, supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q) ∧
          Cset = {fixedFactorImage hx (splitFourFactors e 0),
            fixedFactorImage hx (splitFourFactors e 1)}))
    {J : Subgroup (ProjOrthDerived Q)} (hJ : J ∈ Cset)
    (h60 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) :
    FixedLayerListed Q x ∧
      ¬ (finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
        ∀ s ∈ S, (Q.comp (fixedSpace x).subtype) s = 0) ∧
      Cset = {fixedComponentImage Q x} := by
  rcases htype with ⟨-, rfl⟩ | ⟨hlist, hns, -, hC⟩ | ⟨hlist, e, hW4, hsplit, hK, hF, hC⟩
  · exact absurd hJ (Set.notMem_empty J)
  · exact ⟨hlist, hns, hC⟩
  · exfalso
    rw [hC] at hJ
    rcases hJ with rfl | hJ
    · exact false_of_two_split hQ hx hRep hℓ5 hno4 e hK hW4 hF 0 h60 hN7
    · rw [Set.mem_singleton_iff] at hJ
      subst hJ
      exact false_of_two_split hQ hx hRep hℓ5 hno4 e hK hW4 hF 1 h60 hN7

theorem block_fixed_outcome (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V]
    (hx : OddOrderIsometry Q 5 x) {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep)
    (hℓ5 : ringChar K ≠ 5)
    (hno4 : ∀ E : Subgroup (V ≃ₗ[K] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian 5 E → Nat.card E ≠ 5 ^ 4)
    (hN7 : 7 ≤ finrank K V) {h : K[X]} (hR : h ∈ Rep) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (h60 : Nat.card (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h)) = 60)
    {Cset : Set (Subgroup (ProjOrthDerived Q))}
    (htype : (¬ FixedLayerListed Q x ∧ Cset = ∅) ∨
      (FixedLayerListed Q x ∧
        ¬ (finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
          ∀ s ∈ S, (Q.comp (fixedSpace x).subtype) s = 0) ∧
        CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (fixedSpace x).subtype))) ∧ Cset = {fixedComponentImage Q x}) ∨
      (FixedLayerListed Q x ∧
        ∃ e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
            DeterminantIsometries K,
          finrank K (fixedSpace x) = 4 ∧
          (∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
            ∀ s ∈ S, (Q.comp (fixedSpace x).subtype) s = 0) ∧
          3 < Nat.card K ∧
          (∀ i : Fin 2, supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q) ∧
          Cset = {fixedFactorImage hx (splitFourFactors e 0),
            fixedFactorImage hx (splitFourFactors e 1)}))
    {J : Subgroup (ProjOrthDerived Q)} (hJ : J ∈ Cset)
    (h60J : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) :
    Nat.card K = 2 ∧ finrank K V = 12 ∧ finrank K (fixedSpace x) = 4 := by
  have hh := hRep.1 hR
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨hs, hm, d, hdeg, hd⟩ := block_component_a5 hx hℓ5 hh hne1 hq h60
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨hlist, hns, hC⟩ := fixed_component_cases hQ hx hRep hℓ5 hno4 hN7 htype hJ h60J
  rw [hC, Set.mem_singleton_iff] at hJ
  subst hJ
  have hchar : CharP K 2 := by
    rcases pow_eq_four hK2 hd with ⟨h4, -⟩ | ⟨h2, -⟩
    · exact charP_two_of_card_four h4
    · exact charP_two_of_card_two h2
  obtain ⟨hW4, hK⟩ := fixed_unsplit_a5 hQ hx hlist hns h60J
  have hd2 : d = 2 := by
    rcases pow_eq_four hK2 hd with ⟨h4, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  exact ⟨hK, finrank_eq_twelve hx hh hne1 (by omega) hm hW4, hW4⟩


end Cases

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
