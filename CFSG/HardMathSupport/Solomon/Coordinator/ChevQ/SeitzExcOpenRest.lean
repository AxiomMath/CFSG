module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding TauCeti
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes
open CFSG.Assembly.LowTwoRank

@[expose] def ExcCubeOpenRest (d : LieTypeIndex) (p : ℕ) : Prop :=
  p = 3 ∨ ∃ q : PrimePower,
    (d = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 2 ∧ p < 11) ∨
    (d = .E8 q ∧ ((orderOf ((q.card : ℕ) : ZMod p) = 2 ∧ p < 11) ∨
      (orderOf ((q.card : ℕ) : ZMod p) = 4 ∧ p = 5) ∨
      (p = 5 ∧ orderOf ((q.card : ℕ) : ZMod p) = 1)))

@[expose] def SeitzGoodInnerExcOpenRest : Prop :=
  SeitzHyperLie fun d p E₀ => IsTopIndex d.1 ∧ ¬ NormalizesRSub d E₀ ∧ SeitzGoodIndex p d.1 ∧
    ExcCubeOpenRest d.1 p

theorem seitzHyperLie_orth_good (hO2 : SeitzGoodInnerOrthTwo) :
    SeitzHyperLie fun d p _ => IsOrthogonalIndex d.1 ∧ SeitzGoodIndex p d.1 := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨ho, hgood⟩
  by_cases hred : OReducible d p E₀
  · exact seitzHyperLie_orthReducible d p hp hp2 hpd hlist E₀ hE₀ hcard hred
  · exact seitzGoodInnerOrth_of_two hO2 d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨ho, hred, hgood⟩

theorem not_p1ThreeLieList_orth {p : ℕ} (hp5 : 5 ≤ p) {d : ValidLieTypeIndex}
    (hd : (∃ r q, d.1 = .D r q) ∨ (∃ r q, 3 ≤ r ∧ d.1 = .B r q)) : ¬ P1ThreeLieList p d := by
  unfold P1ThreeLieList
  rintro (⟨n, q', hq', -⟩ | ⟨q', -, hq'⟩ | ⟨-, m, hm⟩ | ⟨q', ⟨-, -, hq'⟩ | ⟨h3, -, -, -⟩⟩ | hch)
  · rcases hd with ⟨r, q, hq⟩ | ⟨r, q, -, hq⟩ <;> rw [hq] at hq' <;> cases hq'
  · rcases hd with ⟨r, q, hq⟩ | ⟨r, q, -, hq⟩ <;> rw [hq] at hq' <;> cases hq'
  · rcases hd with ⟨r, q, hq⟩ | ⟨r, q, -, hq⟩ <;> rw [hq] at hm <;> cases hm
  · rcases hd with ⟨r, q, hq⟩ | ⟨r, q, hr, hq⟩
    · rw [hq] at hq'
      cases hq'
    · rw [hq] at hq'
      cases hq'
      omega
  · omega
  · unfold IsP1ChevTwoIndex at hch
    rcases hch with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, hq'⟩
    · omega
    · omega
    · rcases hd with ⟨r, q, hq⟩ | ⟨r, q, -, hq⟩ <;> rw [hq] at hq' <;> cases hq'

theorem seitzGoodIndex_orth {p : ℕ} (hp5 : 5 ≤ p) {d : LieTypeIndex}
    (hd : (∃ r q, d = .D r q) ∨ (∃ r q, d = .B r q)) : SeitzGoodIndex p d := by
  refine Or.inl ?_
  rintro (h | ⟨h3, -⟩)
  · rcases hd with ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩ <;> simp only [Bal207Index] at h <;> omega
  · omega

theorem exists_primePower_card (K : Type) [Field K] [Finite K] :
    ∃ q : PrimePower, Nat.card K = q.card := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  exact ⟨⟨ringChar K, n, hℓ, n.pos⟩, by rw [Nat.card_eq_fintype_card, hn, PrimePower.card_def]⟩

theorem plusModel_cubes_of_cat {K : Type} [Field K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.D r q).Valid) (hK : Nat.card K = q.card) {p : ℕ}
    (h : ∀ E₀ : Subgroup (Cat ⟨.D r q, hv⟩), IsElemAbelian p E₀ → Nat.card E₀ = p ^ 3 →
      HyperGen p ⊤ E₀)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K)))) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : HyperGen p ⊤ E := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hX : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus r K))) .POmegaPlus r
      q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, hr⟩, K, inferInstance, inferInstance,
      by rw [hK, PrimePower.card_def], ⟨MulEquiv.refl _⟩⟩
  have hY : StatedClassicalModel (Cat ⟨.D r q, hv⟩) .POmegaPlus r q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, hr⟩, _, inferInstance,
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
      CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_D r q)
        (LieTypeIndex.fieldExponent_D r q),
      ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv⟩⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hX hY
  refine hyperGen_of_mulEquiv e ?_
  exact h _ (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _)
    (by rw [Subgroup.card_map_of_injective e.injective, hEc])

theorem oddModel_cubes_of_cat {K : Type} [Field K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.B r q).Valid) (hr3 : 3 ≤ r) (hq2 : q.p ≠ 2) (hK : Nat.card K = q.card)
    {p : ℕ}
    (h : ∀ E₀ : Subgroup (Cat ⟨.B r q, hv⟩), IsElemAbelian p E₀ → Nat.card E₀ = p ^ 3 →
      HyperGen p ⊤ E₀)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K)))) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : HyperGen p ⊤ E := by
  have hX : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd r K))) .POmegaOdd r
      q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, hr3, hq2⟩, K, inferInstance, inferInstance,
      by rw [hK, PrimePower.card_def], ⟨MulEquiv.refl _⟩⟩
  have hY : StatedClassicalModel (Cat ⟨.B r q, hv⟩) .POmegaOdd r q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, hr3, hq2⟩, _, inferInstance,
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
      CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_B r q)
        (LieTypeIndex.fieldExponent_B r q),
      ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq2
        hr3⟩⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hX hY
  refine hyperGen_of_mulEquiv e ?_
  exact h _ (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _)
    (by rw [Subgroup.card_map_of_injective e.injective, hEc])

theorem plusModel_cubes_of_orthTwo (hO2 : SeitzGoodInnerOrthTwo) {K : Type} [Field K] [Finite K]
    {r : ℕ} (hr : 4 ≤ r) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K)))) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : HyperGen p ⊤ E := by
  obtain ⟨q, hK⟩ := exists_primePower_card K
  have hv : (LieTypeIndex.D r q).Valid :=
    (LieTypeIndex.valid_iff _).mpr ⟨(LieTypeIndex.inStandardRange_iff _).mpr hr, by simp⟩
  refine plusModel_cubes_of_cat hv hK (fun E₀ hE₀ hc => ?_) E hE hEc
  have hpq : p ≠ q.p := by
    intro h
    apply hpK
    rw [hK, PrimePower.card_def, h]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact seitzHyperLie_orth_good hO2 ⟨.D r q, hv⟩ p hp (by omega) (by simpa using hpq)
    (not_p1ThreeLieList_orth hp5 (Or.inl ⟨r, q, rfl⟩)) E₀ hE₀ hc
    ⟨Or.inr (Or.inl ⟨r, q, rfl⟩), seitzGoodIndex_orth hp5 (Or.inl ⟨r, q, rfl⟩)⟩

theorem oddModel_cubes_of_orthTwo (hO2 : SeitzGoodInnerOrthTwo) {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) {r : ℕ} (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : ¬ p ∣ Nat.card K)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K)))) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : HyperGen p ⊤ E := by
  obtain ⟨q, hK⟩ := exists_primePower_card K
  have hq2 : q.p ≠ 2 := by
    intro h
    apply h2
    have hc : ringChar K = 2 := by
      have hd : 2 ∣ Nat.card K := by
        rw [hK, PrimePower.card_def, h]
        exact dvd_pow_self _ q.exponent_pos.ne'
      have := (Fintype.ofFinite K)
      obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
      rw [Nat.card_eq_fintype_card, hn] at hd
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 (Nat.prime_two.dvd_of_dvd_pow hd)).symm
    have : CharP K 2 := ringChar.of_eq hc
    exact CharTwo.two_eq_zero
  have hv : (LieTypeIndex.B r q).Valid :=
    (LieTypeIndex.valid_iff _).mpr ⟨(LieTypeIndex.inStandardRange_iff _).mpr ⟨by omega,
      fun h => by omega⟩, by simp; omega⟩
  refine oddModel_cubes_of_cat hv hr hq2 hK (fun E₀ hE₀ hc => ?_) E hE hEc
  have hpq : p ≠ q.p := by
    intro h
    apply hpK
    rw [hK, PrimePower.card_def, h]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact seitzHyperLie_orth_good hO2 ⟨.B r q, hv⟩ p hp (by omega) (by simpa using hpq)
    (not_p1ThreeLieList_orth hp5 (Or.inr ⟨r, q, hr, rfl⟩)) E₀ hE₀ hc
    ⟨Or.inl ⟨r, q, rfl, hr, hq2⟩, seitzGoodIndex_orth hp5 (Or.inr ⟨r, q, rfl⟩)⟩

section Assembly

set_option linter.unusedSectionVars false

theorem seven_le_of_ne_five' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h5 : p ≠ 5) : 7 ≤ p := by
  have h6 : p ≠ 6 := fun h => by
    rw [h] at hp
    norm_num at hp
  omega

theorem seitzGoodInnerExcOpen_of_rest (hO2 : SeitzGoodInnerOrthTwo)
    (hrest : SeitzGoodInnerExcOpenRest) : SeitzGoodInnerExcOpen := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, hopen⟩
  by_cases hr : ExcCubeOpenRest d.1 p
  · exact hrest d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, hr⟩
  have hp3 : p ≠ 3 := fun h => hr (Or.inl h)
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    by_contra h
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  obtain ⟨d, hv⟩ := d
  rcases hopen with h3 | ⟨q, ⟨hd, h2⟩ | ⟨hd, hord⟩⟩
  · exact absurd h3 hp3
  · simp only at hd h2
    rcases hd with rfl | rfl | rfl
    ·
      refine hyperGen_F4_two hv hp hp5 h2 (fun hq2 K _ _ hK E hE hEc => ?_) hE₀ hcard
      have hpK : ¬ p ∣ Nat.card K := by
        rw [hK]
        exact not_dvd_card_of_ne hp (by simpa using hpd)
      have h2K : (2 : K) ≠ 0 := by
        intro h0
        have : Fintype K := Fintype.ofFinite K
        obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
        have hc : ringChar K = 2 := by
          have hd2 : ringChar K ∣ 2 := ringChar.dvd (by exact_mod_cast h0)
          exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd2
        apply hq2
        have hq : q.p ^ q.exponent = 2 ^ (n : ℕ) := by
          rw [← PrimePower.card_def, ← hK, Nat.card_eq_fintype_card, hn, hc]
        have hd : q.p ∣ 2 ^ (n : ℕ) := hq ▸ dvd_pow_self q.p q.exponent_pos.ne'
        exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hd)
      exact oddModel_cubes_of_orthTwo hO2 h2K (by norm_num) hp hp5 hpK E hE hEc
    ·
      have hp11 : 11 ≤ p := by
        by_contra h
        exact hr (Or.inr ⟨q, Or.inl ⟨rfl, h2, by omega⟩⟩)
      refine hyperGen_E7_two hv hp hp11 h2 (fun K _ _ hK E hE hEc => ?_) hE₀ hcard
      have hpK : ¬ p ∣ Nat.card K := by
        rw [hK]
        exact not_dvd_card_of_ne hp (by simpa using hpd)
      exact plusModel_cubes_of_orthTwo hO2 (by norm_num) hp hp5 hpK E hE hEc
    ·
      refine hyperGen_twistedE6_two hv hp hp5 h2 (fun k _ _ hk E hE hEc => ?_) hE₀ hcard
      have hpk : ¬ p ∣ Nat.card k := by
        rw [hk]
        exact not_dvd_card_of_ne hp
          (by simpa [TauCeti.LieTypeIndex.characteristic_twistedE6] using hpd)
      exact plusModel_cubes_of_orthTwo hO2 le_rfl hp hp5 hpk E hE hEc
  · simp only at hd hord
    subst hd
    have hpq : p ≠ q.p := by simpa using hpd
    rcases hord with h2 | h3 | h4 | h6 | ⟨h5, h1⟩
    ·
      have hp11 : 11 ≤ p := by
        by_contra h
        exact hr (Or.inr ⟨q, Or.inr ⟨rfl, Or.inl ⟨h2, by omega⟩⟩⟩)
      refine hyperGen_E8_two hv hp hp11 h2 (fun K _ _ hK E hE hEc => ?_) hE₀ hcard
      have hpK : ¬ p ∣ Nat.card K := by
        rw [hK]
        exact not_dvd_card_of_ne hp hpq
      exact plusModel_cubes_of_orthTwo hO2 (by norm_num) hp hp5 hpK E hE hEc
    · exact hyperGen_E8_three hv hp hp5 hpq h3 hE₀ hcard
    ·
      have hp7 : 7 ≤ p := by
        refine seven_le_of_ne_five' hp hp5 fun h5 => ?_
        exact hr (Or.inr ⟨q, Or.inr ⟨rfl, Or.inr (Or.inl ⟨h4, h5⟩)⟩⟩)
      exact hyperGen_E8_four hv hp hp7 h4 hE₀ hcard
    · exact hyperGen_E8_six hv hp hpq h6 hE₀ hcard
    · exact absurd (Or.inr ⟨q, Or.inr ⟨rfl, Or.inr (Or.inr ⟨h5, h1⟩)⟩⟩) hr

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest
