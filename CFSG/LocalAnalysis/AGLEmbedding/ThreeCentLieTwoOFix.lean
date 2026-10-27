module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import CFSG.RankThree.PartOne.KC.AlternatingSymplecticBasis
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeLin
public import CFSG.Assembly.Defs

public section

namespace CFSG.AGLEmbedding

open Module QuadraticMap

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem polarBilin_isAlt_of_charTwo [CharP K 2] (Q : QuadraticForm K W) :
    (polarBilin Q).IsAlt := fun v => by
  change polar Q v v = 0
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

theorem exists_le_finrank_eq_of_le (T : Submodule K W) [FiniteDimensional K T] {n : ℕ}
    (hn : n ≤ finrank K T) : ∃ T' ≤ T, finrank K T' = n := by
  classical
  obtain ⟨s, hs, hli⟩ := exists_finset_linearIndependent_of_le_finrank (R := K) (M := T) hn
  refine ⟨(Submodule.span K (s : Set T)).map T.subtype, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Submodule.finrank_map_subtype_eq, finrank_span_finset_eq_card hli, hs]

theorem exists_totallySingular_of_card_eq_two [FiniteDimensional K W] (hK : Nat.card K = 2)
    {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate) :
    ∃ U : Submodule K W, finrank K W ≤ 2 * finrank K U + 2 ∧ ∀ u ∈ U, Q u = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  obtain ⟨s, b, hfin, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis
    (polarBilin_isAlt_of_charTwo Q) hQ
  set E := Submodule.span K (Set.range (b ∘ Sum.inl))
  have hE : finrank K E = s := by
    rw [finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective), Fintype.card_fin]
  have hpol : ∀ u ∈ E, ∀ v ∈ E, polar Q u v = 0 := by
    intro u hu v hv
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        exact hb.1 i j
      | zero => exact polar_zero_right _ _
      | add v w _ _ hv hw => rw [polar_add_right, hv, hw, add_zero]
      | smul c v _ hv => rw [polar_smul_right, hv, smul_zero]
    | zero => exact polar_zero_left _ _
    | add u w _ _ hu hw => rw [polar_add_left, hu, hw, add_zero]
    | smul c u _ hu => rw [polar_smul_left, hu, smul_zero]
  have hsq : ∀ c : K, c * c = c := fun c => by
    have := FiniteField.pow_card c
    rwa [Fintype.card_eq_nat_card, hK, pow_two] at this
  let φ : E →ₗ[K] K :=
    { toFun := fun u => Q u
      map_add' := fun u v => by
        change Q ((u : W) + v) = Q u + Q v
        have h0 := hpol u u.2 v v.2
        unfold QuadraticMap.polar at h0
        linear_combination h0
      map_smul' := fun c u => by
        change Q (c • (u : W)) = c • Q u
        rw [QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, hsq] }
  refine ⟨(LinearMap.ker φ).map E.subtype, ?_, ?_⟩
  · rw [Submodule.finrank_map_subtype_eq]
    have hrk := LinearMap.finrank_range_add_finrank_ker φ
    have hr : finrank K (LinearMap.range φ) ≤ 1 := by
      calc finrank K (LinearMap.range φ) ≤ finrank K K := Submodule.finrank_le _
        _ = 1 := finrank_self K
    omega
  · rintro _ ⟨u, hu, rfl⟩
    exact hu

theorem exists_perfect_of_derived {Q : QuadraticForm K W}
    (hperf : Group.IsPerfect ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hnt : Nontrivial ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    ∃ P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), ⁅P, P⁆ = P ∧ P ≠ ⊥ := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  let e := Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self O)
  have hP : Group.IsPerfect ↥((⁅O, O⁆).subgroupOf O) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨(⁅O, O⁆).subgroupOf O, Subgroup.isPerfect_iff.mp hP, fun h => ?_⟩
  have : Nontrivial ↥⁅O, O⁆ := hnt
  have : Nontrivial ↥((⁅O, O⁆).subgroupOf O) := e.toEquiv.nontrivial
  rw [h] at this
  exact not_nontrivial _ this

variable [FiniteDimensional K W]

theorem exists_perfect_of_prime_order_orth (hK : Nat.card K = 2) {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) {g : TauCeti.QuadraticMap.orthogonalGroup Q} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), ⁅P, P⁆ = P ∧ P ≠ ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    orderOf_eq_prime hg hg1 ▸ orderOf_dvd_natCard g
  have hts3 : (∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) →
      ∃ P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), ⁅P, P⁆ = P ∧ P ≠ ⊥ := fun hT => by
    have hq := CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQ hT
    exact exists_perfect_of_derived hq.1 (CFSG.LocalCores.isQuasisimple_nontrivial hq)
  obtain ⟨s, -, hfin, -⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis
    (polarBilin_isAlt_of_charTwo Q) hQ
  rcases s with _ | m
  · exfalso
    have : Subsingleton W := Module.finrank_zero_iff.mp (by simpa using hfin)
    exact hg1 (Subtype.ext (LinearEquiv.ext fun w => Subsingleton.elim _ _))
  by_cases hm3 : 3 ≤ m
  · obtain ⟨U, hU, hUQ⟩ := exists_totallySingular_of_card_eq_two hK hQ
    obtain ⟨T, hTU, hT⟩ := exists_le_finrank_eq_of_le U (n := 3) (by omega)
    exact hts3 ⟨T, hT, fun u hu => hUQ u (hTU hu)⟩
  have hcardK : (Nat.card K : ℤ) = 2 := by exact_mod_cast hK
  have hsmall : ∀ e : ℤ, ((e = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
      (e = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)) →
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 2 * 2 ^ (m * (m + 1)) *
        (2 ^ (m + 1) - e) * ∏ i ∈ Finset.Icc 1 m, ((2 ^ 2 : ℤ) ^ i - 1) := fun e he => by
    rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hfin he, hcardK]
  by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
  · have hc := hsmall 1 (Or.inl ⟨rfl, hplus⟩)
    interval_cases m
    · exfalso
      have h2 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 ^ 1 * 3 ^ 0 := by
        have h1 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
            ((2 ^ 1 * 3 ^ 0 : ℕ) : ℤ) := by rw [hc]; decide
        exact_mod_cast h1
      exact not_dvd_two_pow_mul_three_pow hp hp5 1 0 (h2 ▸ hdvd)
    · exfalso
      have h2 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 ^ 3 * 3 ^ 2 := by
        have h1 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
            ((2 ^ 3 * 3 ^ 2 : ℕ) : ℤ) := by rw [hc]; decide
        exact_mod_cast h1
      exact not_dvd_two_pow_mul_three_pow hp hp5 3 2 (h2 ▸ hdvd)
    · obtain ⟨U, hU, hUQ⟩ := hplus
      exact hts3 ⟨U, by omega, hUQ⟩
  · have hc := hsmall (-1) (Or.inr ⟨rfl, hplus⟩)
    have hts : ∀ U : Submodule K W, finrank K U = finrank K W / 2 → ∃ u ∈ U, Q u ≠ 0 := by
      intro U hU
      by_contra hall
      push Not at hall
      exact hplus ⟨U, by omega, hall⟩
    interval_cases m
    · exfalso
      have h2 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 ^ 1 * 3 ^ 1 := by
        have h1 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
            ((2 ^ 1 * 3 ^ 1 : ℕ) : ℤ) := by rw [hc]; decide
        exact_mod_cast h1
      exact not_dvd_two_pow_mul_three_pow hp hp5 1 1 (h2 ▸ hdvd)
    all_goals
      obtain ⟨hs, hperf, -⟩ := CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
        Q hQ (by omega) hts
      exact exists_perfect_of_derived hperf hs.toNontrivial

end CFSG.AGLEmbedding
