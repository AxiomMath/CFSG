module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIII
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.LocalAnalysis.ComponentInitial in
theorem not_nine_dvd_card_outer_of_psl_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL n 2 1) : ¬ 9 ∣ Nat.card (Outer X) := by
  obtain ⟨⟨-, -, hn, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn3 : 3 ≤ n := by
    by_contra h3
    exact hn2 (by rw [show n = 2 by omega]; rfl)
  have e' : X ≃* LinearFlag.projectiveSL n K := e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have hdvd := UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound Nat.prime_two
    le_rfl hn3 hK
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  intro h9
  have := h9.trans hdvd
  norm_num at this

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag in
theorem not_nine_dvd_card_outer_of_psu_prime {X : Type} [Group X] {n p : ℕ}
    (h : StatedClassicalModel X .PSU n p 1) (hp : p = 2 ∨ p = 3) : ¬ 9 ∣ Nat.card (Outer X) := by
  obtain ⟨⟨hpp, hf, hn, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p 1 K := ⟨hpp, hf, by rw [hK]; ring⟩
  have hq : ¬(n = 3 ∧ p ^ 1 = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h1 := (UnitaryHigher.unitary_full_diagonal_outer_order hU hn hq).2.2.2.2.1
  have e' : X ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv, h1]
  have hdvd : 2 * 1 * Nat.gcd n (p ^ 1 + 1) ∣ 2 * (p + 1) := by
    rw [mul_one, pow_one]
    exact Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_right _ _)
  intro h9
  have := h9.trans hdvd
  rcases hp with rfl | rfl <;> norm_num at this

open CFSG.LocalAnalysis.ComponentInitial in
theorem not_nine_dvd_card_outer_of_psp_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSp n 2 1) : ¬ 9 ∣ Nat.card (Outer X) := by
  have hdvd := (symplectic_model_outer_two_part_bound X n 2 1 h).2.1
  intro h9
  have := h9.trans hdvd
  norm_num at this

open CFSG.LocalAnalysis.ComponentInitial in
theorem not_nine_dvd_card_outer_of_psl_seven {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 7 1) : ¬ 9 ∣ Nat.card (Outer X) := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have hdvd := (linear_two_outer_order_divisor (p := 7) (f := 1) (by norm_num) F
    (by simpa using hcard)).2 X ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩
  intro h9
  have := h9.trans hdvd
  norm_num at this

theorem not_nine_dvd_card_outer_of_census {X : Type} [Group X]
    (h : (∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2IndexTwo d.1 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      ∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ¬ 9 ∣ Nat.card (Outer X) := by
  rcases h with ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  · cases d with
    | A r q =>
      change q.card = 2 at hd
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at h
      exact not_nine_dvd_card_outer_of_psl_two h
    | twistedA r q =>
      change q.card = 2 at hd
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      rw [hp, hf] at h
      exact not_nine_dvd_card_outer_of_psu_prime h (Or.inl rfl)
    | B r q =>
      change q.card = 2 at hd
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
      by_cases h2 : r = 2
      · subst h2
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rw [hp, hf] at h
        exact not_nine_dvd_card_outer_of_psp_two h
      · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp
          (by omega) e
        rw [hp, hf] at h
        exact not_nine_dvd_card_outer_of_psp_two h
    | C r q => exact hd.elim
    | D r q =>
      exact not_nine_dvd_of_mulEquiv e
        (not_nine_dvd_card_outer_orthTwo ⟨.D r q, hv⟩ ⟨r, q, hd, Or.inl rfl⟩)
    | twistedD r q =>
      exact not_nine_dvd_of_mulEquiv e
        (not_nine_dvd_card_outer_orthTwo ⟨.twistedD r q, hv⟩ ⟨r, q, hd, Or.inr (Or.inl rfl)⟩)
    | G2 q =>
      change q.card = 2 at hd
      have hq3 : 3 ≤ q.card :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      omega
    | _ => exact hd.elim
  · exact not_nine_dvd_of_mulEquiv e (not_nine_dvd_card_outer_alt (by omega))
  · rcases hd with ⟨q, hq7, hd⟩ | ⟨q, hq3, hd⟩
    · simp only at hd
      subst hd
      obtain ⟨hp7, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq7
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp7, hf] at h
      exact not_nine_dvd_card_outer_of_psl_seven h
    · simp only at hd
      subst hd
      obtain ⟨hp3, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq3
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp3, hf] at h
      exact not_nine_dvd_card_outer_of_psu_prime h (Or.inr rfl)

theorem map_overgroup_of_central {Y X : Type*} [Group Y] [Group X] [Finite Y] {ρ : Y →* X}
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center Y) (S : Sylow 2 Y)
    {J : Subgroup Y} (hNJ : Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((S : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    IsSylowTwoOf ((S : Subgroup Y).map ρ) ⊤ ∧
      Subgroup.normalizer (((S : Subgroup Y).map ρ : Subgroup X) : Set X) ≤ J.map ρ ∧
      J.map ρ ≠ Subgroup.normalizer (((S : Subgroup Y).map ρ : Subgroup X) : Set X) ∧
      ∀ V : Subgroup X, V ≤ J.map ρ → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_surjective ρ hρ
  have hZN : Subgroup.center Y ≤ Subgroup.normalizer ((S : Subgroup Y) : Set Y) :=
    Subgroup.center_le_normalizer _
  have hZJ : Subgroup.center Y ≤ J := hZN.trans hNJ
  have hN := normalizer_map_le S hρ hker
  refine ⟨?_, hN.trans (Subgroup.map_mono hNJ), ?_, ?_⟩
  · have hS : ((S.mapSurjective hρ : Sylow 2 X) : Subgroup X) = (S : Subgroup Y).map ρ := by
      rw [Sylow.coe_mapSurjective]
    rw [← hS]
    refine ⟨le_top, (S.mapSurjective hρ).isPGroup', ?_⟩
    rw [show (((S.mapSurjective hρ : Sylow 2 X) : Subgroup X).subgroupOf ⊤).index =
      ((S.mapSurjective hρ : Sylow 2 X) : Subgroup X).index from Subgroup.relIndex_top_right _]
    exact (S.mapSurjective hρ).not_dvd_index
  · intro h
    apply hJ
    refine le_antisymm ?_ hNJ
    have h1 : J.map ρ ≤ (Subgroup.normalizer ((S : Subgroup Y) : Set Y)).map ρ := by
      rw [h]
      exact hN
    have h2 := Subgroup.comap_mono (f := ρ) h1
    rwa [Subgroup.comap_map_eq_self (hker.trans hZN), Subgroup.comap_map_eq_self
      (hker.trans hZJ)] at h2
  · intro V hVJ hV
    obtain ⟨W, hW, hWV, hWm⟩ := exists_perfect_map_eq ρ hker hV
      (by rw [MonoidHom.range_eq_top_of_surjective ρ hρ]; exact le_top)
    have hWJ : W ≤ J := by
      intro w hw
      obtain ⟨j, hj, hjw⟩ := hVJ (Subgroup.mem_comap.1 (hWV hw))
      have hk : j⁻¹ * w ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hjw, inv_mul_cancel]
      rw [show w = j * (j⁻¹ * w) by group]
      exact J.mul_mem hj (hZJ (hker hk))
    rw [← hWm]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd W ρ) (hperf W hWJ hW)

theorem kFactOutNineParabolic : KFactOutNineParabolic := by
  intro Y _ _ hY hcl T J hT hNJ hJ hperf h9
  have : Group.IsPerfect Y := ⟨hY.1⟩
  obtain ⟨S, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have hρ : Function.Surjective (QuotientGroup.mk' (Subgroup.center Y)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center Y)).ker ≤ Subgroup.center Y :=
    (QuotientGroup.ker_mk' _).le
  obtain ⟨hT', hN1, hN2, hperf'⟩ := map_overgroup_of_central hρ hker S hNJ hJ hperf
  exact not_nine_dvd_card_outer_of_census
    (kFactParabolicThreeCensus _ hcl _ _ hT' hN1 hN2 hperf')
    (h9.trans (card_outer_dvd_card_outer_centerQuotient Y))

end CFSG.AGLEmbedding
