module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOrth
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClNum
import CFSG.RankThree.PartOne.S11d.OrthSplitModel
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOBlock
import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

section Helpers

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ¬ ∀ x y : G, x * y = y * x) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    apply hna
    intro x y
    exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y)) x

theorem card_quotient_center_of_center_eq_bot {G : Type*} [Group G]
    (h : Subgroup.center G = ⊥) : Nat.card (G ⧸ Subgroup.center G) = Nat.card G :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).toEquiv

end Helpers

section Unsplit

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem card_orthDerived_mul_two [Nontrivial W] (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Nat.card ↥(orthDerived Q) * 2 = Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have heq : orthDerived Q = CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ)
      (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT)
  have hle : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
  have hidx := CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup Q hQ
  rw [← heq, Subgroup.relIndex] at hidx
  have h1 := Subgroup.card_mul_index ((orthDerived Q).subgroupOf
    (TauCeti.QuadraticMap.orthogonalGroup Q))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  exact h1

theorem unsplit_a5_charTwo (Q : QuadraticForm K W) (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ finrank K W)
    (hns : ¬ (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0))
    (h60 : Nat.card (↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) ⧸
      Subgroup.center ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))) = 60) :
    finrank K W = 4 ∧ Nat.card K = 2 := by
  classical
  have hNontriv : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set Φ := orthDerivedEquivCommutator Q with hΦ
  have hcardΩ : Nat.card ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) =
      Nat.card ↥(orthDerived Q) := Nat.card_congr Φ.toEquiv
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  ·
    exfalso
    obtain ⟨T, hT3, hTQ⟩ := hT
    have hd6 : 6 ≤ finrank K W := by
      have := CFSG.ComponentClassification.UnbalancedCatalog.two_mul_finrank_le_of_singular hQ hTQ
      omega
    have hZ : Subgroup.center ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) = ⊥ := by
      have h1 := center_orthDerived_eq_bot hQ ⟨T, hT3, hTQ⟩
      have h2 := Subgroup.map_center_eq Φ.symm
      rw [h1] at h2
      simpa using h2.symm
    have hΩ60 : Nat.card ↥(orthDerived Q) = 60 := by
      rw [← hcardΩ, ← card_quotient_center_of_center_eq_bot hZ]
      exact h60
    have hO := card_orthDerived_mul_two Q hQ ⟨T, hT3, hTQ⟩
    rw [hΩ60] at hO
    obtain ⟨⟨n, hn⟩, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
        Q hQ |>.imp_right fun h => h.1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm2 : 2 ≤ m := by omega
    have hqZ : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq2
    have hOZ : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) ≥ 896 := by
      have hcard : ∀ ε : ℤ, (ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
          (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) →
          (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) ≥ 896 := by
        intro ε hε
        have hεb : ε ≤ 1 := by rcases hε with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
        rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hn hε]
        have h1 : (64 : ℤ) ≤ (Nat.card K : ℤ) ^ (m * (m + 1)) :=
          calc (64 : ℤ) = 2 ^ 6 := by norm_num
            _ ≤ 2 ^ (m * (m + 1)) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
            _ ≤ _ := pow_le_pow_left₀ (by norm_num) hqZ _
        have h2 : (7 : ℤ) ≤ (Nat.card K : ℤ) ^ (m + 1) - ε := by
          have : (8 : ℤ) ≤ (Nat.card K : ℤ) ^ (m + 1) :=
            calc (8 : ℤ) = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
              _ ≤ _ := pow_le_pow_left₀ (by norm_num) hqZ _
          linarith
        have h3 : (1 : ℤ) ≤ ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
          have : 0 < ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
            refine Finset.prod_pos fun i hi => ?_
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            have : (1 : ℤ) < ((Nat.card K : ℤ) ^ 2) ^ i :=
              one_lt_pow₀ (by nlinarith) (by omega)
            linarith
          omega
        have hAB : (64 : ℤ) * 7 ≤ (Nat.card K : ℤ) ^ (m * (m + 1)) *
            ((Nat.card K : ℤ) ^ (m + 1) - ε) :=
          mul_le_mul h1 h2 (by norm_num) (by linarith)
        have hABP : (64 : ℤ) * 7 * 1 ≤ (Nat.card K : ℤ) ^ (m * (m + 1)) *
            ((Nat.card K : ℤ) ^ (m + 1) - ε) *
            ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
          mul_le_mul hAB h3 (by norm_num) (by linarith)
        linarith
      by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType Q
      · exact hcard 1 (Or.inl ⟨rfl, hp⟩)
      · exact hcard (-1) (Or.inr ⟨rfl, hp⟩)
    have : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 120 := by
      rw [← hO]
      norm_num
    omega
  ·
    obtain ⟨⟨n, hn⟩, -, hnf, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
        Q hQ
    by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, Q u = 0
    · exfalso
      obtain ⟨U, hUn, hUQ⟩ := hS
      have hn2 : n = 2 := by
        by_contra hne
        exact hT (exists_threeSingular_of_le Q hUQ (by omega))
      subst hn2
      exact hns ⟨by omega, U, hUn, hUQ⟩
    · have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, Q u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        exact hS ⟨U, hU, hcon⟩
      rcases hnf n (by omega) hn with ⟨b, hb⟩ | ⟨β, γ, -, -, b, hb⟩
      · exfalso
        refine hS ⟨Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)), ?_, ?_⟩
        · exact (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans
            (by simp)
        · intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0
      · have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)),
            Q u = 0 := by
          intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0 0 0
        have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) =>
            b (Sum.inl i))) = n - 1 :=
          (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
        have hn23 : n = 2 ∨ n = 3 := by
          by_contra hne
          exact hT (exists_threeSingular_of_le Q hU (by omega))
        have hts' : ∀ U : Submodule K W, finrank K U = finrank K W / 2 → ∃ u ∈ U, Q u ≠ 0 :=
          fun U hU => hts U (by omega)
        rcases hn23 with rfl | rfl
        ·
          obtain ⟨hsimple, -, hna, -, -, h4, -⟩ :=
            even_minus_four_six_actual_derived_extraction Q hQ (Or.inl (by omega)) hts'
          obtain ⟨E, _, _, D, ψ, ρ, -, -, -, hrange, hcard⟩ := h4 (by omega)
          rw [hrange] at hcard
          haveI := hsimple
          have hZ : Subgroup.center ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) =
              ⊥ := by
            have h1 : Subgroup.center ↥(orthDerived Q) = ⊥ := center_eq_bot_of_simple hna
            have h2 := Subgroup.map_center_eq Φ.symm
            rw [h1] at h2
            simpa using h2.symm
          have hΩ60 : Nat.card ↥(orthDerived Q) = 60 := by
            rw [← hcardΩ, ← card_quotient_center_of_center_eq_bot hZ]
            exact h60
          have hq60 : Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) = 60 := by
            rw [← hcard]
            exact hΩ60
          refine ⟨by omega, ?_⟩
          by_contra hne
          have h3 : 3 ≤ Nat.card K := by omega
          have h9 : 9 ≤ Nat.card K ^ 2 := by nlinarith
          have h81 : 81 ≤ Nat.card K ^ 4 := by nlinarith
          have : 9 * 80 ≤ Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) :=
            Nat.mul_le_mul h9 (by omega)
          omega
        ·
          exfalso
          obtain ⟨hsimple, -, hna, -, -, -, h6⟩ :=
            even_minus_four_six_actual_derived_extraction Q hQ (Or.inr (by omega)) hts'
          obtain ⟨E, _, _, D, ψ, ρ, -, -, -, hrange, hcard⟩ := h6 (by omega)
          rw [hrange] at hcard
          haveI := hsimple
          have hZ : Subgroup.center ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) =
              ⊥ := by
            have h1 : Subgroup.center ↥(orthDerived Q) = ⊥ := center_eq_bot_of_simple hna
            have h2 := Subgroup.map_center_eq Φ.symm
            rw [h1] at h2
            simpa using h2.symm
          have hΩ60 : Nat.card ↥(orthDerived Q) = 60 := by
            rw [← hcardΩ, ← card_quotient_center_of_center_eq_bot hZ]
            exact h60
          have hq60 : Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
              (Nat.card K ^ 4 - 1) = 60 := by
            rw [← hcard]
            exact hΩ60
          have hdvd : Nat.card K ^ 6 ∣ 60 :=
            ⟨(Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) * (Nat.card K ^ 4 - 1), by
              rw [← hq60]
              ring⟩
          have h64 : 64 ≤ Nat.card K ^ 6 :=
            calc 64 = 2 ^ 6 := by norm_num
              _ ≤ _ := Nat.pow_le_pow_left hq2 6
          have := Nat.le_of_dvd (by norm_num) hdvd
          omega

theorem fixed_unsplit_a5 {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} [Nontrivial V]
    (hQ : (polarBilin Q).Nondegenerate) (hx : OddOrderIsometry Q p x)
    (hlist : FixedLayerListed Q x)
    (hns : ¬ (finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x),
      finrank K S = 2 ∧ ∀ s ∈ S, (Q.comp (fixedSpace x).subtype) s = 0))
    (h60 : Nat.card (↥(fixedComponentImage Q x) ⧸ Subgroup.center ↥(fixedComponentImage Q x)) =
      60) :
    finrank K (fixedSpace x) = 4 ∧ Nat.card K = 2 := by
  let e : ↥(fixedComponentImage Q x) ≃*
      ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :=
    (fixedComponentImageEquiv hQ hx).trans (orthDerivedEquivCommutator _).symm
  have h60' : Nat.card (↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype))) ⧸ Subgroup.center ↥(commutator ↥(
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))) = 60 := by
    rw [← h60]
    exact (Nat.card_congr (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)).toEquiv)
  exact unsplit_a5_charTwo _ hx.polarBilin_fixed_nondegenerate hlist.1 hns h60'

end Unsplit

section Split

open Polynomial CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem card_sl_two_of_card_four (hK : Nat.card K = 4) : Nat.card SL(2, K) = 60 := by
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear K 2 (by norm_num), hK]
  norm_num [Finset.Icc_self]

theorem exists_elemAbelian_determinant [CharP K 2] (hK : Nat.card K = 4) :
    ∃ E : Subgroup (DeterminantIsometries K), CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 25 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card SL(2, K) := by rw [card_sl_two_of_card_four hK]; norm_num
  obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card' 5 h5
  obtain ⟨B, hB⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hA5 : A ^ 5 = 1 := by have := pow_orderOf_eq_one A; rwa [hA] at this
  have hB5 : B ^ 5 = 1 := by have := pow_orderOf_eq_one B; rwa [hB] at this
  let P : Subgroup (SL(2, K) × SL(2, K)) := (Subgroup.zpowers A).prod (Subgroup.zpowers B)
  have hPcard : Nat.card P = 25 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hA, hB]
  have hcomm : ∀ p q : SL(2, K) × SL(2, K), p ∈ P → q ∈ P → p * q = q * p := by
    intro p q hp hq
    obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.mp hp
    obtain ⟨hq1, hq2⟩ := Subgroup.mem_prod.mp hq
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hp1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hq1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hq2
    refine Prod.ext ?_ ?_
    · show p.1 * q.1 = q.1 * p.1
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self A i j).eq
    · show p.2 * q.2 = q.2 * p.2
      rw [← hk, ← hl]
      exact (Commute.zpow_zpow_self B k l).eq
  have hexp : ∀ p : SL(2, K) × SL(2, K), p ∈ P → p ^ 5 = 1 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.mp hp
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hp1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp2
    refine Prod.ext ?_ ?_
    · show p.1 ^ 5 = 1
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA5, one_zpow]
    · show p.2 ^ 5 = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hB5, one_zpow]
  refine ⟨P.map (specialRho (K := K)), ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, p, hp, rfl⟩ := a
    obtain ⟨_, q, hq, rfl⟩ := b
    apply Subtype.ext
    show specialRho p * specialRho q = specialRho q * specialRho p
    rw [← map_mul, ← map_mul, hcomm p q hp hq]
  · rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow, hexp p hp, map_one]
  · rw [Subgroup.card_map_of_injective (CFSG.RankThree.PartOne.specialRho_injective), hPcard]

theorem exists_elemAbelian_split [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K W}
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) ≃* DeterminantIsometries K)
    (hK : Nat.card K = 4) :
    ∃ E : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 25 := by
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_determinant hK
  refine ⟨E.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hE _, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem nonempty_equiv_splitFactor {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
      DeterminantIsometries K) (i : Fin 2) :
    Nonempty (↥(supportedFactor hx (splitFourFactors e i)) ≃* SL(2, K)) := by
  have h1 : ↥(supportedFactor hx (splitFourFactors e i)) ≃* ↥(splitFourFactors e i) :=
    (((splitFourFactors e i).map (fixedBlockEquiv hx).symm.toMonoidHom).equivMapOfInjective
      (supportedBlock Q x (X - 1)).subtype
      (supportedBlock Q x (X - 1)).subtype_injective).symm.trans
      ((splitFourFactors e i).equivMapOfInjective (fixedBlockEquiv hx).symm.toMonoidHom
        (fixedBlockEquiv hx).symm.injective).symm
  fin_cases i
  · obtain ⟨eL⟩ := CFSG.ComponentClassification.Burgoyne.C.nonempty_equiv_determinantLeftFactor
      (K := K)
    exact ⟨h1.trans (((determinantLeftFactor K).equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).symm.trans eL)⟩
  · obtain ⟨eR⟩ := CFSG.ComponentClassification.Burgoyne.C.nonempty_equiv_determinantRightFactor
      (K := K)
    exact ⟨h1.trans (((determinantRightFactor K).equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).symm.trans eR)⟩

theorem split_a5 {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
      DeterminantIsometries K) (hK : 3 < Nat.card K)
    (hF : ∀ i : Fin 2, supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q) (i : Fin 2)
    (h60 : Nat.card (↥(fixedFactorImage hx (splitFourFactors e i)) ⧸
      Subgroup.center ↥(fixedFactorImage hx (splitFourFactors e i))) = 60) :
    Nat.card K = 4 ∨ Nat.card K = 5 := by
  obtain ⟨φ⟩ := nonempty_equiv_splitFactor hx e i
  have hperf : commutator ↥(supportedFactor hx (splitFourFactors e i)) = ⊤ :=
    commutator_eq_top_of_mulEquiv φ.symm
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K
        (by omega)).commutator_eq_top
  have h := card_quotient_center_map_projective (hF i) hperf
  have h60' : Nat.card (SL(2, K) ⧸ Subgroup.center SL(2, K)) = 60 := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).toEquiv]
    exact h.symm.trans h60
  exact (sl_a5 (le_refl 2) h60').2

end Split

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
