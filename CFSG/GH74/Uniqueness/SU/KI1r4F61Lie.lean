module

public import CFSG.GH74.Uniqueness.SU.KI1r3FamLie
public import CFSG.GH74.Generic.Context
public import CFSG.GH74.KGroups.L28Tables
public import CFSG.GH74.KGroups.Sz8Tables
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenAllInvolutionFourGroup

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.Uniqueness.SU.K.R3
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def StrictFix (K : Type) [Group K] [Finite K] : Prop :=
  ∀ α : MulAut K, α ^ 2 = 1 →
    ∃ V : Subgroup K, (∀ v ∈ V, α v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4

theorem StrictFix.of_mulEquiv {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']
    (e : K ≃* K') (h : StrictFix K) : StrictFix K' := by
  intro α' hα'
  set α : MulAut K := MulAut.congr e.symm α' with hα
  have hα2 : α ^ 2 = 1 := by rw [hα, ← map_pow, hα', map_one]
  obtain ⟨V, hV, hVel, hVc⟩ := h α hα2
  refine ⟨V.map e.toMonoidHom, ?_, SU4.isElemAbelian_map e.toMonoidHom hVel, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    have h1 : α v = v := hV v hv
    have h2 : e.symm (α' (e v)) = v := h1
    have h3 := congrArg e h2
    rw [MulEquiv.apply_symm_apply] at h3
    exact h3
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hVc

theorem StrictFix.of_inner {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a)
    (h : ∀ α : MulAut K, α ^ 2 = 1 → ∃ g : K, α = MulAut.conj g) : StrictFix K := by
  intro α hα
  obtain ⟨g, rfl⟩ := h α hα
  exact four_group_fixed_of_inner hnab g hα

@[expose] def StrictFamLie (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel K t n p f → StrictFix K

namespace StrictAux

theorem strictFix_of_fixedSubgroup {K : Type} [Group K] [Finite K]
    (h : ∀ α : MulAut K, α ^ 2 = 1 → ∃ V : Subgroup K, V ≤ fixedSubgroup α ∧
      CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) : StrictFix K := by
  intro α hα
  obtain ⟨V, hV, hVel, hVc⟩ := h α hα
  exact ⟨V, fun v hv => hV hv,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).1 hVel, hVc⟩

theorem strictFix_of_out_inner {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a)
    (h : ∀ (φ : MulAut K) (n : ℕ), φ ^ 2 ^ n = 1 → ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹) :
    StrictFix K := by
  have := hs
  refine StrictFix.of_inner hnab fun α hα => ?_
  obtain ⟨k, hk⟩ := h α 1 (by rwa [pow_one])
  exact ⟨k, MulEquiv.ext fun x => (hk x).trans (MulAut.conj_apply k x).symm⟩

end StrictAux

open StrictAux CFSG.GH74.Uniqueness.SU.K.R3.FamLieAux
open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear

theorem strictAlt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → StrictFix (alternatingGroup (Fin n)) := by
  intro n hn7 _ α hα
  by_cases hα1 : α = 1
  · subst hα1
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    obtain ⟨V, -, hVel, hVc⟩ := four_group_fixed_of_inner
      (alternatingGroup_nonabelian (n := n) (by omega)) 1 (by rw [map_one, one_pow])
    exact ⟨V, fun v _ => by rw [MulAut.one_apply], hVel, hVc⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨⟨V, hV, hVel, hVc⟩, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.alternating_at_least_seven_involution_fixed_four_group
        hn7 α (orderOf_eq_prime hα hα1)
    exact ⟨V, fun v hv => hV hv,
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).1 hVel, hVc⟩

theorem strictLie_psl3 : StrictFamLie .PSL 3 := by
  intro K _ _ _ _ p f _ hp2 h
  exact strictFix_of_fixedSubgroup fun α hα =>
    odd_higher_linear_all_involution_fixed_four_group
      K hp2 (by norm_num) (statedClassical_of_lieModel (by norm_num) h) α hα

theorem strictLie_psl4 : StrictFamLie .PSL 4 := by
  intro K _ _ _ _ p f _ hp2 h
  exact strictFix_of_fixedSubgroup fun α hα =>
    odd_higher_linear_all_involution_fixed_four_group
      K hp2 (by norm_num) (statedClassical_of_lieModel (by norm_num) h) α hα

theorem strictLie_psl5 : StrictFamLie .PSL 5 := by
  intro K _ _ _ _ p f _ hp2 h
  exact strictFix_of_fixedSubgroup fun α hα =>
    odd_higher_linear_all_involution_fixed_four_group
      K hp2 (by norm_num) (statedClassical_of_lieModel (by norm_num) h) α hα

theorem strictLie_psu3 : StrictFamLie .PSU 3 := by
  intro K _ _ _ _ p f _ hp2 h
  exact strictFix_of_fixedSubgroup fun α hα =>
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.odd_unitary_all_involution_fixed_four_group
      K hp2 (statedClassical_of_lieModel (by norm_num) h) α hα

theorem strictLie_psu4 : StrictFamLie .PSU 4 := by
  intro K _ _ _ _ p f _ hp2 h
  exact strictFix_of_fixedSubgroup fun α hα =>
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.odd_unitary_all_involution_fixed_four_group
      K hp2 (statedClassical_of_lieModel (by norm_num) h) α hα

theorem strictLie_psu5 : StrictFamLie .PSU 5 := by
  intro K _ _ _ _ p f _ hp2 h
  exact strictFix_of_fixedSubgroup fun α hα =>
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.odd_unitary_all_involution_fixed_four_group
      K hp2 (statedClassical_of_lieModel (by norm_num) h) α hα

theorem strictLie_psp2 : StrictFamLie .PSp 2 := by
  intro K _ _ _ _ p f _ hp2 h
  exact strictFix_of_fixedSubgroup fun α hα =>
    CFSG.LocalAnalysis.ComponentInitial.OddSymplectic.odd_symplectic_all_involution_fixed_four_group
      K hp2 (statedClassical_of_lieModel (by norm_num) h) α hα

theorem strictLie_g2 :
    StrictFamLie .G2 0 := by
  intro K _ _ hsimple hnab p f hp hp2 h
  have := hsimple
  have hS := chevalley_of_lieModel_g2 h
  exact strictFix_of_fixedSubgroup fun α hα =>
    CFSG.LieType.Chevalley.odd_G2_F4_E8_all_involution_fixed_four_group K hnab .G2 (Or.inl rfl)
      hp hp2 hS.1.2.1 hS α hα

theorem strictLie_3d4 :
    StrictFamLie .trialityD4 0 := by
  intro K _ _ hsimple hnab p f hp hp2 h
  have := hsimple
  have hS := chevalley_of_lieModel_trialityD4 h
  exact strictFix_of_fixedSubgroup fun α hα =>
    CFSG.LieType.Chevalley.odd_triality_all_involution_fixed_four_group K hnab hp hp2 hS.1.2.1 hS
      α hα

theorem strictRee :
    ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      ∀ f : ℕ, LieModel K .twistedG2 0 3 f → StrictFix K := by
  intro K _ _ hsimple hnab f h
  have := hsimple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine StrictFix.of_inner hnab fun α hα => ?_
  have hout := (CFSG.LieType.Ree.SuzukiReeOuterTwoPart.small_Ree_case (ree_of_lieModel h)).1
  have : Finite (MulAut K) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer K) := Nat.card_pos
  have hodd : ¬ 2 ∣ Nat.card (Outer K) := by
    intro h2
    have h3 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' h2
    exact (Nat.ne_of_gt (Nat.one_lt_two_pow h3.ne')) hout
  have hx2 : (QuotientGroup.mk α : Outer K) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hx1 : (QuotientGroup.mk α : Outer K) = 1 := by
    by_contra hne
    have hord := orderOf_eq_prime hx2 hne
    have hdvd := orderOf_dvd_natCard (QuotientGroup.mk α : Outer K)
    rw [hord] at hdvd
    exact hodd hdvd
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).1 hx1
  exact ⟨g, hg.symm⟩

theorem strictL28
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (h : LieModel K .PSL 2 2 3) : StrictFix K :=
  strictFix_of_out_inner hs hnab fun φ n hφ => CFSG.GH74.KGroups.L28.out_inner h φ n hφ

theorem strictU34 {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (h : LieModel K .PSU 3 2 2) : StrictFix K := by
  have := hs
  refine strictFix_of_fixedSubgroup fun α hα => ?_
  exact
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_unitary_all_involution_fixed_four_group
      K hnab (CFSG.GH74.Generic.stated_of_lieModel_PSU h) α hα

theorem strictSz8
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (h : LieModel K .twistedB2 0 2 3) : StrictFix K :=
  strictFix_of_out_inner hs hnab fun φ n hφ => CFSG.GH74.KGroups.Sz8.out_inner h φ n hφ

end CFSG.GH74.Uniqueness.SU.K.R4
