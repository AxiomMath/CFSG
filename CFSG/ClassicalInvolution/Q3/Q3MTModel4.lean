module

public import CFSG.ClassicalInvolution.Q3.Q3MTModel3
public import CFSG.ClassicalInvolution.Asc77.AscMuTabStar
public import CFSG.ClassicalInvolution.Uniform.U5Three

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups


section Orders

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}

theorem card_cls3 (M : Ih8Model 3 1 Ω t k e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls) : Nat.card R = 24 := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  obtain ⟨eR⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hR
  rw [Nat.card_congr eR.toEquiv]
  exact natCard_sl2_galoisField_three

theorem card_map3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls) :
    Nat.card (R.map M.ψ) = 24 := by
  obtain ⟨z, hz⟩ := hΩ.classical _ (M.map_mem hR)
  have hs : (MemberType.sl2 3 1).IsSolvableType := (by norm_num : (3 : ℕ) ^ 1 = 3)
  have hdvd : Nat.card ↥(R.map M.ψ) ∣ 24 := card_cls3 M hG2 hD4 hR ▸ Subgroup.card_map_dvd R M.ψ
  obtain ⟨eL⟩ := hz.nonempty_equiv_sl2Three hs
  have h24 : Nat.card (↥(R.map M.ψ) ⧸ CFSG.Open.classicalInvolutionOddCore ↥(R.map M.ψ)) = 24 := by
    rw [Nat.card_congr eL.toEquiv]
    exact natCard_sl2Three
  have h24' : 24 ∣ Nat.card ↥(R.map M.ψ) := by
    rw [← h24]
    exact Subgroup.card_quotient_dvd_card _
  exact Nat.dvd_antisymm hdvd h24'

theorem injOn_map3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls) :
    ∀ r ∈ R, ∀ s ∈ R, M.ψ r = M.ψ s → r = s := by
  have := finite_K3 M
  exact T3CII.injOn_of_natCard_map M.ψ
    (by rw [card_cls3 M hG2 hD4 hR, card_map3 M hΩ hG2 hD4 hR])

end Orders

theorem orderOf_map_of_injOn {K G : Type} [Group K] [Group G] (ψ : K →* G) {S : Subgroup K}
    (hinj : ∀ r ∈ S, ∀ s ∈ S, ψ r = ψ s → r = s) {x : K} (hx : x ∈ S) :
    orderOf (ψ x) = orderOf x := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro h
    exact hinj (x ^ n) (S.pow_mem hx n) 1 S.one_mem (by rw [map_pow, h, map_one])
  · intro h
    rw [← map_pow, h, map_one]

theorem natCard_isSylow2In_of_card {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hP : IsSylow2In P K) : Nat.card P = 2 ^ (Nat.card K).factorization 2 := by
  rw [← Sylow.card_eq_multiplicity (Uniform.sylowOfIsSylow2In hP),
    Uniform.coe_sylowOfIsSylow2In,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv]

theorem two_pow_factorization_24 : (2 : ℕ) ^ (Nat.factorization 24) 2 = 8 := by
  have h : (Nat.factorization 24) 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    have h1 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    have h0 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    omega
  rw [h]
  norm_num

section Star

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}

theorem star_elt3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R S : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls)
    (hS : S ∈ M.cls) (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) :
    ∃ s ∈ S, s ∈ Subgroup.normalizer (R : Set (modelUniv t k 3 e Fact.out).K) ∧
      orderOf s = 4 := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  have := finite_K3 M
  obtain ⟨-, -, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨R', hR', hUR', hcyc, hidx⟩ := hU
  obtain ⟨J', hJ', hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hJ'card : Nat.card J' = 24 := by
    obtain ⟨R₁, hR₁, rfl⟩ := (M.mem_iff J').mp hJ'
    exact card_map3 M hΩ hG2 hD4 hR₁
  have hR'card : Nat.card R' = 8 := by
    rw [natCard_isSylow2In_of_card hRJ', hJ'card]
    exact two_pow_factorization_24
  have h1 := Subgroup.relIndex_mul_card U R'
  rw [inf_eq_left.mpr hUR', hidx, hR'card] at h1
  have hUc : Nat.card U = 4 := by omega
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := U)
  have hordu : orderOf (u : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu, hUc]
  obtain ⟨s, hsS, hsu⟩ := hUJ u.2
  refine ⟨s, hsS, ?_, ?_⟩
  · exact mem_normalizer_of_map_gen3 M.ψ M.ker_le_center (ih8Model_ker_pow_three M hD4)
      (ih8Model_gen3 M hG2 hD4 hR) (by rw [hsu]; exact hUN u.2)
  · rw [← orderOf_map_of_injOn M.ψ (injOn_map3 M hΩ hG2 hD4 hS) hsS, hsu, hordu]

theorem star_data3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R S : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls)
    (hS : S ∈ M.cls) (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) :
    ∃ (eR : R ≃* SL(2, GaloisField 3 e)) (eS : S ≃* SL(2, GaloisField 3 e)),
      ∃ s ∈ S, s ∈ Subgroup.normalizer (R : Set (modelUniv t k 3 e Fact.out).K) ∧
        orderOf s = 4 ∧ sl2Inv eS * sl2Inv eR = sl2Inv eR * sl2Inv eS := by
  obtain ⟨s, hsS, hsN, hord⟩ := star_elt3 M hΩ hG2 hD4 hR hS hJ
  obtain ⟨eR⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hR
  obtain ⟨eS⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hS
  have hodd := M.natCard_galoisField_odd (by norm_num)
  exact ⟨eR, eS, s, hsS, hsN, hord, muTab_invol_comm hodd hodd eR eS hsS hsN (a := 2)
    (by rw [hord]; norm_num) (by norm_num)⟩

theorem false_of_linear_star3 {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3) {W U V : Subgroup X} (h : WeakCT.LinearBlockStandardPair F W U V)
    {s : X} (hsV : s ∈ V) (hsN : s ∈ Subgroup.normalizer (U : Set X)) (hord : orderOf s = 4) :
    False := by
  have h2 := linear_pow_card_sub_one3 hF h hsV hsN
  rw [hF] at h2
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at h3
  norm_num at h3

theorem star_trichotomy3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hdich : T3CII.StdDich3 t k)
    {R S : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) :
    Commutes R S ∨ ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R S := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  obtain ⟨eR, eS, s, hsS, hsN, hord, hzcomm⟩ := star_data3 M hΩ hG2 hD4 hR hS hJ
  have hFcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]; norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hFcard]; decide
  have hRl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hR)
  have hSl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hS)
  rcases hdich R hRl S hSl (sl2Inv eR) (sl2Inv eS) (sl2Inv_mem eR) (sl2Inv_mem eS)
    (orderOf_sl2Inv hodd eR) (orderOf_sl2Inv hodd eS) hzcomm.symm with h | h | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact absurd (by rw [h]) hJ.2.1
  · exact Or.inl h
  · exact (false_of_linear_star3 hFcard hW hsS hsN hord).elim
  · exact Or.inr ⟨W, hW⟩

end Star

end CFSG.ClassicalInvolution.Q3.Q3MT
