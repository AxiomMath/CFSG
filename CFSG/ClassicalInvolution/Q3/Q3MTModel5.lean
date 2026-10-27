module

public import CFSG.ClassicalInvolution.Q3.Q3MTModel4
public import CFSG.ClassicalInvolution.Q3.Q3WAMBase
public import CFSG.ClassicalInvolution.Asc77.AscMuTabEdge
public import CFSG.ClassicalInvolution.Q3.Q3MTModel2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped MatrixGroups


section StarEdge

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}

theorem mem_omegaStarNbr_of_cyclic3 {K J T : Subgroup G} (hJ : J ∈ Ω) (hJcard : Nat.card J = 24)
    (hne : J ≠ K) (hTJ : T ≤ J) (hT2 : IsPGroup 2 T) (hTc : IsCyclic ↥T) (hT4 : Nat.card T = 4)
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) : J ∈ omegaStarNbr Ω K := by
  obtain ⟨R, -, hRJ, hTR⟩ := exists_mem_RSet_ge hJ hT2 hTJ
  have hRcard : Nat.card R = 8 := by
    rw [natCard_isSylow2In_of_card hRJ, hJcard]
    exact two_pow_factorization_24
  have hU : T ∈ USet Ω := mem_USet_of_natCard hJ hRJ hTR hTc (by rw [hRcard, hT4])
  exact ⟨hJ, hne, T, hU, hTJ, hTN⟩

theorem dstarAdj_of_torus3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {R₁ R₂ : Subgroup (modelUniv t k 3 e Fact.out).K}
    (hR₁ : R₁ ∈ M.cls) (hR₂ : R₂ ∈ M.cls) (hne : R₁ ≠ R₂) {v : (modelUniv t k 3 e Fact.out).K}
    (hv : v ∈ R₂) (hvN : v ∈ Subgroup.normalizer (R₁ : Set _)) (hv4 : orderOf v = 4) :
    dstarAdj Ω (R₁.map M.ψ) (R₂.map M.ψ) := by
  have hord : orderOf (M.ψ v) = 4 := by
    rw [orderOf_map_of_injOn M.ψ (injOn_map3 M hΩ hG2 hD4 hR₂) hv, hv4]
  have hcardT : Nat.card (Subgroup.zpowers (M.ψ v)) = 4 := by
    rw [Nat.card_zpowers, hord]
  have hT2 : IsPGroup 2 (Subgroup.zpowers (M.ψ v)) :=
    IsPGroup.of_card (n := 2) (by rw [hcardT]; norm_num)
  have hne' : R₂.map M.ψ ≠ R₁.map M.ψ := fun h => hne (map_inj3 M hG2 hD4 hR₁ hR₂ h.symm)
  exact ⟨M.map_mem hR₂, Or.inl (mem_omegaStarNbr_of_cyclic3 (M.map_mem hR₂)
    (card_map3 M hΩ hG2 hD4 hR₂) hne' (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hv))
    hT2 inferInstance hcardT
    (Subgroup.zpowers_le.mpr (muTab_mem_normalizer_map M.ψ hvN)))⟩

theorem unitary_ne_nc3 (M : Ih8Model 3 1 Ω t k e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R₁ R₂ : Subgroup (modelUniv t k 3 e Fact.out).K} (hR₁ : R₁ ∈ M.cls) (hR₂ : R₂ ∈ M.cls)
    {W : Subgroup (modelUniv t k 3 e Fact.out).K}
    (hW : Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂) :
    R₁ ≠ R₂ ∧ ¬ Commutes R₁ R₂ := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 2 (by norm_num)]; norm_num
  have hne : R₁ ≠ R₂ := by
    intro h
    refine Q3W.not_commutes_self_modelFund3 M.isFundTag M.admissible hG2 hD4 (M.cls_sub hR₂)
      fun x hx y hy => ?_
    have hN : ∀ z ∈ R₂, z ∈ Subgroup.normalizer (R₁ : Set _) := fun z hz => by
      rw [h]
      exact Subgroup.le_normalizer hz
    exact UnitaryBlockStandardPair.comm_of_normalizes3 hK (by norm_num) hW hx hy (hN x hx)
      (hN y hy)
  refine ⟨hne, fun hc => ?_⟩
  have hbot : R₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact unitaryPair_eq_one_of_centralizes3 hK (by norm_num) hW hx fun y hy => hc x hx y hy
  refine Q3W.not_commutes_self_modelFund3 M.isFundTag M.admissible hG2 hD4 (M.cls_sub hR₁) ?_
  intro a ha b hb
  rw [hbot, Subgroup.mem_bot] at ha
  rw [ha, one_mul, mul_one]

theorem dstarAdj_unitary3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {R₁ R₂ : Subgroup (modelUniv t k 3 e Fact.out).K}
    (hR₁ : R₁ ∈ M.cls) (hR₂ : R₂ ∈ M.cls)
    {W : Subgroup (modelUniv t k 3 e Fact.out).K}
    (hW : Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂) :
    dstarAdj Ω (R₁.map M.ψ) (R₂.map M.ψ) := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 2 (by norm_num)]; norm_num
  obtain ⟨hne, -⟩ := unitary_ne_nc3 M hG2 hD4 hR₁ hR₂ hW
  obtain ⟨u, hu⟩ := MuTab.exists_orderOf_two_part
    (normOne (unitaryInvolution (GaloisField 3 2) 3 1))
  obtain ⟨v, hvV, hvN, hvo⟩ := UnitaryBlockStandardPair.muTab_exists_torus_elt hK hW u
  have hcardN : Nat.card (normOne (unitaryInvolution (GaloisField 3 2) 3 1)) = 4 := by
    rw [Phan.card_normOne hK]
    norm_num
  have hfac : (Nat.factorization 4) 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hu4 : orderOf u = 4 := by
    rw [hu, hcardN, hfac]
    norm_num
  exact dstarAdj_of_torus3 M hΩ hG2 hD4 hR₁ hR₂ hne hvV hvN (hvo.trans hu4)

theorem edge_of_commuting3 (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hne : Ω.Nonempty) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (h : ∃ R ∈ ModelFund 3 t k e, ∃ S ∈ ModelFund 3 t k e, Commutes R S) :
    ∃ K ∈ Ω, (omegaNbr Ω K).Nonempty := by
  obtain ⟨R, hR, S, hS, hc⟩ := h
  have hR' := M.fund_subset_cls hne hG2 hD4 hR
  have hS' := M.fund_subset_cls hne hG2 hD4 hS
  refine edge3 M hΩ hG2 hD4 ⟨R, hR', S, hS', ?_, hc⟩
  intro hRS
  exact ne_of_commutes_members hΩ (M.map_mem hR') (ih8_commutes_map M.ψ hc) (by rw [hRS])

end StarEdge

end CFSG.ClassicalInvolution.Q3.Q3MT
