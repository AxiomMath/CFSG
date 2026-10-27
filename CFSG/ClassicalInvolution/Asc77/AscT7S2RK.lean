module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RB
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RH
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RI
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RJ
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKB
public import CFSG.ClassicalInvolution.Asc77.AscMuTabHubSpin

public section

namespace CFSG.ClassicalInvolution.Asc77.T7S2R

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.MuTab.OrthHub CFSG.LieType.Universal QuadraticMap
open scoped MatrixGroups

section Assembly

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {t : StatedLieTag}
  {k e : ℕ}

theorem Ih8Model.dstarConnected_of_pair (M : Ih8Model p f Ω t k e) (hΩ : HypOmegaMod p f Ω)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {R₁ R₂ : Subgroup (modelUniv t k p e Fact.out).K}
    (hR₁ : R₁ ∈ M.cls) (hadj : dstarAdj Ω (R₁.map M.ψ) (R₂.map M.ψ))
    (hgen : Subgroup.normalizer (R₁ : Set (modelUniv t k p e Fact.out).K) ⊔
      Subgroup.normalizer (R₂ : Set (modelUniv t k p e Fact.out).K) = ⊤) :
    T3.DStarConnected Ω := by
  exact dstarConnected_of_normalizers hΩ.conjInvariant (M.exists_conj_of_fund hG2 hD4)
    (M.map_mem hR₁) (Relation.ReflTransGen.single hadj) (normalizer_map_sup_eq_top M.ψ M.surj hgen)

end Assembly

section Odd

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem Ih8Model.exists_pair_odd [Finite G] (M : Ih8Model p f Ω .POmegaOdd 3 e)
    (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, dstarAdj Ω (R₁.map M.ψ) (R₂.map M.ψ) ∧
      Subgroup.normalizer (R₁ : Set (modelUniv .POmegaOdd 3 p e Fact.out).K) ⊔
        Subgroup.normalizer (R₂ : Set (modelUniv .POmegaOdd 3 p e Fact.out).K) = ⊤ := by
  have hD4 : StatedLieTag.POmegaOdd ≠ .trialityD4 := by decide
  have hG2 : StatedLieTag.POmegaOdd ≠ .G2 := by decide
  have hnpsl : ¬ (StatedLieTag.POmegaOdd = .PSL ∧ (3 : ℕ) = 2) := by simp
  have he : e = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ e := he ▸ hq
  have hadm := M.admissible
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq'
  have he0 : e ≠ 0 := by
    have := hadm.2.1
    omega
  have h5 : 5 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he0]
    exact hq'
  have h7 : 7 ≤ Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have hQ := nondegenerate_polarBilin_quadOdd 3 (GaloisField p e) h2
  have hperf := isPerfect_spinGroup_quadOdd h2 (le_refl 3)
  have hrange := range_spinAction_quadOdd h2 (le_refl 3)
  have S := ModelFacts.spinCtx_pOmegaOdd (p := p) (n := 3) (e := e) (by norm_num) hp2 hq'
  have hodd' : Odd (p ^ f) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hmod : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    rcases hodd' with ⟨k, hk⟩
    omega
  rcases hmod with hq4 | hq3
  · have hab : (0 : Fin 3) ≠ 1 := by decide
    have hbc : (1 : Fin 3) ≠ 2 := by decide
    have hac : (0 : Fin 3) ≠ 2 := by decide
    obtain ⟨R₁, hR₁, e₁⟩ := (fundCorr_odd (p := p) (f := e) hp2 hq' hadm).2
      ((oddFrame 3 (GaloisField p e)).toHypFrame.toFrame hab true true).La.range
      ⟨_, IsFundamental.of_frame _⟩
    obtain ⟨R₂, hR₂, e₂⟩ := (fundCorr_odd (p := p) (f := e) hp2 hq' hadm).2
      ((oddFrame 3 (GaloisField p e)).toHypFrame.toFrame hbc true true).La.range
      ⟨_, IsFundamental.of_frame _⟩
    have hR₁c : R₁ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₁
    have hR₂c : R₂ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₂
    have hL₁ := ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁
    have hL₂ := ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₂
    refine ⟨R₁, hR₁c, R₂, hR₂c, ?_, ?_⟩
    · obtain ⟨W, hW⟩ :=
        linearPair_toFrame hodd (oddFrame 3 (GaloisField p e)).toHypFrame hab hbc hac
      obtain ⟨W', hW'⟩ := S.linear_of_map hL₁ hL₂ ⟨W, by rw [e₁, e₂]; exact hW⟩
      exact M.muTab_dstarAdj_linear hΩ hp2 hq hD4 hnpsl hq4 hR₁c hR₂c hW'
    · have hgen := elementaryGroup_le_normE_sup_toFrame hQ hodd h5 h7
        (oddFrame 3 (GaloisField p e)).toHypFrame hab hbc hac
      exact normalizer_sup_eq_top hperf hrange (S.perf_le hL₁) (S.perf_le hL₂)
        (by rw [e₁, e₂]; exact hgen)
  · have hq3' : p ^ e % 4 = 3 := he ▸ hq3
    have hneg : ¬ IsSquare (-1 : GaloisField p e) :=
      MuTab.not_isSquare_neg_one_galoisField (p := p) (e := e) (by omega) hq3'
    obtain ⟨a₀, b₀, hab₀⟩ := CharP.sq_add_sq (GaloisField p e) p (-1)
    have hab : (a₀ : GaloisField p e) * a₀ + (b₀ : GaloisField p e) * b₀ = -1 := by
      have := hab₀
      push_cast at this
      linear_combination this
    have h4 : (4 : GaloisField p e) ≠ 0 := by
      have : (4 : GaloisField p e) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    have hq4i : 4 * (4 : GaloisField p e)⁻¹ = 1 := mul_inv_cancel₀ h4
    have hh2 : 2 * (2 : GaloisField p e)⁻¹ = 1 := mul_inv_cancel₀ h2
    let S₆ : Sys (quadOdd 3 (GaloisField p e)) := oddSys
    obtain ⟨R₁, hR₁, e₁⟩ := (fundCorr_odd (p := p) (f := e) hp2 hq' hadm).2
      (S₆.hubFrame h2 hab hq4i).La.range ⟨_, IsFundamental.of_frame _⟩
    obtain ⟨R₂, hR₂, e₂⟩ := (fundCorr_odd (p := p) (f := e) hp2 hq' hadm).2
      (S₆.stdFrame h2 hh2).La.range ⟨_, IsFundamental.of_frame _⟩
    have hR₁c : R₁ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₁
    have hR₂c : R₂ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₂
    have hL₁ := ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁
    have hL₂ := ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₂
    refine ⟨R₁, hR₁c, R₂, hR₂c, ?_, ?_⟩
    · have hpair := unitaryPair_hub (K' := GaloisField p (2 * e)) (f := e) S₆ S.card_eq S.card_eq'
        hodd hneg hab hq4i hh2
      obtain ⟨W', hW'⟩ := S.unitary_of_map hL₁ hL₂ ⟨_, by rw [e₁, e₂]; exact hpair⟩
      exact M.muTab_dstarAdj_unitary hΩ hp2 hq hD4 hnpsl hq3 hR₁c hR₂c hW'
    · have hgen := elementaryGroup_le_normE_sup_hub S₆ hQ hodd h5 h7 hab hq4i hh2
      exact normalizer_sup_eq_top hperf hrange (S.perf_le hL₁) (S.perf_le hL₂)
        (by rw [e₁, e₂]; exact hgen)

end Odd

section Minus

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem Ih8Model.exists_pair_minus [Finite G] (M : Ih8Model p f Ω .POmegaMinus 4 e)
    (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, dstarAdj Ω (R₁.map M.ψ) (R₂.map M.ψ) ∧
      Subgroup.normalizer (R₁ : Set (modelUniv .POmegaMinus 4 p e Fact.out).K) ⊔
        Subgroup.normalizer (R₂ : Set (modelUniv .POmegaMinus 4 p e Fact.out).K) = ⊤ := by
  have hD4 : StatedLieTag.POmegaMinus ≠ .trialityD4 := by decide
  have hG2 : StatedLieTag.POmegaMinus ≠ .G2 := by decide
  have hnpsl : ¬ (StatedLieTag.POmegaMinus = .PSL ∧ (4 : ℕ) = 2) := by simp
  have he : e = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ e := he ▸ hq
  have hadm := M.admissible
  have hirr := minusCoeffs_irr p e
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq'
  have he0 : e ≠ 0 := by
    have := hadm.2.1
    omega
  have h5 : 5 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he0]
    exact hq'
  have h7 : 7 ≤ Module.finrank (GaloisField p e)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    norm_num
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 (GaloisField p e) hirr
  have hperf := isPerfect_spinGroup_quadMinus (n := 4) (K := GaloisField p e) (by norm_num) hirr
  have hrange := range_spinAction_quadMinus (n := 4) (K := GaloisField p e) (by norm_num) hirr
  have S := ModelFacts.spinCtx_pOmegaMinus hadm hp2 hq'
  have hodd' : Odd (p ^ f) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hmod : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    rcases hodd' with ⟨k, hk⟩
    omega
  rcases hmod with hq4 | hq3
  · have hab : (⟨0, by norm_num⟩ : Fin (4 - 1)) ≠ ⟨1, by norm_num⟩ := by decide
    have hbc : (⟨1, by norm_num⟩ : Fin (4 - 1)) ≠ ⟨2, by norm_num⟩ := by decide
    have hac : (⟨0, by norm_num⟩ : Fin (4 - 1)) ≠ ⟨2, by norm_num⟩ := by decide
    obtain ⟨R₁, hR₁, e₁⟩ := (fundCorr_minus (p := p) (f := e) hp2 hq' hadm).2
      ((Twisted.minusFrame 4 (minusCoeffs p e).1 (minusCoeffs p e).2).toHypFrame.toFrame hab
        true true).La.range ⟨_, IsFundamental.of_frame _⟩
    obtain ⟨R₂, hR₂, e₂⟩ := (fundCorr_minus (p := p) (f := e) hp2 hq' hadm).2
      ((Twisted.minusFrame 4 (minusCoeffs p e).1 (minusCoeffs p e).2).toHypFrame.toFrame hbc
        true true).La.range ⟨_, IsFundamental.of_frame _⟩
    have hR₁c : R₁ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₁
    have hR₂c : R₂ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₂
    have hL₁ := ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁
    have hL₂ := ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₂
    refine ⟨R₁, hR₁c, R₂, hR₂c, ?_, ?_⟩
    · obtain ⟨W, hW⟩ := linearPair_toFrame hodd
        (Twisted.minusFrame 4 (minusCoeffs p e).1 (minusCoeffs p e).2).toHypFrame hab hbc hac
      obtain ⟨W', hW'⟩ := S.linear_of_map hL₁ hL₂ ⟨W, by rw [e₁, e₂]; exact hW⟩
      exact M.muTab_dstarAdj_linear hΩ hp2 hq hD4 hnpsl hq4 hR₁c hR₂c hW'
    · have hgen := elementaryGroup_le_normE_sup_toFrame hQ hodd h5 h7
        (Twisted.minusFrame 4 (minusCoeffs p e).1 (minusCoeffs p e).2).toHypFrame hab hbc hac
      exact normalizer_sup_eq_top hperf hrange (S.perf_le hL₁) (S.perf_le hL₂)
        (by rw [e₁, e₂]; exact hgen)
  · have hq3' : p ^ e % 4 = 3 := he ▸ hq3
    have hneg : ¬ IsSquare (-1 : GaloisField p e) :=
      MuTab.not_isSquare_neg_one_galoisField (p := p) (e := e) (by omega) hq3'
    obtain ⟨a₀, b₀, hab₀⟩ := CharP.sq_add_sq (GaloisField p e) p (-1)
    have hab : (a₀ : GaloisField p e) * a₀ + (b₀ : GaloisField p e) * b₀ = -1 := by
      have := hab₀
      push_cast at this
      linear_combination this
    have h4 : (4 : GaloisField p e) ≠ 0 := by
      have : (4 : GaloisField p e) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    have hq4i : 4 * (4 : GaloisField p e)⁻¹ = 1 := mul_inv_cancel₀ h4
    have hh2 : 2 * (2 : GaloisField p e)⁻¹ = 1 := mul_inv_cancel₀ h2
    let S₆ : Sys (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2) :=
      minusSys (minusCoeffs p e).1 (minusCoeffs p e).2
    obtain ⟨R₁, hR₁, e₁⟩ := (fundCorr_minus (p := p) (f := e) hp2 hq' hadm).2
      (S₆.hubFrame h2 hab hq4i).La.range ⟨_, IsFundamental.of_frame _⟩
    obtain ⟨R₂, hR₂, e₂⟩ := (fundCorr_minus (p := p) (f := e) hp2 hq' hadm).2
      (S₆.stdFrame h2 hh2).La.range ⟨_, IsFundamental.of_frame _⟩
    have hR₁c : R₁ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₁
    have hR₂c : R₂ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₂
    have hL₁ := ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁
    have hL₂ := ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₂
    refine ⟨R₁, hR₁c, R₂, hR₂c, ?_, ?_⟩
    · have hpair := unitaryPair_hub (K' := GaloisField p (2 * e)) (f := e) S₆ S.card_eq S.card_eq'
        hodd hneg hab hq4i hh2
      obtain ⟨W', hW'⟩ := S.unitary_of_map hL₁ hL₂ ⟨_, by rw [e₁, e₂]; exact hpair⟩
      exact M.muTab_dstarAdj_unitary hΩ hp2 hq hD4 hnpsl hq3 hR₁c hR₂c hW'
    · have hgen := elementaryGroup_le_normE_sup_hub S₆ hQ hodd h5 h7 hab hq4i hh2
      exact normalizer_sup_eq_top hperf hrange (S.perf_le hL₁) (S.perf_le hL₂)
        (by rw [e₁, e₂]; exact hgen)

end Minus

section Final

variable (p f : ℕ) [Fact p.Prime]

theorem ih8S4Star : Ih8S4Star p f := by
  intro hp2 hq G _ _ Ω e hΩ hM
  by_cases hne : Ω.Nonempty
  swap
  · intro K hK
    exact absurd ⟨K, hK⟩ hne
  rcases hM with hM | hM
  · obtain ⟨M⟩ := hM
    obtain ⟨R₁, hR₁, R₂, -, hadj, hgen⟩ := Ih8Model.exists_pair_odd M hΩ hp2 hq hne
    exact Ih8Model.dstarConnected_of_pair M hΩ (by decide) (by decide) hR₁ hadj hgen
  · obtain ⟨M⟩ := hM
    obtain ⟨R₁, hR₁, R₂, -, hadj, hgen⟩ := Ih8Model.exists_pair_minus M hΩ hp2 hq hne
    exact Ih8Model.dstarConnected_of_pair M hΩ (by decide) (by decide) hR₁ hadj hgen

end Final

end CFSG.ClassicalInvolution.Asc77.T7S2R
