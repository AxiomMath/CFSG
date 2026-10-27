module

public import CFSG.ClassicalInvolution.Q3.Q3WAMOrth
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Asc77.AscMuTabHubSpin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Universal.Spin.Twisted
open scoped MatrixGroups




section Transfer

variable {p e : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p e) V]
  [FiniteDimensional (GaloisField p e) V] {Q : QuadraticForm (GaloisField p e) V}
  {𝓕 : Set (Subgroup (spinGroup Q))}

theorem layer_eq_of_ctx3 (S : SpinCtx3 p e Q 𝓕)
    (hgeo : ∀ L ∈ Gaps.fundSet Q, ∀ L₁ ∈ Gaps.fundSet Q, ∀ L₂ ∈ Gaps.fundSet Q,
      Commutes L L₁ → Commutes L L₂ → L₁ = L₂) :
    ∀ R ∈ 𝓕, ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, Commutes R R₁ → Commutes R R₂ → R₁ = R₂ := by
  intro R hR R₁ hR₁ R₂ hR₂ c1 c2
  have hc : ∀ {A B : Subgroup (spinGroup Q)}, Commutes A B →
      Commutes (A.map (spinAction Q)) (B.map (spinAction Q)) := by
    rintro A B h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h a ha b hb]
  exact S.eq_of_map_eq hR₁ hR₂
    (hgeo _ (S.map R hR) _ (S.map R₁ hR₁) _ (S.map R₂ hR₂) (hc c1) (hc c2))

end Transfer

section Layers

theorem modelLayerEq_pOmegaOdd3 :
    ∀ R ∈ ModelFund 3 .POmegaOdd 3 1, ∀ R₁ ∈ ModelFund 3 .POmegaOdd 3 1,
      ∀ R₂ ∈ ModelFund 3 .POmegaOdd 3 1, Commutes R R₁ → Commutes R R₂ → R₁ = R₂ := by
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hM : Generic.modelUniv .POmegaOdd 3 3 1 Fact.out =
      ⟨spinGroup (quadOdd 3 (GaloisField 3 1)), oddDatum 3 (GaloisField 3 1)⟩ := rfl
  unfold ModelFund
  generalize Generic.modelUniv .POmegaOdd 3 3 1 Fact.out = M at hM ⊢
  subst hM
  have hodd := odd_gf3
  have hdim : Module.finrank (GaloisField 3 1) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField 3 1) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have S := spinCtx3_mono (spinCtx3_pOmegaOdd hadm (by norm_num))
    (fundamentalSubgroups_subset_longest (t := .POmegaOdd) (by decide) (by decide) _)
  refine layer_eq_of_ctx3 S (fun L hL L₁ hL₁ L₂ hL₂ c1 c2 =>
    fundSet_layer_eq_of_noOrth3 hodd (fun F₀ F₁ h => ?_) L hL L₁ hL₁ L₂ hL₂ c1 c2)
  have hle := Submodule.finrank_mono h
  rw [F₁.finrank_span] at hle
  have h4' := ModelFacts.finrank_perp_add_four F₀
  omega

theorem modelLayerEq_pOmegaMinus3 :
    ∀ R ∈ ModelFund 3 .POmegaMinus 4 1, ∀ R₁ ∈ ModelFund 3 .POmegaMinus 4 1,
      ∀ R₂ ∈ ModelFund 3 .POmegaMinus 4 1, Commutes R R₁ → Commutes R R₂ → R₁ = R₂ := by
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hM : Generic.modelUniv .POmegaMinus 4 3 1 Fact.out =
      ⟨spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum 4 (minusCoeffs_irr 3 1)⟩ := rfl
  unfold ModelFund
  generalize Generic.modelUniv .POmegaMinus 4 3 1 Fact.out = M at hM ⊢
  subst hM
  have hodd := odd_gf3
  have S := spinCtx3_mono (spinCtx3_pOmegaMinus hadm (by norm_num))
    (fundamentalSubgroups_subset_longest (t := .POmegaMinus) (by decide) (by decide) _)
  refine layer_eq_of_ctx3 S (fun L hL L₁ hL₁ L₂ hL₂ c1 c2 =>
    fundSet_layer_eq_of_noOrth3 hodd (fun F₀ F₁ hF' => ?_) L hL L₁ hL₁ L₂ hL₂ c1 c2)
  exact ModelFacts.TG3.false_of_orth_quadMinus_four3 two_ne_zero_gf3 (minusCoeffs_irr 3 1)
    (by rw [card_gf3]; norm_num) F₀ F₁ hF'

end Layers

section Hub

open CFSG.ClassicalInvolution.Asc77.MuTab

@[expose] noncomputable def tvP {K : Type} [Field K] (i : Fin 4) : Fin 4 ⊕ Fin 4 → K :=
  Pi.single (.inl i) 1 + Pi.single (.inr i) 1

@[expose] noncomputable def svP {K : Type} [Field K] (i : Fin 4) : Fin 4 ⊕ Fin 4 → K :=
  Pi.single (.inl i) 1 - Pi.single (.inr i) 1

@[expose] noncomputable def plusSys {K : Type} [Field K] : OrthHub.Sys (quadPlus 4 K) where
  o := ![tvP 0, tvP 1, tvP 2, tvP 3, svP 0, svP 1]
  sq := by
    intro i
    fin_cases i <;> simp [quadPlus_apply, tvP, svP, OrthHub.eps, Pi.single_apply]
  orth := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (rw [polar_quadPlus]; simp [tvP, svP, Pi.single_apply, Fin.sum_univ_four])

theorem exists_unitaryPair_odd3 :
    ∃ R₁ ∈ ModelFund 3 .POmegaOdd 3 1, ∃ R₂ ∈ ModelFund 3 .POmegaOdd 3 1,
      ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂ := by
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hM : Generic.modelUniv .POmegaOdd 3 3 1 Fact.out =
      ⟨spinGroup (quadOdd 3 (GaloisField 3 1)), oddDatum 3 (GaloisField 3 1)⟩ := rfl
  unfold ModelFund
  generalize Generic.modelUniv .POmegaOdd 3 3 1 Fact.out = M at hM ⊢
  subst hM
  have hodd := odd_gf3
  have S := spinCtx3_mono (spinCtx3_pOmegaOdd hadm (by norm_num))
    (fundamentalSubgroups_subset_longest (t := .POmegaOdd) (by decide) (by decide) _)
  obtain ⟨fr₁, fr₂, hpair⟩ := OrthHub.exists_unitaryPair (K := GaloisField 3 1)
    (K' := GaloisField 3 2) (p := 3) (f := 1) OrthHub.oddSys S.card_eq S.card_eq' S.odd_card
    (Asc77.MuTab.not_isSquare_neg_one_galoisField S.one_le (by norm_num))
  obtain ⟨R₁, hR₁, e₁⟩ := Gaps.exists_map_eq_odd (by norm_num : 3 ≤ 3) hodd
    (⟨_, IsFundamental.of_frame fr₁⟩ : fr₁.La.range ∈ Gaps.fundSet (quadOdd 3 (GaloisField 3 1)))
  obtain ⟨R₂, hR₂, e₂⟩ := Gaps.exists_map_eq_odd (by norm_num : 3 ≤ 3) hodd
    (⟨_, IsFundamental.of_frame fr₂⟩ : fr₂.La.range ∈ Gaps.fundSet (quadOdd 3 (GaloisField 3 1)))
  refine ⟨R₁, hR₁, R₂, hR₂, S.unitary_of_map hR₁ hR₂ ⟨fr₁.La.range ⊔ fr₂.La.range, ?_⟩⟩
  rw [e₁, e₂]
  exact hpair

theorem exists_unitaryPair_minus3 :
    ∃ R₁ ∈ ModelFund 3 .POmegaMinus 4 1, ∃ R₂ ∈ ModelFund 3 .POmegaMinus 4 1,
      ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂ := by
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hM : Generic.modelUniv .POmegaMinus 4 3 1 Fact.out =
      ⟨spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum 4 (minusCoeffs_irr 3 1)⟩ := rfl
  have hF := Exotic.fundCorr_minus3 (p := 3) (f := 1) (by norm_num) hadm
  unfold ModelFund
  generalize Generic.modelUniv .POmegaMinus 4 3 1 Fact.out = M at hM ⊢
  subst hM
  have S := spinCtx3_mono (spinCtx3_pOmegaMinus hadm (by norm_num))
    (fundamentalSubgroups_subset_longest (t := .POmegaMinus) (by decide) (by decide) _)
  obtain ⟨fr₁, fr₂, hpair⟩ := OrthHub.exists_unitaryPair (K := GaloisField 3 1)
    (K' := GaloisField 3 2) (p := 3) (f := 1)
    (OrthHub.minusSys (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) S.card_eq S.card_eq' S.odd_card
    (Asc77.MuTab.not_isSquare_neg_one_galoisField S.one_le (by norm_num))
  obtain ⟨R₁, hR₁, e₁⟩ := hF.2 fr₁.La.range ⟨_, IsFundamental.of_frame fr₁⟩
  obtain ⟨R₂, hR₂, e₂⟩ := hF.2 fr₂.La.range ⟨_, IsFundamental.of_frame fr₂⟩
  refine ⟨R₁, hR₁, R₂, hR₂, S.unitary_of_map hR₁ hR₂ ⟨fr₁.La.range ⊔ fr₂.La.range, ?_⟩⟩
  rw [e₁, e₂]
  exact hpair

theorem exists_unitaryPair_plus3 :
    ∃ R₁ ∈ ModelFund 3 .POmegaPlus 4 1, ∃ R₂ ∈ ModelFund 3 .POmegaPlus 4 1,
      ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂ := by
  have h3 : 3 ≤ 4 := by omega
  have hn : 4 ≤ 4 := le_rfl
  have h : Generic.modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) h3⟩ :=
    RouteD.modelUniv_POmegaPlus_eq h3
  unfold ModelFund
  generalize Generic.modelUniv .POmegaPlus 4 3 1 Fact.out = L at h ⊢
  subst h
  have hodd := odd_gf3
  have S := spinCtx3_mono (spinCtx3_pOmegaPlus (p := 3) (n := 4) (e := 1) hn (by norm_num))
    (fundamentalSubgroups_subset_longest (t := .POmegaPlus) (by decide) (by decide) _)
  obtain ⟨fr₁, fr₂, hpair⟩ := OrthHub.exists_unitaryPair (K := GaloisField 3 1)
    (K' := GaloisField 3 2) (p := 3) (f := 1) plusSys S.card_eq S.card_eq' S.odd_card
    (Asc77.MuTab.not_isSquare_neg_one_galoisField S.one_le (by norm_num))
  obtain ⟨R₁, hR₁, e₁⟩ := Gaps.exists_map_eq h3 hodd
    (⟨_, IsFundamental.of_frame fr₁⟩ : fr₁.La.range ∈ Gaps.fundSet (quadPlus 4 (GaloisField 3 1)))
  obtain ⟨R₂, hR₂, e₂⟩ := Gaps.exists_map_eq h3 hodd
    (⟨_, IsFundamental.of_frame fr₂⟩ : fr₂.La.range ∈ Gaps.fundSet (quadPlus 4 (GaloisField 3 1)))
  refine ⟨R₁, hR₁, R₂, hR₂, S.unitary_of_map hR₁ hR₂ ⟨fr₁.La.range ⊔ fr₂.La.range, ?_⟩⟩
  rw [e₁, e₂]
  exact hpair

end Hub

end CFSG.ClassicalInvolution.Q3.Q3W
