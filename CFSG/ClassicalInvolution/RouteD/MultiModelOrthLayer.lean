module

public import CFSG.ClassicalInvolution.RouteD.MultiModelOrthStar
public import CFSG.ClassicalInvolution.RouteD.MultiModelLayer
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem fundSet_layer_eq_of_noOrth (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    (hNo : ∀ F₀ F₁ : OFrame Q, F₁.span ≤ F₀.perp → False) :
    ∀ L ∈ Gaps.fundSet Q, ∀ L₁ ∈ Gaps.fundSet Q, ∀ L₂ ∈ Gaps.fundSet Q, Commutes L L₁ →
      Commutes L L₂ → L₁ = L₂ := by
  rintro L ⟨i, hL⟩ L₁ ⟨i₁, hL₁⟩ L₂ ⟨i₂, hL₂⟩ c1 c2
  have hn0 := not_commutes_self_of_isFundamental hodd h4 hL
  obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin hodd hL
  have key : ∀ {M : Subgroup (V ≃ₗ[K] V)} {j : V ≃ₗ[K] V}, IsFundamental Q M j →
      Commutes L M → M = L' := by
    intro M j hM hc
    rcases Gaps.orth_or_twin hodd hL hM hc with horth | heq
    · exfalso
      obtain ⟨F₀, -, hi₀⟩ := hL
      obtain ⟨F₁, -, hj⟩ := hM
      rw [hi₀, hj] at horth
      exact hNo F₀ F₁ (Exotic.span_le_perp_of_negSpace hodd horth)
    · subst heq
      rcases huniq M hM with h | h
      · exact absurd (h ▸ hc) hn0
      · exact h
  rw [key hL₁ c1, key hL₂ c2]

variable [FiniteDimensional K V]

theorem fundSet_layer_eq_or_commutes_eight (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    (hdim : Module.finrank K V = 8) :
    ∀ L ∈ Gaps.fundSet Q, ∀ L₁ ∈ Gaps.fundSet Q, ∀ L₂ ∈ Gaps.fundSet Q, Commutes L L₁ →
      Commutes L L₂ → L₁ = L₂ ∨ Commutes L₁ L₂ := by
  rintro L ⟨i, hL⟩ L₁ ⟨i₁, hL₁⟩ L₂ ⟨i₂, hL₂⟩ h01 h02
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hn0 := not_commutes_self_of_isFundamental hodd h4 hL
  have hne01 : L ≠ L₁ := fun h => hn0 (h ▸ h01)
  have hne02 : L ≠ L₂ := fun h => hn0 (h ▸ h02)
  obtain ⟨F₀, rfl, rfl⟩ := hL
  obtain ⟨F₁, rfl, rfl⟩ := hL₁
  obtain ⟨F₂, rfl, rfl⟩ := hL₂
  have twin : ∀ {G H : OFrame Q}, H.La (-1) = G.La (-1) → H.La.range ≠ G.La.range →
      H.La.range = G.swap.La.range := fun hh hne =>
    (Frame.La_range_eq_or_eq_swap h2 hh).resolve_left hne
  have hperp : ∀ {G H : OFrame Q}, SpanOrth G H → H.span = G.perp := by
    intro G H h
    have hle : H.span ≤ G.perp := (Exotic.span_le_perp_iff G H).mpr h
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have h4' := ModelFacts.finrank_perp_add_four G
    rw [H.finrank_span]
    omega
  have hcommSwap : ∀ {G H : OFrame Q}, SpanOrth G H → Commutes G.swap.La.range H.La.range := by
    intro G H h
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact Frame.La_comm_of_orth (F := G.swap) (F' := H) (fun X Y => by
      rw [Frame.incl_swap]; exact h _ Y) A B
  have hcommTwin : ∀ G : OFrame Q, Commutes G.swap.La.range G.La.range := by
    intro G
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact (G.La_comm_La_swap B A).symm
  rcases spanOrth_or_eq h2 h01 with o01 | c1
  · rcases spanOrth_or_eq h2 h02 with o02 | c2
    · have hs : F₂.span = F₁.span := (hperp o02).trans (hperp o01).symm
      rcases La_range_twin_of_span_eq h2 hs with e | e
      · exact Or.inl e
      · right
        rw [e]
        exact hcommTwin F₂
    · right
      rw [twin c2 (Ne.symm hne02)]
      exact (hcommSwap o01).symm
  · rcases spanOrth_or_eq h2 h02 with o02 | c2
    · right
      rw [twin c1 (Ne.symm hne01)]
      exact hcommSwap o02
    · left
      rw [twin c1 (Ne.symm hne01), twin c2 (Ne.symm hne02)]

end Geometry

section Transfer

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)}

theorem layer_of_map (hker : π.ker ≤ Subgroup.center KY) (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓕')
    (hgeo : ∀ L ∈ 𝓕', ∀ L₁ ∈ 𝓕', ∀ L₂ ∈ 𝓕', Commutes L L₁ → Commutes L L₂ →
      L₁ = L₂ ∨ Commutes L₁ L₂) :
    ∀ R ∈ 𝓕, ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, Commutes R R₁ → Commutes R R₂ → R₁ = R₂ ∨ Commutes R₁ R₂ := by
  intro R hR R₁ hR₁ R₂ hR₂ c1 c2
  have hci : ∀ {A B : Subgroup KY}, A ∈ 𝓕 → (Commutes (A.map π) (B.map π) ↔ Commutes A B) :=
    fun hA => Gaps.commutes_map_iff hker (hperf _ hA)
  rcases hgeo _ (hmap R hR) _ (hmap R₁ hR₁) _ (hmap R₂ hR₂) ((hci hR).mpr c1)
    ((hci hR).mpr c2) with h | h
  · exact Or.inl (ModelFacts.eq_of_map_eq_of_isPerfect π hker (hperf _ hR₁) (hperf _ hR₂) h)
  · exact Or.inr ((hci hR₁).mp h)

end Transfer

section Models

variable {p : ℕ} [Fact p.Prime]

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic

theorem modelLayer_pOmegaOdd {e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    ∀ R ∈ ModelFund p .POmegaOdd 3 e, ∀ R₁ ∈ ModelFund p .POmegaOdd 3 e,
      ∀ R₂ ∈ ModelFund p .POmegaOdd 3 e, Commutes R R₁ → Commutes R R₂ →
      R₁ = R₂ ∨ Commutes R₁ R₂ := by
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have : Finite (spinGroup (quadOdd 3 (GaloisField p e))) :=
    ModelFacts.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have hCQ := Gaps.centralQuot_odd hp2 (le_refl 3) hq
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  refine layer_of_map (KY := spinGroup (quadOdd 3 (GaloisField p e))) hCQ.ker_le hCQ.perf
    hCQ.map_mem ?_
  intro L hL L₁ hL₁ L₂ hL₂ c1 c2
  refine Or.inl (fundSet_layer_eq_of_noOrth hodd h4 (fun F₀ F₁ h => ?_) L hL L₁ hL₁ L₂ hL₂ c1 c2)
  have hle := Submodule.finrank_mono h
  rw [F₁.finrank_span] at hle
  have h4' := ModelFacts.finrank_perp_add_four F₀
  omega

theorem modelLayer_pOmegaPlus {e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    ∀ R ∈ ModelFund p .POmegaPlus 4 e, ∀ R₁ ∈ ModelFund p .POmegaPlus 4 e,
      ∀ R₂ ∈ ModelFund p .POmegaPlus 4 e, Commutes R R₁ → Commutes R R₂ →
      R₁ = R₂ ∨ Commutes R₁ R₂ := by
  have h3 : 3 ≤ 4 := by omega
  have h : modelUniv .POmegaPlus 4 p e Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) h3⟩ :=
    RouteD.modelUniv_POmegaPlus_eq h3
  unfold ModelFund
  generalize modelUniv .POmegaPlus 4 p e Fact.out = L at h ⊢
  subst h
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have : Finite (spinGroup (quadPlus 4 (GaloisField p e))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hCQ := Gaps.centralQuot_plus hp2 (le_refl 4) h3 hq
  have hdim : Module.finrank (GaloisField p e) (Fin 4 ⊕ Fin 4 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  exact layer_of_map hCQ.ker_le hCQ.perf hCQ.map_mem (fundSet_layer_eq_or_commutes_eight hodd h4 hdim)

theorem modelLayer_pOmegaMinus {e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p e) :
    ∀ R ∈ ModelFund p .POmegaMinus 4 e, ∀ R₁ ∈ ModelFund p .POmegaMinus 4 e,
      ∀ R₂ ∈ ModelFund p .POmegaMinus 4 e, Commutes R R₁ → Commutes R R₂ →
      R₁ = R₂ ∨ Commutes R₁ R₂ := by
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hCtx := ModelFacts.spinCtx_pOmegaMinus hadm hp2 hq
  have hY := RouteD.yData_minus (p := p) (f := e) (le_refl 4) hp2 hadm (by omega)
  have hF := Exotic.fundCorr_minus (p := p) (f := e) hp2 hq hadm
  have := hCtx.fin
  refine layer_of_map
    (KY := spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2))
    (ker_spinAction_le_center _)
    (fun R hR => le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
      R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) (hY.perfR R hR))
    hF.1 ?_
  intro L hL L₁ hL₁ L₂ hL₂ c1 c2
  exact Or.inl (fundSet_layer_eq_of_noOrth hodd h4 (fun F₀ F₁ hF' =>
    Exotic.false_of_orth_quadMinus_four (ModelFacts.two_ne_zero_galoisField e hp2)
      (minusCoeffs_irr p e) h4 F₀ F₁ hF') L hL L₁ hL₁ L₂ hL₂ c1 c2)

end Models

end CFSG.ClassicalInvolution.RouteD
