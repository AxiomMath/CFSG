module

public import CFSG.ClassicalInvolution.Q3.Q3WAMBase
public import CFSG.ClassicalInvolution.RouteD.MultiModelOrthGeom
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthLayer
public import CFSG.ClassicalInvolution.Asc77.AscR10E24
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WAStarMain
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

omit [Finite K] in
theorem not_commutes_self_of_isFundamental3 {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (h : IsFundamental Q L i) : ¬ Commutes L L := by
  obtain ⟨F, rfl, -⟩ := h
  exact NonClassical.not_commutes_self_range F

theorem fundSet_layer_eq_of_noOrth3 (hodd : Odd (Nat.card K))
    (hNo : ∀ F₀ F₁ : OFrame Q, F₁.span ≤ F₀.perp → False) :
    ∀ L ∈ Gaps.fundSet Q, ∀ L₁ ∈ Gaps.fundSet Q, ∀ L₂ ∈ Gaps.fundSet Q, Commutes L L₁ →
      Commutes L L₂ → L₁ = L₂ := by
  rintro L ⟨i, hL⟩ L₁ ⟨i₁, hL₁⟩ L₂ ⟨i₂, hL₂⟩ c1 c2
  have hn0 := not_commutes_self_of_isFundamental3 hL
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

theorem fundSet_layer_eq_or_commutes_eight3 (hodd : Odd (Nat.card K))
    (hdim : Module.finrank K V = 8) :
    ∀ L ∈ Gaps.fundSet Q, ∀ L₁ ∈ Gaps.fundSet Q, ∀ L₂ ∈ Gaps.fundSet Q, Commutes L L₁ →
      Commutes L L₂ → L₁ = L₂ ∨ Commutes L₁ L₂ := by
  rintro L ⟨i, hL⟩ L₁ ⟨i₁, hL₁⟩ L₂ ⟨i₂, hL₂⟩ h01 h02
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hn0 := not_commutes_self_of_isFundamental3 hL
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

omit [FiniteDimensional K V] in
theorem orth_star_dichotomy3 (hodd : Odd (Nat.card K))
    {L L₁ L₂ : Subgroup (V ≃ₗ[K] V)} {i i₁ i₂ : V ≃ₗ[K] V}
    (hL : IsFundamental Q L i) (hL₁ : IsFundamental Q L₁ i₁) (hL₂ : IsFundamental Q L₂ i₂)
    (h01 : Commutes L L₁) (h02 : Commutes L L₂) (h12 : Commutes L₁ L₂) :
    (∃ Lβ : Subgroup (V ≃ₗ[K] V), (∃ j, IsFundamental Q Lβ j) ∧
        (∃ W, LinearBlockStandardPair K W L Lβ) ∧ (∃ W, LinearBlockStandardPair K W L₁ Lβ) ∧
        (∃ W, LinearBlockStandardPair K W L₂ Lβ)) ∨
      ∃ L₃ : Subgroup (V ≃ₗ[K] V), (∃ j, IsFundamental Q L₃ j) ∧ Commutes L L₃ ∧
        ¬ Commutes L₁ L₃ ∧ ¬ Commutes L₂ L₃ := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hn0 := not_commutes_self_of_isFundamental3 hL
  have hn1 := not_commutes_self_of_isFundamental3 hL₁
  have hne01 : L ≠ L₁ := fun h => hn0 (h ▸ h01)
  have hne02 : L ≠ L₂ := fun h => hn0 (h ▸ h02)
  have hne12 : L₁ ≠ L₂ := fun h => hn1 (h ▸ h12)
  obtain ⟨F₀, rfl, rfl⟩ := hL
  obtain ⟨F₁, rfl, rfl⟩ := hL₁
  obtain ⟨F₂, rfl, rfl⟩ := hL₂
  have twin : ∀ {G H : Frame Q}, H.La (-1) = G.La (-1) → H.La.range ≠ G.La.range →
      H.La.range = G.swap.La.range := fun hh hne =>
    (Frame.La_range_eq_or_eq_swap h2 hh).resolve_left hne
  have E01 := spanOrth_or_eq h2 h01
  have E02 := spanOrth_or_eq h2 h02
  have E12 := spanOrth_or_eq h2 h12
  by_cases c1 : F₁.La (-1) = F₀.La (-1)
  · have t1 : F₁.La.range = F₀.swap.La.range := twin c1 (Ne.symm hne01)
    rcases E02 with o02 | c2
    · left
      obtain ⟨Fβ, hA, hB, -⟩ := cross_partner h2 o02
      exact ⟨Fβ.La.range, ⟨_, IsFundamental.of_frame Fβ⟩, hA _ (Or.inl rfl), hA _ (Or.inr t1),
        hB _ (Or.inl rfl)⟩
    · exfalso
      rcases Frame.La_range_eq_or_eq_swap h2 c2 with e | e
      · exact hne02 e.symm
      · exact hne12 (t1.trans e.symm)
  have o01 : SpanOrth F₀ F₁ := E01.resolve_right c1
  by_cases c2 : F₂.La (-1) = F₀.La (-1)
  · have t2 : F₂.La.range = F₀.swap.La.range := twin c2 (Ne.symm hne02)
    left
    obtain ⟨Fβ, hA, hB, -⟩ := cross_partner h2 o01
    exact ⟨Fβ.La.range, ⟨_, IsFundamental.of_frame Fβ⟩, hA _ (Or.inl rfl), hB _ (Or.inl rfl),
      hA _ (Or.inr t2)⟩
  have o02 : SpanOrth F₀ F₂ := E02.resolve_right c2
  by_cases c3 : F₂.La (-1) = F₁.La (-1)
  · have t3 : F₂.La.range = F₁.swap.La.range := twin c3 (Ne.symm hne12)
    left
    obtain ⟨Fβ, hA, hB, -⟩ := cross_partner h2 o01.symm
    exact ⟨Fβ.La.range, ⟨_, IsFundamental.of_frame Fβ⟩, hB _ (Or.inl rfl), hA _ (Or.inl rfl),
      hA _ (Or.inr t3)⟩
  have o12 : SpanOrth F₁ F₂ := E12.resolve_right c3
  right
  obtain ⟨Fβ, hA, hB, hH⟩ := cross_partner h2 o12
  refine ⟨Fβ.La.range, ⟨_, IsFundamental.of_frame Fβ⟩, ?_, ?_, ?_⟩
  · have hS := hH F₀ o01 o02
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact Frame.La_comm_of_orth hS A B
  · obtain ⟨W, hW⟩ := hA _ (Or.inl rfl)
    exact not_commutes_of_linearBlockStandardPair hW
  · obtain ⟨W, hW⟩ := hB _ (Or.inl rfl)
    exact not_commutes_of_linearBlockStandardPair hW

omit [FiniteDimensional K V] in
theorem fundSet_star3 (hodd : Odd (Nat.card K)) :
    ∀ L ∈ Gaps.fundSet Q, ∀ L₁ ∈ Gaps.fundSet Q, ∀ L₂ ∈ Gaps.fundSet Q, Commutes L L₁ →
      Commutes L L₂ → Commutes L₁ L₂ →
      (∃ Lβ ∈ Gaps.fundSet Q, (∃ W, LinearBlockStandardPair K W L Lβ) ∧
        (∃ W, LinearBlockStandardPair K W L₁ Lβ) ∧ (∃ W, LinearBlockStandardPair K W L₂ Lβ)) ∨
      ∃ L₃ ∈ Gaps.fundSet Q, Commutes L L₃ ∧ ¬ Commutes L₁ L₃ ∧ ¬ Commutes L₂ L₃ := by
  rintro L ⟨i, hL⟩ L₁ ⟨i₁, hL₁⟩ L₂ ⟨i₂, hL₂⟩ h01 h02 h12
  rcases orth_star_dichotomy3 hodd hL hL₁ hL₂ h01 h02 h12 with
    ⟨Lβ, ⟨j, hj⟩, a, b, c⟩ | ⟨L₃, ⟨j, hj⟩, a, b, c⟩
  · exact Or.inl ⟨Lβ, ⟨j, hj⟩, a, b, c⟩
  · exact Or.inr ⟨L₃, ⟨j, hj⟩, a, b, c⟩

end Geometry

section Transfer

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts

variable {p e : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p e) V]
  [FiniteDimensional (GaloisField p e) V] {Q : QuadraticForm (GaloisField p e) V}
  {𝓕 : Set (Subgroup (spinGroup Q))}

theorem spinCtx3_mono {𝔉 𝔉' : Set (Subgroup (spinGroup Q))} (S : SpinCtx3 p e Q 𝔉)
    (h : 𝔉' ⊆ 𝔉) : SpinCtx3 p e Q 𝔉' :=
  ⟨S.h3, S.hQ, S.fin, S.hker2, S.hC, fun R hR => S.inj R (h hR), fun R hR => S.map R (h hR)⟩




theorem layer_of_ctx3 (S : SpinCtx3 p e Q 𝓕)
    (hgeo : ∀ L ∈ Gaps.fundSet Q, ∀ L₁ ∈ Gaps.fundSet Q, ∀ L₂ ∈ Gaps.fundSet Q,
      Commutes L L₁ → Commutes L L₂ → L₁ = L₂ ∨ Commutes L₁ L₂) :
    ∀ R ∈ 𝓕, ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, Commutes R R₁ → Commutes R R₂ →
      R₁ = R₂ ∨ Commutes R₁ R₂ := by
  intro R hR R₁ hR₁ R₂ hR₂ c1 c2
  have hc : ∀ {A B : Subgroup (spinGroup Q)}, Commutes A B →
      Commutes (A.map (spinAction Q)) (B.map (spinAction Q)) := by
    rintro A B h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h a ha b hb]
  rcases hgeo _ (S.map R hR) _ (S.map R₁ hR₁) _ (S.map R₂ hR₂) (hc c1) (hc c2) with h | h
  · exact Or.inl (S.eq_of_map_eq hR₁ hR₂ h)
  · exact Or.inr (S.commutes_of_map hR₁ h)

theorem star_of_ctx3 (S : SpinCtx3 p e Q 𝓕)
    (hsurj : ∀ L ∈ Gaps.fundSet Q, ∃ R ∈ 𝓕, R.map (spinAction Q) = L)
    (hgeo : ∀ L ∈ Gaps.fundSet Q, ∀ L₁ ∈ Gaps.fundSet Q, ∀ L₂ ∈ Gaps.fundSet Q,
      Commutes L L₁ → Commutes L L₂ → Commutes L₁ L₂ →
      (∃ Lβ ∈ Gaps.fundSet Q, (∃ W, LinearBlockStandardPair (GaloisField p e) W L Lβ) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W L₁ Lβ) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W L₂ Lβ)) ∨
      ∃ L₃ ∈ Gaps.fundSet Q, Commutes L L₃ ∧ ¬ Commutes L₁ L₃ ∧ ¬ Commutes L₂ L₃) :
    ∀ R ∈ 𝓕, ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn 𝓕 R R₁ R₂ →
      ∃ R_β ∈ 𝓕, (∃ W, LinearBlockStandardPair (GaloisField p e) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R_β) := by
  intro R hR R₁ hR₁ R₂ hR₂ h01 h02 h12 hnl
  have hc : ∀ {A B : Subgroup (spinGroup Q)}, Commutes A B →
      Commutes (A.map (spinAction Q)) (B.map (spinAction Q)) := by
    rintro A B h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h a ha b hb]
  have hci : ∀ {A B : Subgroup (spinGroup Q)}, A ∈ 𝓕 →
      (Commutes (A.map (spinAction Q)) (B.map (spinAction Q)) ↔ Commutes A B) :=
    fun hA => ⟨S.commutes_of_map hA, hc⟩
  rcases hgeo _ (S.map R hR) _ (S.map R₁ hR₁) _ (S.map R₂ hR₂) (hc h01) (hc h02) (hc h12) with
    ⟨Lβ, hLβ, a, b, c⟩ | ⟨L₃, hL₃, hc3, hn1, hn2⟩
  · obtain ⟨Rβ, hRβ, rfl⟩ := hsurj Lβ hLβ
    exact ⟨Rβ, hRβ, S.linear_of_map hR hRβ a, S.linear_of_map hR₁ hRβ b,
      S.linear_of_map hR₂ hRβ c⟩
  · exfalso
    obtain ⟨R₃, hR₃, rfl⟩ := hsurj L₃ hL₃
    apply hnl
    have c3 : Commutes R R₃ := (hci hR).mp hc3
    have n1 : ¬ Commutes R₁ R₃ := fun hh => hn1 ((hci hR₁).mpr hh)
    have n2 : ¬ Commutes R₂ R₃ := fun hh => hn2 ((hci hR₂).mpr hh)
    exact (Relation.ReflTransGen.single ⟨hR₁, hR₃, h01.symm, c3.symm, n1⟩).tail
      ⟨hR₃, hR₂, c3.symm, h02.symm, fun hh => n2 hh.symm⟩

end Transfer

section Tags

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Universal.Spin.Twisted




theorem modelLayer_pOmegaOdd3 :
    ∀ R ∈ ModelFund 3 .POmegaOdd 3 1, ∀ R₁ ∈ ModelFund 3 .POmegaOdd 3 1,
      ∀ R₂ ∈ ModelFund 3 .POmegaOdd 3 1, Commutes R R₁ → Commutes R R₂ →
      R₁ = R₂ ∨ Commutes R₁ R₂ := by
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
  refine layer_of_ctx3 S (fun L hL L₁ hL₁ L₂ hL₂ c1 c2 => Or.inl
    (fundSet_layer_eq_of_noOrth3 hodd (fun F₀ F₁ h => ?_) L hL L₁ hL₁ L₂ hL₂ c1 c2))
  have hle := Submodule.finrank_mono h
  rw [F₁.finrank_span] at hle
  have h4' := ModelFacts.finrank_perp_add_four F₀
  omega

theorem modelLayer_pOmegaPlus3 :
    ∀ R ∈ ModelFund 3 .POmegaPlus 4 1, ∀ R₁ ∈ ModelFund 3 .POmegaPlus 4 1,
      ∀ R₂ ∈ ModelFund 3 .POmegaPlus 4 1, Commutes R R₁ → Commutes R R₂ →
      R₁ = R₂ ∨ Commutes R₁ R₂ := by
  have h3 : 3 ≤ 4 := by omega
  have hn : 4 ≤ 4 := le_rfl
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have h : Generic.modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) h3⟩ :=
    RouteD.modelUniv_POmegaPlus_eq h3
  unfold ModelFund
  generalize Generic.modelUniv .POmegaPlus 4 3 1 Fact.out = L at h ⊢
  subst h
  have hodd := odd_gf3
  have hdim : Module.finrank (GaloisField 3 1) (Fin 4 ⊕ Fin 4 → GaloisField 3 1) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have S := spinCtx3_mono (spinCtx3_pOmegaPlus (p := 3) (n := 4) (e := 1) hn (by norm_num))
    (fundamentalSubgroups_subset_longest (t := .POmegaPlus) (by decide) (by decide) _)
  exact layer_of_ctx3 S (fundSet_layer_eq_or_commutes_eight3 hodd hdim)

theorem modelLayer_pOmegaMinus3 :
    ∀ R ∈ ModelFund 3 .POmegaMinus 4 1, ∀ R₁ ∈ ModelFund 3 .POmegaMinus 4 1,
      ∀ R₂ ∈ ModelFund 3 .POmegaMinus 4 1, Commutes R R₁ → Commutes R R₂ →
      R₁ = R₂ ∨ Commutes R₁ R₂ := by
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
  refine layer_of_ctx3 S (fun L hL L₁ hL₁ L₂ hL₂ c1 c2 => Or.inl
    (fundSet_layer_eq_of_noOrth3 hodd (fun F₀ F₁ hF' => ?_) L hL L₁ hL₁ L₂ hL₂ c1 c2))
  exact ModelFacts.TG3.false_of_orth_quadMinus_four3 two_ne_zero_gf3 (minusCoeffs_irr 3 1)
    (by rw [card_gf3]; norm_num) F₀ F₁ hF'

theorem modelStar_pOmegaPlus3 {n : ℕ} (hn : 4 ≤ n) :
    ∀ R ∈ ModelFund 3 .POmegaPlus n 1, ∀ R₁ ∈ ModelFund 3 .POmegaPlus n 1,
      ∀ R₂ ∈ ModelFund 3 .POmegaPlus n 1, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund 3 .POmegaPlus n 1) R R₁ R₂ →
      ∃ R_β ∈ ModelFund 3 .POmegaPlus n 1,
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R_β) := by
  have h3 : 3 ≤ n := by omega
  have h : Generic.modelUniv .POmegaPlus n 3 1 Fact.out =
      ⟨spinGroup (quadPlus n (GaloisField 3 1)), plusDatum n (GaloisField 3 1) h3⟩ :=
    RouteD.modelUniv_POmegaPlus_eq h3
  unfold ModelFund
  generalize Generic.modelUniv .POmegaPlus n 3 1 Fact.out = L at h ⊢
  subst h
  have hodd := odd_gf3
  have S := spinCtx3_mono (spinCtx3_pOmegaPlus (p := 3) (n := n) (e := 1) hn (by norm_num))
    (fundamentalSubgroups_subset_longest (t := .POmegaPlus) (by decide) (by decide) _)
  exact star_of_ctx3 S (fun L hL => Gaps.exists_map_eq h3 hodd hL) (fundSet_star3 hodd)

theorem modelStar_pOmegaOdd3 {n : ℕ} (hn : 3 ≤ n) :
    ∀ R ∈ ModelFund 3 .POmegaOdd n 1, ∀ R₁ ∈ ModelFund 3 .POmegaOdd n 1,
      ∀ R₂ ∈ ModelFund 3 .POmegaOdd n 1, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund 3 .POmegaOdd n 1) R R₁ R₂ →
      ∃ R_β ∈ ModelFund 3 .POmegaOdd n 1,
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R_β) := by
  have hadm : StatedLieAdmissible .POmegaOdd n 3 1 := ⟨Nat.prime_three, le_rfl, hn, by norm_num⟩
  have hM : Generic.modelUniv .POmegaOdd n 3 1 Fact.out =
      ⟨spinGroup (quadOdd n (GaloisField 3 1)), oddDatum n (GaloisField 3 1)⟩ := rfl
  unfold ModelFund
  generalize Generic.modelUniv .POmegaOdd n 3 1 Fact.out = M at hM ⊢
  subst hM
  have hodd := odd_gf3
  have S := spinCtx3_mono (spinCtx3_pOmegaOdd hadm (by norm_num))
    (fundamentalSubgroups_subset_longest (t := .POmegaOdd) (by decide) (by decide) _)
  exact star_of_ctx3 S (fun L hL => Gaps.exists_map_eq_odd hn hodd hL) (fundSet_star3 hodd)

theorem modelStar_pOmegaMinus3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    ∀ R ∈ ModelFund 3 .POmegaMinus n 1, ∀ R₁ ∈ ModelFund 3 .POmegaMinus n 1,
      ∀ R₂ ∈ ModelFund 3 .POmegaMinus n 1, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund 3 .POmegaMinus n 1) R R₁ R₂ →
      ∃ R_β ∈ ModelFund 3 .POmegaMinus n 1,
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R_β) := by
  have hM : Generic.modelUniv .POmegaMinus n 3 1 Fact.out =
      ⟨spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum n (minusCoeffs_irr 3 1)⟩ := rfl
  have hF := Exotic.fundCorr_minus3 (p := 3) (f := 1) (by norm_num) hadm
  unfold ModelFund
  generalize Generic.modelUniv .POmegaMinus n 3 1 Fact.out = M at hM ⊢
  subst hM
  have hodd := odd_gf3
  have S := spinCtx3_mono (spinCtx3_pOmegaMinus hadm (by norm_num))
    (fundamentalSubgroups_subset_longest (t := .POmegaMinus) (by decide) (by decide) _)
  exact star_of_ctx3 S hF.2 (fundSet_star3 hodd)

end Tags

end CFSG.ClassicalInvolution.Q3.Q3W
