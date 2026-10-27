module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Planes
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Triple

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

section Cross

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def SpanOrth (F G : Frame Q) : Prop := ∀ X Y, polar Q (F.incl X) (G.incl Y) = 0

theorem SpanOrth.symm {F G : Frame Q} (h : SpanOrth F G) : SpanOrth G F := fun X Y => by
  rw [polar_comm]
  exact h Y X

theorem SpanOrth.polar_zero {F G : Frame Q} (h : SpanOrth F G) {x y : V} (hx : x ∈ F.span)
    (hy : y ∈ G.span) : polar Q x y = 0 := by
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  exact h X Y

theorem hypOrth_symm {P P' : HypPair Q} (h : P.Orth P') : P'.Orth P :=
  ⟨by rw [polar_comm]; exact h.ee, by rw [polar_comm]; exact h.fe,
    by rw [polar_comm]; exact h.ef, by rw [polar_comm]; exact h.ff⟩

theorem SpanOrth.orth_pairs {F G : Frame Q} (h : SpanOrth F G) :
    F.P.Orth G.P ∧ F.P.Orth G.P' ∧ F.P'.Orth G.P ∧ F.P'.Orth G.P' :=
  ⟨⟨h.polar_zero F.e₁_mem_span G.e₁_mem_span, h.polar_zero F.e₁_mem_span G.f₁_mem_span,
      h.polar_zero F.f₁_mem_span G.e₁_mem_span, h.polar_zero F.f₁_mem_span G.f₁_mem_span⟩,
    ⟨h.polar_zero F.e₁_mem_span G.e₂_mem_span, h.polar_zero F.e₁_mem_span G.f₂_mem_span,
      h.polar_zero F.f₁_mem_span G.e₂_mem_span, h.polar_zero F.f₁_mem_span G.f₂_mem_span⟩,
    ⟨h.polar_zero F.e₂_mem_span G.e₁_mem_span, h.polar_zero F.e₂_mem_span G.f₁_mem_span,
      h.polar_zero F.f₂_mem_span G.e₁_mem_span, h.polar_zero F.f₂_mem_span G.f₁_mem_span⟩,
    ⟨h.polar_zero F.e₂_mem_span G.e₂_mem_span, h.polar_zero F.e₂_mem_span G.f₂_mem_span,
      h.polar_zero F.f₂_mem_span G.e₂_mem_span, h.polar_zero F.f₂_mem_span G.f₂_mem_span⟩⟩

@[expose] def swapOrder (F : Frame Q) : Frame Q := ⟨F.P', F.P, hypOrth_symm F.orth⟩

theorem swapOrder_span_le (F : Frame Q) : (swapOrder F).span ≤ F.span := by
  rintro _ ⟨X, rfl⟩
  refine ⟨!![-X 0 1, -X 0 0; X 1 1, X 1 0], ?_⟩
  simp only [Frame.incl_apply, swapOrder]
  simp
  abel

theorem swapOrder_span (F : Frame Q) : (swapOrder F).span = F.span :=
  le_antisymm (swapOrder_span_le F) (swapOrder_span_le (swapOrder F))

theorem La_range_twin_of_span_eq (h2 : (2 : K) ≠ 0) {Φ Φ' : Frame Q} (hs : Φ'.span = Φ.span) :
    Φ.La.range = Φ'.La.range ∨ Φ.La.range = Φ'.swap.La.range :=
  Frame.La_range_eq_or_eq_swap h2 (Frame.La_neg_one_eq_of_span_eq hs.symm)

theorem lbsp_of_triple (T : Triple Q) {L₁ L₂ : Subgroup (V ≃ₗ[K] V)}
    (h₁ : L₁ = T.frame01.La.range ∨ L₁ = T.frame01.swap.La.range)
    (h₂ : L₂ = T.frame12.La.range ∨ L₂ = T.frame12.swap.La.range) :
    ∃ W, LinearBlockStandardPair K W L₁ L₂ := by
  obtain ⟨θ, hinj, hrange, hU, hV⟩ := T.exists_theta h₁ h₂
  exact ⟨_, CFSG.ClassicalInvolution.Models.linearBlockStandardPair_of_normalized
    (by rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]; exact bot_le) hrange hU hV⟩

theorem cross_partner (h2 : (2 : K) ≠ 0) {F G : Frame Q} (h : SpanOrth F G) :
    ∃ Fβ : Frame Q,
      (∀ LA : Subgroup (V ≃ₗ[K] V), (LA = F.La.range ∨ LA = F.swap.La.range) →
        ∃ W, LinearBlockStandardPair K W LA Fβ.La.range) ∧
      (∀ LB : Subgroup (V ≃ₗ[K] V), (LB = G.La.range ∨ LB = G.swap.La.range) →
        ∃ W, LinearBlockStandardPair K W LB Fβ.La.range) ∧
      (∀ H : Frame Q, SpanOrth H F → SpanOrth H G → SpanOrth H Fβ) := by
  obtain ⟨hFG, hFG', hF'G, hF'G'⟩ := h.orth_pairs
  let T₁ : Triple Q := ⟨F.P, F.P', G.P, F.orth, hFG, hF'G⟩
  let T₂ : Triple Q := ⟨G.P', G.P, F.P', hypOrth_symm G.orth, hypOrth_symm hF'G',
    hypOrth_symm hF'G⟩
  refine ⟨T₁.frame12, ?_, ?_, ?_⟩
  · intro LA hLA
    exact lbsp_of_triple T₁ hLA (Or.inl rfl)
  · intro LB hLB
    have hs : (swapOrder G).span = G.span := swapOrder_span G
    have hs' : (swapOrder G).span = G.swap.span := by rw [Frame.span_eq_swap_span]; exact hs
    refine lbsp_of_triple T₂ ?_ ?_
    · rcases hLB with rfl | rfl
      · exact La_range_twin_of_span_eq h2 hs
      · exact La_range_twin_of_span_eq h2 hs'
    · exact La_range_twin_of_span_eq h2 (swapOrder_span T₁.frame12)
  · intro H hHF hHG X Y
    have hx : H.incl X ∈ H.span := ⟨X, rfl⟩
    have e1 : polar Q (H.incl X) F.e₂ = 0 := hHF.polar_zero hx F.e₂_mem_span
    have e2 : polar Q (H.incl X) F.f₂ = 0 := hHF.polar_zero hx F.f₂_mem_span
    have e3 : polar Q (H.incl X) G.e₁ = 0 := hHG.polar_zero hx G.e₁_mem_span
    have e4 : polar Q (H.incl X) G.f₁ = 0 := hHG.polar_zero hx G.f₁_mem_span
    show polar Q (H.incl X) (Y 0 0 • F.e₂ + Y 1 1 • F.f₂ + (-Y 0 1) • G.e₁ + Y 1 0 • G.f₁) = 0
    simp only [polar_add_right, polar_smul_right_eq, e1, e2, e3, e4, mul_zero, add_zero]

end Cross

section Dichotomy

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem not_commutes_self_of_isFundamental (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) : ¬ Commutes L L := by
  intro hc
  have hle : ⁅L, L⁆ ≤ ⊥ := Subgroup.commutator_le.mpr fun a ha b hb => by
    have : a * b = b * a := hc a ha b hb
    simp [commutatorElement_def, this]
  have hi : i ∈ ⁅L, L⁆ := by rw [IsFundamental.commutator_eq h4 h]; exact h.mem
  exact IsFundamental.ne_one hodd h (Subgroup.mem_bot.mp (hle hi))

omit [Finite K] in
theorem spanOrth_or_eq (h2 : (2 : K) ≠ 0) {F G : Frame Q}
    (h : Commutes F.La.range G.La.range) : SpanOrth F G ∨ G.La (-1) = F.La (-1) :=
  Frame.orth_or_eq h2 (h _ ⟨-1, rfl⟩ _ ⟨-1, rfl⟩).symm fun A => (h _ ⟨A, rfl⟩ _ ⟨-1, rfl⟩).symm

theorem orth_star_dichotomy (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    {L L₁ L₂ : Subgroup (V ≃ₗ[K] V)} {i i₁ i₂ : V ≃ₗ[K] V}
    (hL : IsFundamental Q L i) (hL₁ : IsFundamental Q L₁ i₁) (hL₂ : IsFundamental Q L₂ i₂)
    (h01 : Commutes L L₁) (h02 : Commutes L L₂) (h12 : Commutes L₁ L₂) :
    (∃ Lβ : Subgroup (V ≃ₗ[K] V), (∃ j, IsFundamental Q Lβ j) ∧
        (∃ W, LinearBlockStandardPair K W L Lβ) ∧ (∃ W, LinearBlockStandardPair K W L₁ Lβ) ∧
        (∃ W, LinearBlockStandardPair K W L₂ Lβ)) ∨
      ∃ L₃ : Subgroup (V ≃ₗ[K] V), (∃ j, IsFundamental Q L₃ j) ∧ Commutes L L₃ ∧
        ¬ Commutes L₁ L₃ ∧ ¬ Commutes L₂ L₃ := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hn0 := not_commutes_self_of_isFundamental hodd h4 hL
  have hn1 := not_commutes_self_of_isFundamental hodd h4 hL₁
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

end Dichotomy

end CFSG.ClassicalInvolution.RouteD
