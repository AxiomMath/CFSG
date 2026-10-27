module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Pairs
public import CFSG.ClassicalInvolution.RouteD.GapsFrChain

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.Models (linearBlockStandardPair_of_normalized)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Bridge

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem polar_eq_zero_of_sup {A₁ A₂ B₁ B₂ : Submodule K V}
    (h11 : ∀ x ∈ A₁, ∀ y ∈ B₁, polar Q x y = 0) (h12 : ∀ x ∈ A₁, ∀ y ∈ B₂, polar Q x y = 0)
    (h21 : ∀ x ∈ A₂, ∀ y ∈ B₁, polar Q x y = 0) (h22 : ∀ x ∈ A₂, ∀ y ∈ B₂, polar Q x y = 0) :
    ∀ x ∈ A₁ ⊔ A₂, ∀ y ∈ B₁ ⊔ B₂, polar Q x y = 0 := by
  intro x hx y hy
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hy
  simp only [polar_add_left, polar_add_right, h11 _ ha₁ _ hb₁, h12 _ ha₁ _ hb₂, h21 _ ha₂ _ hb₁,
    h22 _ ha₂ _ hb₂, add_zero]

theorem commutes_of_span_orth (F F' : OFrame Q)
    (h : ∀ x ∈ F.span, ∀ y ∈ F'.span, polar Q x y = 0) :
    Commutes F.La.range F'.La.range := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact Frame.La_comm_of_orth (fun X Y => h _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩) A B

theorem La_neg_one_mkFrame_swap (P P' : HypPair Q) (h : P.Orth P') (x : V) :
    (mkFrame P (swapPair P') (orth_swapPair h)).La (-1) x =
      x - (2 : K) • (polar Q x P.f • P.e + polar Q x P.e • P.f + polar Q x P'.e • P'.f +
        polar Q x P'.f • P'.e) := by
  rw [Frame.La_neg_one_apply]
  congr 2
  simp [Frame.incl_apply, Frame.coords_apply, mkFrame, swapPair]

theorem bridge_aux (hodd : Odd (Nat.card K)) {L : ℕ → Subgroup (V ≃ₗ[K] V)}
    {i : ℕ → V ≃ₗ[K] V} (hc : VChain Q 5 L i) {L5 : Subgroup (V ≃ₗ[K] V)}
    (h5 : IsFundamental Q L5 (i 4)) (hne : L5 ≠ L 4) (p : ℕ → HypPair Q)
    (horth : ∀ a b, a ≤ 5 → b ≤ 5 → a ≠ b → (p a).Orth (p b))
    (hL : ∀ a (ha : a < 5), L a =
      (oFrame true (p a) (p (a + 1)) (horth a (a + 1) ha.le (by omega) (by omega))).La.range)
    (q : HypPair Q) (hq : ∀ a < 6, (p a).Orth q) :
    (∀ a < 4, Commutes (mkFrame (p 5) (swapPair q) (orth_swapPair (hq 5 (by norm_num)))).La.range
      (L a)) ∧
    LinearBlockStandardPair K (L 4 ⊔
      (mkFrame (p 5) (swapPair q) (orth_swapPair (hq 5 (by norm_num)))).La.range) (L 4)
      (mkFrame (p 5) (swapPair q) (orth_swapPair (hq 5 (by norm_num)))).La.range ∧
    LinearBlockStandardPair K (L5 ⊔
      (mkFrame (p 5) (swapPair q) (orth_swapPair (hq 5 (by norm_num)))).La.range) L5
      (mkFrame (p 5) (swapPair q) (orth_swapPair (hq 5 (by norm_num)))).La.range := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set F := mkFrame (p 5) (swapPair q) (orth_swapPair (hq 5 (by norm_num))) with hF
  refine ⟨fun a ha => ?_, ?_⟩
  ·
    rw [hL a (by omega)]
    refine commutes_of_span_orth F _ ?_
    rw [frame_span_eq, frame_span_eq]
    simp only [oFrame, mkFrame, twistPair, ite_true, hypPlane_swapPair, hF]
    refine polar_eq_zero_of_sup (fun x hx y hy => ?_) (fun x hx y hy => ?_)
      (fun x hx y hy => ?_) (fun x hx y hy => ?_)
    · exact polar_hypPlane_of_orth (horth 5 a (by omega) (by omega) (by omega)) x hx y hy
    · exact polar_hypPlane_of_orth (horth 5 (a + 1) (by omega) (by omega) (by omega)) x hx y hy
    · exact polar_hypPlane_of_orth (hq a (by omega)).symm x hx y hy
    · exact polar_hypPlane_of_orth (hq (a + 1) (by omega)).symm x hx y hy
  ·
    let T : Triple Q := ⟨p 4, p 5, q, horth 4 5 (by omega) (by omega) (by omega),
      hq 4 (by omega), hq 5 (by omega)⟩
    have hL4 : L 4 = T.frame01.swap.La.range := by
      rw [hL 4 (by omega)]
      rfl
    have hFT : F = T.frame12.swap := rfl
    have hf4 : IsFundamental Q (L 4) (T.frame01.swap.La (-1)) :=
      hL4 ▸ IsFundamental.of_frame T.frame01.swap
    have hi4 : i 4 = T.frame01.swap.La (-1) :=
      IsFundamental.involution_unique hodd (hc.fund 4 (by omega)) hf4
    have hL5 : L5 = T.frame01.La.range := by
      obtain ⟨F'', hF''L, hF''i⟩ := h5
      have hii : F''.La (-1) = T.frame01.swap.La (-1) := hF''i.symm.trans hi4
      rcases Frame.La_range_eq_or_eq_swap h2 hii with h | h
      · exact absurd (hF''L.trans (h.trans hL4.symm)) hne
      · rw [hF''L, h]
        rfl
    have hker : ∀ θ : SL(3, K) →* (V ≃ₗ[K] V), Function.Injective θ →
        θ.ker ≤ Subgroup.center SL(3, K) := fun θ hinj => by
      rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]
      exact bot_le
    refine ⟨?_, ?_⟩
    · obtain ⟨θ, hinj, hrange, hU, hV⟩ := T.exists_theta (Or.inr hL4) (Or.inr rfl)
      rw [hFT]
      exact linearBlockStandardPair_of_normalized (hker θ hinj) hrange hU hV
    · obtain ⟨θ, hinj, hrange, hU, hV⟩ := T.exists_theta (Or.inl hL5) (Or.inr rfl)
      rw [hFT]
      exact linearBlockStandardPair_of_normalized (hker θ hinj) hrange hU hV

theorem exists_bridges (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 15 ≤ Module.finrank K V) {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}
    (hc : VChain Q 5 L i) {L5 : Subgroup (V ≃ₗ[K] V)} (h5 : IsFundamental Q L5 (i 4))
    (hne : L5 ≠ L 4) :
    ∃ S₁ S₂ : Subgroup (V ≃ₗ[K] V), S₁ ∈ fundSet Q ∧ S₂ ∈ fundSet Q ∧
      (∀ a < 4, Commutes S₁ (L a) ∧ Commutes S₂ (L a)) ∧
      LinearBlockStandardPair K (L 4 ⊔ S₁) (L 4) S₁ ∧
      LinearBlockStandardPair K (L5 ⊔ S₁) L5 S₁ ∧
      LinearBlockStandardPair K (L 4 ⊔ S₂) (L 4) S₂ ∧
      LinearBlockStandardPair K (L5 ⊔ S₂) L5 S₂ ∧ ¬ Commutes S₁ S₂ ∧ S₁ ≠ S₂ := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨p, horth, hpl, hL⟩ := exists_chain_pairs true hodd hc (by norm_num : 2 ≤ 5)
  have ho : ∀ a b, a < 6 → b < 6 → a ≠ b → (p a).Orth (p b) :=
    fun a b ha hb hab => horth a b (by omega) (by omega) hab
  obtain ⟨q₁, q₂, c, hq, he, hf, hQc, hce, hcf⟩ :=
    exists_two_pairs_perp hodd hQ p 6 ho (by omega)
  have hq₁ : ∀ a < 6, (p a).Orth q₁ := fun a ha => (hq a ha).1
  have hq₂ : ∀ a < 6, (p a).Orth q₂ := fun a ha => (hq a ha).2
  obtain ⟨c₁, s₁, t₁⟩ := bridge_aux hodd hc h5 hne p horth hL q₁ hq₁
  obtain ⟨c₂, s₂, t₂⟩ := bridge_aux hodd hc h5 hne p horth hL q₂ hq₂
  set F₁ := mkFrame (p 5) (swapPair q₁) (orth_swapPair (hq₁ 5 (by norm_num))) with hF₁
  set F₂ := mkFrame (p 5) (swapPair q₂) (orth_swapPair (hq₂ 5 (by norm_num))) with hF₂
  refine ⟨F₁.La.range, F₂.La.range, ⟨_, IsFundamental.of_frame F₁⟩,
    ⟨_, IsFundamental.of_frame F₂⟩, fun a ha => ⟨c₁ a ha, c₂ a ha⟩, s₁, t₁, s₂, t₂, ?_⟩
  have hmemF : ∀ (F : OFrame Q), F.P = p 5 → ∀ x ∈ hypPlane (p 5), x ∈ negSpace (F.La (-1)) := by
    intro F hFP x hx
    rw [negSpace_La_neg_one h2, frame_span_eq, hFP]
    exact Submodule.mem_sup_left hx
  have hne' : F₂.La (-1) ≠ F₁.La (-1) := by
    intro heq
    set f := q₁.f with hff
    have e1 := La_neg_one_mkFrame_swap (p 5) q₁ (hq₁ 5 (by norm_num)) f
    have e2 := La_neg_one_mkFrame_swap (p 5) q₂ (hq₂ 5 (by norm_num)) f
    have hx1 : (F₁.La (-1)) f = f - (2 : K) • (polar Q f (p 5).f • (p 5).e +
        polar Q f (p 5).e • (p 5).f + polar Q f q₁.e • q₁.f + polar Q f q₁.f • q₁.e) := e1
    have hx2 : (F₂.La (-1)) f = f - (2 : K) • (polar Q f (p 5).f • (p 5).e +
        polar Q f (p 5).e • (p 5).f + polar Q f q₂.e • q₂.f + polar Q f q₂.f • q₂.e) := e2
    have hh := congrArg (fun g : V ≃ₗ[K] V => polar Q f (g f)) heq
    simp only [hx1, hx2] at hh
    have o1 : polar Q f (p 5).f = 0 := by
      rw [polar_comm]
      exact (hq₁ 5 (by norm_num)).ff
    have o2 : polar Q f (p 5).e = 0 := by
      rw [polar_comm]
      exact (hq₁ 5 (by norm_num)).ef
    have o3 : polar Q f q₁.e = 1 := q₁.polar_fe
    have o4 : polar Q f q₁.f = 0 := q₁.polar_ff
    have o5 : polar Q f q₂.e = 1 := by rw [he]; exact o3
    have o6 : polar Q f q₂.f = -Q c := by
      rw [hf, polar_sub_right, polar_add_right, polar_smul_right_eq, o4, hcf, o3]
      ring
    simp only [polar_sub_right, polar_add_right, polar_smul_right_eq, o1, o2, o3, o4, o5, o6,
      zero_mul, zero_add, add_zero, mul_zero] at hh
    have h4 : (2 : K) * (2 * Q c) = 0 := by linear_combination hh
    rcases mul_eq_zero.mp h4 with h | h
    · exact h2 h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h2 h'
      · exact hQc h'
  refine ⟨not_commutes_of_nonorth hodd (IsFundamental.of_frame F₁) (IsFundamental.of_frame F₂)
    hne' (hmemF F₁ rfl _ (e_mem_hypPlane (p 5))) (hmemF F₂ rfl _ (f_mem_hypPlane (p 5)))
    (by rw [(p 5).polar_ef]; exact one_ne_zero), fun h => hne' ?_⟩
  exact IsFundamental.involution_unique hodd (IsFundamental.of_frame F₂)
    (h ▸ IsFundamental.of_frame F₁)

end Bridge

end CFSG.ClassicalInvolution.RouteD.TWE.B6
