module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Bridge
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.RouteD.GapsFrModel
public import CFSG.ClassicalInvolution.RouteD.TWEB6Layer

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.Generic (Commutes)

set_option linter.unusedSectionVars false

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_noncommuting_pair (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 11 ≤ Module.finrank K V) {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}
    (hc : VChain Q 2 L i) :
    ∃ S₁ S₂ : Subgroup (V ≃ₗ[K] V), S₁ ∈ fundSet Q ∧ S₂ ∈ fundSet Q ∧
      (∀ a < 2, Commutes S₁ (L a) ∧ Commutes S₂ (L a)) ∧ ¬ Commutes S₁ S₂ ∧ S₁ ≠ S₂ := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨p, horth, -, hL⟩ := exists_chain_pairs true hodd hc (le_refl 2)
  have ho3 : ∀ a b, a < 3 → b < 3 → a ≠ b → (p a).Orth (p b) := fun a b ha hb hab =>
    horth a b (by omega) (by omega) hab
  obtain ⟨pb, hpb⟩ := exists_pair_perp_fam hodd hQ p 3 ho3 (by omega)
  let p4 : ℕ → HypPair Q := fun a => if a < 3 then p a else pb
  have ho4 : ∀ a b, a < 4 → b < 4 → a ≠ b → (p4 a).Orth (p4 b) := by
    intro a b ha hb hab
    by_cases h1 : a < 3 <;> by_cases h3 : b < 3
    · simp only [p4, h1, h3, ite_true]
      exact ho3 a b h1 h3 hab
    · have : b = 3 := by omega
      simp only [p4, h1, h3, ite_true, ite_false]
      exact hpb a h1
    · have : a = 3 := by omega
      simp only [p4, h1, h3, ite_true, ite_false]
      exact (hpb b h3).symm
    · omega
  obtain ⟨q₁, q₂, c, hq, he, hf, hQc, hce, hcf⟩ := exists_two_pairs_perp hodd hQ p4 4 ho4
    (by omega)
  have hpq₁ : ∀ a < 3, (p a).Orth q₁ := fun a ha => by
    have := (hq a (by omega)).1
    simpa [p4, ha] using this
  have hpq₂ : ∀ a < 3, (p a).Orth q₂ := fun a ha => by
    have := (hq a (by omega)).2
    simpa [p4, ha] using this
  have hbq₁ : pb.Orth q₁ := by
    have := (hq 3 (by omega)).1
    simpa [p4] using this
  have hbq₂ : pb.Orth q₂ := by
    have := (hq 3 (by omega)).2
    simpa [p4] using this
  set F₁ := mkFrame pb (swapPair q₁) (orth_swapPair hbq₁) with hF₁
  set F₂ := mkFrame pb (swapPair q₂) (orth_swapPair hbq₂) with hF₂
  have hcomm : ∀ (q : HypPair Q) (hbq : pb.Orth q), (∀ a < 3, (p a).Orth q) → ∀ a < 2,
      Commutes (mkFrame pb (swapPair q) (orth_swapPair hbq)).La.range (L a) := by
    intro q hbq hpq a ha
    rw [hL a ha]
    refine commutes_of_span_orth _ _ ?_
    rw [frame_span_eq, frame_span_eq]
    simp only [oFrame, mkFrame, twistPair, ite_true, hypPlane_swapPair]
    refine polar_eq_zero_of_sup (fun x hx y hy => ?_) (fun x hx y hy => ?_)
      (fun x hx y hy => ?_) (fun x hx y hy => ?_)
    · exact polar_hypPlane_of_orth (hpb a (by omega)).symm x hx y hy
    · exact polar_hypPlane_of_orth (hpb (a + 1) (by omega)).symm x hx y hy
    · exact polar_hypPlane_of_orth (hpq a (by omega)).symm x hx y hy
    · exact polar_hypPlane_of_orth (hpq (a + 1) (by omega)).symm x hx y hy
  have hmemF : ∀ (F : OFrame Q), F.P = pb → ∀ x ∈ hypPlane pb, x ∈ negSpace (F.La (-1)) := by
    intro F hFP x hx
    rw [negSpace_La_neg_one h2, frame_span_eq, hFP]
    exact Submodule.mem_sup_left hx
  have hne' : F₂.La (-1) ≠ F₁.La (-1) := by
    intro heq
    set f := q₁.f with hff
    have e1 := La_neg_one_mkFrame_swap pb q₁ hbq₁ f
    have e2 := La_neg_one_mkFrame_swap pb q₂ hbq₂ f
    have hx1 : (F₁.La (-1)) f = f - (2 : K) • (polar Q f pb.f • pb.e +
        polar Q f pb.e • pb.f + polar Q f q₁.e • q₁.f + polar Q f q₁.f • q₁.e) := e1
    have hx2 : (F₂.La (-1)) f = f - (2 : K) • (polar Q f pb.f • pb.e +
        polar Q f pb.e • pb.f + polar Q f q₂.e • q₂.f + polar Q f q₂.f • q₂.e) := e2
    have hh := congrArg (fun g : V ≃ₗ[K] V => polar Q f (g f)) heq
    simp only [hx1, hx2] at hh
    have o1 : polar Q f pb.f = 0 := by
      rw [polar_comm]
      exact hbq₁.ff
    have o2 : polar Q f pb.e = 0 := by
      rw [polar_comm]
      exact hbq₁.ef
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
  refine ⟨F₁.La.range, F₂.La.range, ⟨_, IsFundamental.of_frame F₁⟩,
    ⟨_, IsFundamental.of_frame F₂⟩, fun a ha => ⟨hcomm q₁ hbq₁ hpq₁ a ha, hcomm q₂ hbq₂ hpq₂ a ha⟩,
    not_commutes_of_nonorth hodd (IsFundamental.of_frame F₁) (IsFundamental.of_frame F₂) hne'
      (hmemF F₁ rfl _ (e_mem_hypPlane pb)) (hmemF F₂ rfl _ (f_mem_hypPlane pb))
      (by rw [pb.polar_ef]; exact one_ne_zero), fun h => hne' ?_⟩
  exact IsFundamental.involution_unique hodd (IsFundamental.of_frame F₂)
    (h ▸ IsFundamental.of_frame F₁)

end Model

section Spin

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.RouteD


theorem exists_noncommuting_pair_spin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 11 ≤ Module.finrank (GaloisField p f) V)
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V))
    {R₀ R₁ : Subgroup (spinGroup Q)} (h₀ : R₀ ∈ 𝓕) (h₁ : R₁ ∈ 𝓕)
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) :
    ∃ T ∈ 𝓕, ∃ T' ∈ 𝓕, Commutes T R₀ ∧ Commutes T R₁ ∧ Commutes T' R₀ ∧ Commutes T' R₁ ∧
      ¬ Commutes T T' ∧ T ≠ T' := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ h₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ h₁
  have hdata := adj_data hodd (by omega) hi₀ hi₁ (cq.modelAdj h₀ h₁ hadj)
  obtain ⟨W, hW⟩ := hlin
  have hsing := hasSingularVector_of_linearPair hp2 (by omega) hi₀ hi₁ hdata.1 hdata.2.1
    hdata.2.2 ⟨_, linearBlockStandardPair_map_central hW _ cq.ker_le⟩
  have hvc : VChain Q 2 (fun a => if a = 0 then R₀.map (spinAction Q) else R₁.map (spinAction Q))
      (fun a => if a = 0 then i₀ else i₁) := by
    refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a b hab hb => ?_⟩
    · rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · exact hi₀
      · exact hi₁
    · obtain rfl : a = 0 := by omega
      exact hdata.1
    · obtain rfl : a = 0 := by omega
      exact hdata.2.1
    · obtain rfl : a = 0 := by omega
      exact hdata.2.2
    · obtain rfl : a = 0 := by omega
      exact hsing
    · exfalso
      omega
  obtain ⟨S, S', hS, hS', hc, hnc, hne⟩ := exists_noncommuting_pair hodd hQ hdim hvc
  obtain ⟨T, hT, rfl⟩ := cq.surj S hS
  obtain ⟨T', hT', rfl⟩ := cq.surj S' hS'
  have c0 := hc 0 (by norm_num)
  have c1 := hc 1 (by norm_num)
  simp only [ite_true, one_ne_zero, ite_false] at c0 c1
  exact ⟨T, hT, T', hT', (cq.commutes_iff hT).mp c0.1, (cq.commutes_iff hT).mp c1.1,
    (cq.commutes_iff hT').mp c0.2, (cq.commutes_iff hT').mp c1.2,
    fun h => hnc ((cq.commutes_iff hT).mpr h), fun h => hne (by rw [h])⟩

end Spin

section Group

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}


theorem exists_noncommuting_members (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {u})
    (hshape : LocalShapeT p f 0 .POmegaOdd 5 Ω u) {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember p f K z) (hs : IsClassicalMember p f β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) :
    ∃ N₁ ∈ centralizingMembers Ω {u}, ∃ N₂ ∈ centralizingMembers Ω {u},
      Commutes K N₁ ∧ Commutes β N₁ ∧ Commutes K N₂ ∧ Commutes β N₂ ∧ ¬ Commutes N₁ N₂ ∧
        N₁ ≠ N₂ := by
  classical
  obtain ⟨e⟩ := Layer0.of_shape hΩ hex (by decide) (by decide) hshape
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 5 p f := ⟨Fact.out, hf1, by norm_num, hp2⟩
  have hY : YData p f .POmegaOdd 5 := yData_odd (by norm_num) hadm (by omega)
  have hF := orthFacts_odd (m := 5) hp2 (by norm_num) hq
  have cq := centralQuot_odd (m := 5) hp2 (by norm_num) hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hQ : (polarBilin (quadOdd 5 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 5 _ h2
  have hdim : 11 ≤ Module.finrank (GaloisField p f)
      (Fin 5 ⊕ Fin 5 ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv .POmegaOdd 5 p f Fact.out).K) R₀ R₁ :=
    e.modelAdj hY hΩ hP1 hK hβ hR₀ hR₁ hKR hβR hz hs (ne_of_linearBlockStandardPair hW)
      (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hF hP1 hK hβ hR₀ hR₁ hKR hβR hW
  obtain ⟨T, hT, T', hT', c0, c1, c0', c1', hnc, hne⟩ :=
    exists_noncommuting_pair_spin hp2 hq hQ hdim cq hR₀ hR₁ hadjR ⟨W', hW'⟩
  obtain ⟨N, hN, hNT⟩ := e.comp T hT
  obtain ⟨N', hN', hN'T⟩ := e.comp T' hT'
  refine ⟨N, hN, N', hN', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN hK hT hNT hKR).mpr c0)
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN hβ hT hNT hβR).mpr c1)
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN' hK hT' hN'T hKR).mpr c0')
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN' hβ hT' hN'T hβR).mpr c1')
  · exact fun h => hnc ((e.commutes_iff hY hΩ hP1 hN hN' hT hNT hN'T).mp h)
  · intro h
    refine hne (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect e.φ e.ker_le
      (cq.perf T hT) (cq.perf T' hT') ?_)
    rw [← hNT, ← hN'T, h]

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.B4
