module

public import CFSG.ClassicalInvolution.RouteD.TWEB4Fixed

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWE.B4
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.Models (linearBlockStandardPair_of_normalized)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem commutes_mk_of_orth {a b c d : HypPair Q} (hab : a.Orth b) (hcd : c.Orth d)
    (hac : a.Orth c) (had : a.Orth d) (hbc : b.Orth c) (hbd : b.Orth d) :
    Commutes (mkFrame a b hab).La.range (mkFrame c d hcd).La.range := by
  refine commutes_of_span_orth _ _ ?_
  rw [frame_span_eq, frame_span_eq]
  simp only [mkFrame]
  exact polar_eq_zero_of_sup (fun x hx y hy => polar_hypPlane_of_orth hac x hx y hy)
    (fun x hx y hy => polar_hypPlane_of_orth had x hx y hy)
    (fun x hx y hy => polar_hypPlane_of_orth hbc x hx y hy)
    (fun x hx y hy => polar_hypPlane_of_orth hbd x hx y hy)

theorem exists_leaf_pair_three (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}
    (hc : VChain Q 2 L i) :
    ∃ S₁ S₂ : Subgroup (V ≃ₗ[K] V), S₁ ∈ fundSet Q ∧ S₂ ∈ fundSet Q ∧ Commutes S₁ (L 0) ∧
      Commutes S₂ (L 0) ∧ LinearBlockStandardPair K (L 1 ⊔ S₁) (L 1) S₁ ∧
      LinearBlockStandardPair K (L 1 ⊔ S₂) (L 1) S₂ ∧ S₁ ≠ S₂ := by
  obtain ⟨p, horth, -, hL⟩ := exists_chain_pairs true hodd hc (le_refl 2)
  obtain ⟨p', hp', ho'⟩ := exists_orth_ext hodd hQ p 3
    (fun a b ha hb hab => horth a b (by omega) (by omega) hab) 1 (by omega)
  have hpp : ∀ a b, a < 4 → b < 4 → a ≠ b → (p' a).Orth (p' b) :=
    fun a b ha hb hab => ho' a b (by omega) (by omega) hab
  have hL0 : L 0 = (oFrame true (p' 0) (p' 1) (hpp 0 1 (by norm_num) (by norm_num)
      (by norm_num))).La.range := by
    have := hL 0 (by norm_num)
    simpa only [hp' 0 (by norm_num), hp' 1 (by norm_num)] using this
  have hL1 : L 1 = (oFrame true (p' 1) (p' 2) (hpp 1 2 (by norm_num) (by norm_num)
      (by norm_num))).La.range := by
    have := hL 1 (by norm_num)
    simpa only [hp' 1 (by norm_num), hp' 2 (by norm_num)] using this
  have o02 := hpp 0 2 (by norm_num) (by norm_num) (by norm_num)
  have o03 := hpp 0 3 (by norm_num) (by norm_num) (by norm_num)
  have o12 := hpp 1 2 (by norm_num) (by norm_num) (by norm_num)
  have o13 := hpp 1 3 (by norm_num) (by norm_num) (by norm_num)
  have o23 := hpp 2 3 (by norm_num) (by norm_num) (by norm_num)
  let T : Triple Q := ⟨p' 1, p' 2, p' 3, o12, o13, o23⟩
  have hL1T : L 1 = T.frame01.swap.La.range := by rw [hL1]; rfl
  have hker : ∀ θ : SL(3, K) →* (V ≃ₗ[K] V), Function.Injective θ →
      θ.ker ≤ Subgroup.center SL(3, K) := fun θ hinj => by
    rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]
    exact bot_le
  have hpair : ∀ {S : Subgroup (V ≃ₗ[K] V)},
      (S = T.frame12.La.range ∨ S = T.frame12.swap.La.range) →
      LinearBlockStandardPair K (L 1 ⊔ S) (L 1) S := fun {S} hS => by
    obtain ⟨θ, hinj, hrange, hU, hV⟩ := T.exists_theta (Or.inr hL1T) hS
    exact linearBlockStandardPair_of_normalized (hker θ hinj) hrange hU hV
  have hcomm : ∀ F : OFrame Q, F.span = hypPlane (p' 2) ⊔ hypPlane (p' 3) →
      Commutes F.La.range (L 0) := by
    intro F hF
    rw [hL0]
    refine commutes_of_span_orth _ _ ?_
    rw [hF, frame_span_eq]
    simp only [oFrame, mkFrame, twistPair, ite_true, hypPlane_swapPair]
    exact polar_eq_zero_of_sup (fun x hx y hy => polar_hypPlane_of_orth o02.symm x hx y hy)
      (fun x hx y hy => polar_hypPlane_of_orth o12.symm x hx y hy)
      (fun x hx y hy => polar_hypPlane_of_orth o03.symm x hx y hy)
      (fun x hx y hy => polar_hypPlane_of_orth o13.symm x hx y hy)
  have hspan : T.frame12.span = hypPlane (p' 2) ⊔ hypPlane (p' 3) := frame_span_eq T.frame12
  refine ⟨T.frame12.swap.La.range, T.frame12.La.range, ⟨_, IsFundamental.of_frame_swap _⟩,
    ⟨_, IsFundamental.of_frame _⟩, hcomm _ (by rw [← Frame.span_eq_swap_span]; exact hspan),
    hcomm _ hspan, hpair (Or.inr rfl), hpair (Or.inl rfl),
    (Frame.La_range_ne_swap_La_range T.frame12).symm⟩

end Model

section Spin

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}


theorem exists_leaf_spin_three (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hdim : 9 ≤ Module.finrank (GaloisField p f) V)
    (hQ : (polarBilin Q).Nondegenerate) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V))
    (hF : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕,
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map (spinAction Q))
        (R₂.map (spinAction Q))) → ∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂)
    {R₀ R₁ : Subgroup (spinGroup Q)} (h₀ : R₀ ∈ 𝓕) (h₁ : R₁ ∈ 𝓕)
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) :
    ∃ T₁ ∈ 𝓕, ∃ T₂ ∈ 𝓕, Commutes T₁ R₀ ∧ Commutes T₂ R₀ ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ T₁) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ T₂) ∧ T₁ ≠ T₂ := by
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
  obtain ⟨S₁, S₂, hS₁, hS₂, c₁, c₂, s₁, s₂, hne⟩ := exists_leaf_pair_three hodd hQ hdim hvc
  obtain ⟨T₁, hT₁, rfl⟩ := cq.surj S₁ hS₁
  obtain ⟨T₂, hT₂, rfl⟩ := cq.surj S₂ hS₂
  exact ⟨T₁, hT₁, T₂, hT₂, (cq.commutes_iff hT₁).mp c₁, (cq.commutes_iff hT₂).mp c₂,
    hF R₁ h₁ T₁ hT₁ ⟨_, s₁⟩, hF R₁ h₁ T₂ hT₂ ⟨_, s₂⟩, fun h => hne (by rw [h])⟩

end Spin

section Group

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}


theorem exists_leaf_b3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {u})
    (hshape : LocalShapeT p f 0 .POmegaOdd 4 Ω u) {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember p f K z) (hs : IsClassicalMember p f β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) :
    ∃ N₁ ∈ centralizingMembers Ω {u}, ∃ N₂ ∈ centralizingMembers Ω {u},
      Commutes K N₁ ∧ Commutes K N₂ ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W β N₁) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W β N₂) ∧ N₁ ≠ N₂ := by
  classical
  obtain ⟨e⟩ := Layer0.of_shape hΩ hex (by decide) (by decide) hshape
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨Fact.out, hf1, by norm_num, hp2⟩
  have hY : YData p f .POmegaOdd 4 := yData_odd (by norm_num) hadm (by omega)
  have hF := orthFacts_odd (m := 4) hp2 (by norm_num) hq
  have cq := centralQuot_odd (m := 4) hp2 (by norm_num) hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hQ : (polarBilin (quadOdd 4 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 4 _ h2
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv .POmegaOdd 4 p f Fact.out).K) R₀ R₁ :=
    e.modelAdj hY hΩ hP1 hK hβ hR₀ hR₁ hKR hβR hz hs (ne_of_linearBlockStandardPair hW)
      (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hF hP1 hK hβ hR₀ hR₁ hKR hβR hW
  obtain ⟨T₁, hT₁, T₂, hT₂, c₁, c₂, p₁, p₂, hne⟩ := exists_leaf_spin_three hp2 hq hdim hQ cq
    (fun A hA B hB hl => hF.lift (spinAction _) (ker_spinAction_le_center _) A hA B hB hl) hR₀
    hR₁ hadjR ⟨W', hW'⟩
  obtain ⟨N₁, hN₁, hN₁T⟩ := e.comp T₁ hT₁
  obtain ⟨N₂, hN₂, hN₂T⟩ := e.comp T₂ hT₂
  obtain ⟨W₁, hW₁⟩ := p₁
  obtain ⟨W₂, hW₂⟩ := p₂
  refine ⟨N₁, hN₁, N₂, hN₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN₁ hK hT₁ hN₁T hKR).mpr c₁)
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN₂ hK hT₂ hN₂T hKR).mpr c₂)
  · exact e.pair_of_model hq hΩ hP1 hβ hN₁ hβR hN₁T hW₁
  · exact e.pair_of_model hq hΩ hP1 hβ hN₂ hβR hN₂T hW₂
  · intro h
    refine hne (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect e.φ e.ker_le
      (cq.perf T₁ hT₁) (cq.perf T₂ hT₂) ?_)
    rw [← hN₁T, ← hN₂T, h]

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.B3
