module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqA1
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqA2
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace TwE6UniqAbs

set_option linter.unusedSectionVars false

theorem orbit_logic {C : Type*} (n : C → ℕ) (f : C → C) (hf : Function.Injective f)
    (hn : ∀ c, n (f c) = n c) (sizes : ∀ c, n c = 2 ∨ n c = 6 ∨ 12 ≤ n c)
    (big : ∀ c d, c ≠ d → 12 ≤ n c → 12 ≤ n d → False)
    (four : ∀ c d e g : C, c ≠ d → c ≠ e → c ≠ g → d ≠ e → d ≠ g → e ≠ g → False)
    (three : ∀ c d e : C, c ≠ d → c ≠ e → d ≠ e → n c = 6 ∧ n d = 6 ∧ n e = 6)
    (Q : C → Prop) (hQ2 : ∀ c, Q c → n c ≠ 2) (hQ6 : ∀ c, Q c → n c = 6 → f c ≠ c)
    (i j : C) (hi : Q i) (hj : Q j) : i = j ∨ f i = j ∨ f j = i := by
  have h6or : ∀ c, Q c → n c = 6 ∨ 12 ≤ n c := by
    intro c hc
    rcases sizes c with h | h | h
    · exact (hQ2 c hc h).elim
    · exact Or.inl h
    · exact Or.inr h
  by_cases hij : i = j
  · exact Or.inl hij
  right
  rcases h6or i hi with hi6 | hi12 <;> rcases h6or j hj with hj6 | hj12
  · by_cases h1 : f i = j
    · exact Or.inl h1
    right
    by_cases h2 : f j = i
    · exact h2
    exfalso
    exact four i (f i) j (f j) (hQ6 i hi hi6).symm hij (fun h => h2 h.symm) (fun h => h1 h)
      (fun h => hij (hf h)) (hQ6 j hj hj6).symm
  · exfalso
    have hfi := hQ6 i hi hi6
    have := (three i (f i) j hfi.symm hij (fun h => by
      subst h
      have := hn i
      omega)).2.2
    omega
  · exfalso
    have hfj := hQ6 j hj hj6
    have := (three j (f j) i hfj.symm (Ne.symm hij) (fun h => by
      subst h
      have := hn j
      omega)).2.2
    omega
  · exfalso
    exact big i j hij hi12 hj12

section Rat


theorem rationalRoots_eq_of_image {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) {i j : KernelComponent (rootCharHom a)}
    (h : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) j) :
    rationalRoots S.ρ (rootCharHom a) i = rationalRoots S.ρ (rootCharHom a) j := by
  obtain ⟨s, hs0, hs⟩ := outer_exists_period S hT i
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    have hδ' : δ ∈ (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s'] '' componentRoots (rootCharHom a) j := by
      rw [← h, ← Set.image_comp]
      have e : ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s'] ∘ (S.ρ : (Fin Tag.E6.rank → ℤ) → _)) =
          (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s' + 1] := (Function.iterate_succ _ _).symm
      rw [e, hs]
      exact hδ
    obtain ⟨δ', hδ'j, rfl⟩ := hδ'
    exact ⟨k + s', δ', hδ'j, by rw [Function.iterate_add_apply]⟩
  · rintro ⟨k, δ, hδ, rfl⟩
    rw [← h] at hδ
    obtain ⟨δ', hδ', rfl⟩ := hδ
    exact ⟨k + 1, δ', hδ', by rw [Function.iterate_succ_apply]⟩

theorem rationalComponent_eq_of_rationalRoots_eq {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ} {i j : KernelComponent (rootCharHom a)}
    (h : rationalRoots S.ρ (rootCharHom a) i = rationalRoots S.ρ (rootCharHom a) j) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i = rationalComponent S.ρ S.Γ (rootCharHom a) j := by
  unfold rationalComponent rationalSpan
  rw [h]

theorem ratQuasiEq_holds : RatQuasiEq := by
  intro L _ _ p₀ S a hq2 hT hap _ i j hi hj
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := by
      rw [← hq2]
      exact S.hqpow.2
    have e : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
    rw [e, h2, zero_add]
    exact one_ne_zero
  have F := kac_facts h3 hap
  choose f hf using fun c => outer_exists_image_component S hT c
  have hinj : Function.Injective f := by
    intro c d h
    refine eq_of_componentRoots_eq ?_
    have h1 := hf c
    rw [h, ← hf d] at h1
    exact Set.image_injective.2 S.ρ.injective h1
  have hn : ∀ c, (componentRoots (rootCharHom a) (f c)).ncard =
      (componentRoots (rootCharHom a) c).ncard := fun c => by
    rw [← hf c]
    exact Set.ncard_image_of_injective _ S.ρ.injective
  have hQ2 : ∀ c, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) c) →
      (componentRoots (rootCharHom a) c).ncard ≠ 2 := by
    intro c hc h2
    have hne := orbit_ne_of_rank_one_quasisimple S hq2 hT c (F.rank_one c h2) h2 hc
    have hfc : f c = c := F.one (f c) c (by rw [hn c]; exact h2) h2
    exact hne (by rw [hf c, hfc])
  have hQ6 : ∀ c, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) c) →
      (componentRoots (rootCharHom a) c).ncard = 6 → f c ≠ c := by
    intro c hc h6 hfc
    exact orbit_ne_of_A2_quasisimple S hq2 hT c (F.frame c h6) (F.glue c h6) hc
      (by rw [hf c, hfc])
  rcases orbit_logic (fun c => (componentRoots (rootCharHom a) c).ncard) f hinj hn F.sizes F.big
    F.four F.three (fun c => CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) c))
    hQ2 hQ6 i j hi hj with h | h | h
  · rw [h]
  · exact rationalComponent_eq_of_rationalRoots_eq S (rationalRoots_eq_of_image S hT (h ▸ hf i))
  · exact (rationalComponent_eq_of_rationalRoots_eq S
      (rationalRoots_eq_of_image S hT (h ▸ hf j))).symm

end Rat

end TwE6UniqAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
