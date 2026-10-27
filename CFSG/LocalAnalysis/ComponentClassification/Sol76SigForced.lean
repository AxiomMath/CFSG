module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigMoves

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

abbrev SigOrientation : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Subgroup G → Subgroup G → Subgroup G → Prop

@[expose] def WTrivialFor (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V = ⊥

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

@[expose] def SigEscape (N K K' : Subgroup G) (e f : G) : Prop :=
  (∃ V B : Subgroup G, SigPair N K K' V B ∧ f ∈ V ∧ e ∈ B) ∨
    (3 ≤ CFSG.Open.pRank 2 K ∧ ∃ V E : Subgroup G, IsKleinFour V ∧ V ≤ K' ∧ f ∈ V ∧
      IsKleinFour E ∧ E ≤ K ⊓ centralizer (V : Set G) ∧ e ∈ E ∧
      ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
        Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) ∨
    (∃ E : Subgroup G, IsKleinFour E ∧ E ≤ K ∧ e ∈ E ∧ f ∈ K' ⊓ centralizer (E : Set G) ∧
      (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected ∧
      ∃ t x : G, t ∈ K' ⊓ centralizer (E : Set G) ∧ orderOf t = 2 ∧ x ∈ N ∧
        x ∈ coreActionKernel K' ∧ orderOf x = 2 ∧ x ∉ E ∧ E ≤ centralizer ({x} : Set G) ∧
        x * t = t * x)

@[expose] def SigForced (R : SigOrientation) (N K K' : Subgroup G) (e f : G) : Prop :=
  (R G N K K' → ¬ SigEscape N K K' e f) ∧ (R G N K' K → ¬ SigEscape N K' K f e)

@[expose] def ForcedSeparationFor (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
    ∀ e ∈ K, orderOf e = 2 → ∀ f ∈ K', orderOf f = 2 → f * e = e * f →
      SigForced R N K K' e f →
      oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥

theorem oddCoreIn_inf_eq_bot_of_escape (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hW : ∀ V B : Subgroup G, SigPair N K K' V B → wGroup B V = ⊥) {e f : G}
    (he1 : e ≠ 1) (hf2 : orderOf f = 2) (hesc : SigEscape N K K' e f) :
    oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥ := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  rcases hesc with ⟨V, B, hP, hfV, heB⟩ | ⟨h3, V, E, hV, hVK', hfV, -, hEX, heE, hconn⟩ |
    ⟨E, hE, hEK, heE, hf, hconn, t, x, ht, ht2, hxN, hxQ, hx2, hxE, hEx, hxt⟩
  · exact oddCoreIn_inf_eq_bot_of_sigPair hP (hW V B hP) heB he1 hfV
  · exact oddCoreIn_inf_eq_bot_of_twoConnected h32 hG hN hK hK' hne hV hVK' hEX h3 hconn
      (fun B hP => hW V B hP) heE he1 hfV
  · exact oddCoreIn_inf_eq_bot_of_preconnected h32 hG hN hK hK' hne hE hEK hconn ht ht2 hxN hxQ
      hx2 hxE hEx hxt hW heE he1 hf hf2

theorem forced_facts {R : SigOrientation} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {e f : G} (heK : e ∈ K)
    (he2 : orderOf e = 2) (hfK' : f ∈ K') (hf2 : orderOf f = 2) (hfe : f * e = e * f)
    (hR : R G N K K') (hR' : R G N K' K) (hF : SigForced R N K K' e f) :
    CFSG.Open.pRank 2 (K ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G)) ≤ 2 ∧
      CFSG.Open.pRank 2 (K' ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G)) ≤ 2 ∧
      ∀ b ∈ N ⊓ coreActionKernel K ⊓ coreActionKernel K', orderOf b = 2 →
        b * e = e * b → b * f = f * b → b ∈ K ⊓ K' := by
  rcases exists_sigPair_or_forced hK hK' hne heK he2 hfK' hf2 hfe with h | h | h
  · exact (hF.1 hR (Or.inl h)).elim
  · exact (hF.2 hR' (Or.inl h)).elim
  · exact h

theorem oddCoreSeparatedFor_of_forced (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) {R : SigOrientation}
    (hW : WTrivialFor R) (hres : ForcedSeparationFor R) : OddCoreSeparatedFor simpleAmbient := by
  intro G _ _ hG N hN K hK K' hK' hne e heK he2 f hfK' hf2 hfe
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he2; norm_num at he2
  have hf1 : f ≠ 1 := fun h => by rw [h, orderOf_one] at hf2; norm_num at hf2
  by_cases h1 : R G N K K' ∧ SigEscape N K K' e f
  · exact oddCoreIn_inf_eq_bot_of_escape hq hR1 hG hN hK hK' hne
      (fun V B hP => hW G hG N hN K K' V B hP h1.1) he1 hf2 h1.2
  by_cases h2 : R G N K' K ∧ SigEscape N K' K f e
  · rw [inf_comm]
    exact oddCoreIn_inf_eq_bot_of_escape hq hR1 hG hN hK' hK hne.symm
      (fun V B hP => hW G hG N hN K' K V B hP h2.1) hf1 he2 h2.2
  exact hres G hG N hN K hK K' hK' hne e heK he2 f hfK' hf2 hfe
    ⟨fun hR hesc => h1 ⟨hR, hesc⟩, fun hR hesc => h2 ⟨hR, hesc⟩⟩

theorem lemma315bInputFor_simple_of_forced (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) {R : SigOrientation}
    (hW : WTrivialFor R) (hres : ForcedSeparationFor R) : Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_of_separated (lemma32FullFor_simple_of_twoPart hq hR1)
    (oddCoreSeparatedFor_of_forced hq hR1 hW hres)

end CFSG.ComponentClassification.Sol76.Sig
