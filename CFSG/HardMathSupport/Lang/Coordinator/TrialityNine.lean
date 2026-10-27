module

public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicTwE6
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.RankThreeTheoremC


theorem exists_nine_graphFixedRootGroup_D4 (K : Type) [Field K] (σ : K ≃+* K) (hσ : σ ^ 3 = 1) :
    ∃ A : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  obtain ⟨ι, η, hι, hη, hcomm⟩ := triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσ
  have hker : ∀ {F : Type} [Field F] (R : SL2 F →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      Function.Injective R → ∀ g ∈ R.ker,
        ∃ l : F, (g : Matrix (Fin 2) (Fin 2) F) = l • 1 := fun R hR g hg => by
    have : g = 1 := hR (by rw [MonoidHom.mem_ker.1 hg, map_one])
    exact ⟨1, by rw [this]; simp⟩
  have hind := independent_of_commuting_sl2 ι η (fun g h => hcomm g h) (hker ι hι)
    (hker η hη)
  refine exists_isElemAbelian_card_nine_of_commute (ι (sl2OrderThree K))
    (η (sl2OrderThree (fixSubfield σ))) ?_ ?_ (hcomm _ _) hind
  · rw [← map_pow, sl2OrderThree_pow_three, map_one]
  · rw [← map_pow, sl2OrderThree_pow_three, map_one]

theorem exists_nine_of_trialityD4 {X : Type} [Group X] {ℓ f : ℕ}
    (h : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 ℓ f) :
    ∃ A : Subgroup X, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  obtain ⟨⟨hℓ, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel X .D4 (ℓ ^ f) := hm
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hℓ hf1 hm'
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields .D4 hℓ hf1 K hcard
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  subst hσσ'
  have h3 : σ' ^ 3 = 1 := by
    rw [← hord.trans (by rfl : TwistTag.D4.order = 3)]
    exact pow_orderOf_eq_one σ'
  exact exists_isElemAbelian_of_mulEquiv e.symm (exists_nine_graphFixedRootGroup_D4 K σ' h3)

end CFSG.HardMathSupport.Lang.Coordinator
