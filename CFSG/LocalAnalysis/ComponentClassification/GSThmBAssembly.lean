module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBIsoInput

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def Hyp52ContradictionStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → False

theorem orbitLayerStatement_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput) :
    ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
      Assembly.KProper Blueprint.Catalog X →
      ∀ (a : X) (J S : Subgroup X), orderOf a = 2 → J ≤ centralizer ({a} : Set X) →
        IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))) →
        S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
        (∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
          (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) →
        ∀ B : Subgroup X, B ≠ ⊥ → B ≤ S ⊓ coreActionKernel J →
          ∃ M : Subgroup X, M ≤ normalizer (B : Set X) ∧
            IsPComponent 2 (M.subgroupOf (normalizer (B : Set X))) ∧
            conjClosure (GSLit.fixedLayer J B) (layerIn (normalizer (B : Set X))) =
              M ⊔ conjugate M a := by
  intro X _ _ _ hnonab hK a J S ha hJa hJ hSX hSsyl B hB hBP
  obtain ⟨-, -, -, -, -, -, -, ⟨M, hMH, hM, -, hVM, -⟩, -⟩ :=
    (actual_two_local_fixed_layer_orbits_of_inputs hS hU hheld hnonab hK ha hJa hJ hSX hSsyl rfl
      (fun B => normalizer (B : Set X)) (fun B => oddCoreIn (normalizer (B : Set X)))
      (fun B => GSLit.fixedLayer J B)
      (fun B => GSLit.fixedLayer J B ⊔ oddCoreIn (normalizer (B : Set X)))
      (fun B => layerIn (normalizer (B : Set X)))
      (fun B => conjClosure (GSLit.fixedLayer J B) (layerIn (normalizer (B : Set X))))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun W => Nat.card ((↥W ⧸ pPrimeCore 2 ↥W) ⧸ center (↥W ⧸ pPrimeCore 2 ↥W)))
      (fun _ => rfl)).1 B hB hBP
  exact ⟨M, hMH, hM, hVM⟩

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_sylow_mem {H : Subgroup X} {x : X} (hxH : x ∈ H) (hx : orderOf x = 2) :
    ∃ S : Subgroup X, S ≤ H ∧ (∃ P : Sylow 2 ↥H, (P : Subgroup _) = S.subgroupOf H) ∧ x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers (⟨x, hxH⟩ : H)) := IsPGroup.of_card (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  refine ⟨(P : Subgroup H).map H.subtype, map_subtype_le _, ⟨P, ?_⟩, ⟨_, hP (mem_zpowers _), rfl⟩⟩
  ext y
  simp [mem_subgroupOf]

theorem gilman_solomon_theorem_B_iso_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hCTI : LayerGeneratedUniversalComponentStandard) (hRS : RestrictedStandardInput)
    (hcontra : Hyp52ContradictionStatement) : TheoremBIsoInput := by
  have horbit := orbitLayerStatement_of_inputs hS hU hheld
  intro X _ _ _ hnonab hK hz hUo a x J hmax hiso htype
  have hB2b : ConclusionB2b a J := conclusionB2b_of_maximal hmax
  by_cases hB1 : ConclusionB1 J
  · exact Or.inl hB1
  by_cases hB2a : ConclusionB2a a J
  · exact Or.inr ⟨hB2a, hB2b⟩
  exfalso
  obtain ⟨ha, hx, hax, hJa, hJpc, -, -⟩ := gsUnbalancingTriple_iff.mp hmax.1
  have hxH : x ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hax.symm,
      mem_normalizer_of_gsUnbalancingTriple hmax.1⟩
  obtain ⟨S, hSX, hSsyl, hxS⟩ := exists_sylow_mem hxH hx
  have htype' : 2 ≤ pRank 2 ↥J ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        Assembly.LowTwoRank.StatedClassicalModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
      Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
      Assembly.LowTwoRank.StatedClassicalModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2 := by
    rcases htype with h7 | ⟨p, f, hp, hp2, hf, -, hm⟩ | h34
    · exact Or.inr (Or.inr (Or.inl h7))
    · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, GSLit.statedClassicalModel_of_lieModel_psl_two hm⟩)
    · exact Or.inr (Or.inr (Or.inr (GSLit.statedClassicalModel_of_lieModel_psl_three h34)))
  rcases original_maximal_triple_critical_standard_dichotomy_of_inputs hS hU hheld hCTI
      hnonab hK ha hJa hJpc hSX hSsyl rfl
      (fun B => normalizer (B : Set X)) (fun B => oddCoreIn (normalizer (B : Set X)))
      (fun B => GSLit.fixedLayer J B)
      (fun B => GSLit.fixedLayer J B ⊔ oddCoreIn (normalizer (B : Set X)))
      (fun B => layerIn (normalizer (B : Set X)))
      (fun B => conjClosure (GSLit.fixedLayer J B) (layerIn (normalizer (B : Set X))))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      _ (fun _ => rfl) hmax hiso htype' with hall | hcrit
  · exact hB2a (conclusionB2a_of_sylow hSsyl fun b hb hb2 => hall b hb2 hb)
  obtain ⟨h, rfl, rfl, rfl, rfl⟩ := hyp52_of_criticalAlternative hS hRS hnonab hK hmax hiso
    htype hSX hSsyl hxS (horbit X hnonab hK a J S ha hJa hJpc hSX hSsyl) hcrit
  exact hcontra X hnonab hK hz hUo h hmax hiso hB1 hB2a

end CFSG.ComponentClassification.GSThmB
