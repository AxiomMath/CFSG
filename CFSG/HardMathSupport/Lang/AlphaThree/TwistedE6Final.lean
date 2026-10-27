module

public import CFSG.HardMathSupport.Lang.AlphaThree.TwistedE6Commutator
public import CFSG.HardMathSupport.Lang.AlphaThree.TwistedE6Assembly

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.AlphaThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.AGLEmbedding.KFactProofs.CoverE6 (fourRoots)


section Gen

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem closure_pairCentralizing_eq_top_twistedE6 (hσσ : ∀ c, σ (σ c) = c)
    (hσ1 : ∃ c, σ c ≠ c)
    (h : Fin 4 → ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hmem : ∀ i, ((h i : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
      ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K (fourRoots i) ⊔
        rootSubgroup TwistTag.E6.tag K (-fourRoots i)) :
    Subgroup.closure (CFSG.AGLEmbedding.pairCentralizing h) = ⊤ := by
  set M := Subgroup.closure (CFSG.AGLEmbedding.pairCentralizing h) with hMdef
  have hle := graphFixedRootGroup_le_of_orbitGroups (t := TwistTag.E6) σ.toRingHom σ.surjective
    (M.map (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype) (by
      rintro O ⟨α, hα, rfl⟩ u hu
      obtain ⟨hur, huΓ⟩ := Subgroup.mem_inf.1 hu
      have hset : ((TwistTag.E6.diagramOrbit α : Finset E6Vec) : Set E6Vec) =
          ({α, rhoE6 α} : Set E6Vec) := by
        rw [diagramOrbit_E6]
        simp
      rw [hset] at hur
      have hρ : IsRoot TwistTag.E6.tag (rhoE6 α) := isRoot_rhoE6 hα
      have hG : u ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
        rcases IsRoot.height_pos_or_neg hα with hpos | hneg
        · have : u ∈ posUnipotent TwistTag.E6.tag K := rootSpan_le_posUnipotent (fun β hβ => by
            rcases hβ with rfl | hβ
            · exact ⟨hα, hpos⟩
            · rw [Set.mem_singleton_iff] at hβ
              subst hβ
              exact ⟨hρ, by rw [rhoE6, height_permLattice]; exact hpos⟩) hur
          exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
            (Subgroup.mem_inf.2 ⟨this, huΓ⟩)
        · have : u ∈ negUnipotent TwistTag.E6.tag K := rootSpan_le_negUnipotent (fun β hβ => by
            rcases hβ with rfl | hβ
            · exact ⟨hα, hneg⟩
            · rw [Set.mem_singleton_iff] at hβ
              subst hβ
              exact ⟨hρ, by rw [rhoE6, height_permLattice]; exact hneg⟩) hur
          exact graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
            (Subgroup.mem_inf.2 ⟨this, huΓ⟩)
      exact ⟨⟨u, hG⟩, orbit_mem_closure hσσ hσ1 h hmem hα ⟨u, hG⟩ hur, rfl⟩)
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hyM, hy⟩ := hle x.2
  have : y = x := Subtype.ext hy
  rw [← this]
  exact hyM

theorem twistedE6_generation (q : TauCeti.PrimePower) [Finite K] (σ : K →+* K)
    (hK : Nat.card K = q.card ^ 2) (hσ : ∀ c, σ c = c ^ q.card)
    (h : Fin 4 → ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hmem : ∀ i, ((h i : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K) ∈
      rootSubgroup TwistTag.E6.tag K (CFSG.AGLEmbedding.KFactProofs.CoverE6.fourRoots i) ⊔
        rootSubgroup TwistTag.E6.tag K
          (-CFSG.AGLEmbedding.KFactProofs.CoverE6.fourRoots i)) :
    Subgroup.closure (CFSG.AGLEmbedding.pairCentralizing h) = ⊤ := by
  have hp : q.p.Prime := q.prime_p
  have : Fact q.p.Prime := ⟨hp⟩
  have hUD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData q.p q.exponent K :=
    ⟨hp, q.exponent_pos, by rw [hK, TauCeti.PrimePower.card_def, ← pow_mul, mul_comm]⟩
  have hσbar : ∀ c, σ c = hUD.bar c := fun c => by
    rw [hσ, hUD.bar_apply, TauCeti.PrimePower.card_def]
  let σe : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσσ : ∀ c, σe (σe c) = c := fun c => by
    change σ (σ c) = c
    rw [hσbar, hσbar, hUD.bar_bar]
  have hσ1 : ∃ c, σe c ≠ c := by
    obtain ⟨c, hc⟩ := hUD.exists_bar_ne
    exact ⟨c, by change σ c ≠ c; rwa [hσbar]⟩
  exact closure_pairCentralizing_eq_top_twistedE6 (σ := σe) hσσ hσ1 h hmem

end Gen

section Final


theorem liftableNormalizerGen_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq3 : 3 ∣ q.card + 1) :
    CFSG.AGLEmbedding.LiftableNormalizerGen
      (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) := by
  exact liftableNormalizerGen_twistedE6_of_gen q hv hq3
    (fun K _ _ σ hK hσ h hh => twistedE6_generation q σ hK hσ h hh)

end Final

end CFSG.HardMathSupport.Lang.AlphaThree
