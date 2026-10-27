module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwist
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerCover
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayer
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.TwistedE6

section Layer

variable {p f : ℕ} [Fact p.Prime]

theorem map_twistedRootGroup_sup_fixed (hp2 : p ≠ 2) (hf : 1 ≤ f) {β : Fin (Tag.rank .E6) → ℤ}
    (hβ : IsRoot .E6 β) (hfix : rho β = β) :
    (twistedRootGroup (GaloisField p (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ p f)
        (proj β) ⊔
      twistedRootGroup (GaloisField p (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ p f)
        (-proj β)).map
      (CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi p f
        (AlgebraicClosure (GaloisField p (2 * f)))) =
      fixedPointsIn (rootSubgroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) β)
          (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
            (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f))))) ⊔
        fixedPointsIn (rootSubgroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f)))
            (-β))
          (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
            (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f))))) := by
  have hρneg : rho (-β) = -β := (permLattice_neg _ β).trans (congrArg Neg.neg hfix)
  rw [Subgroup.map_sup, CFSG.ClassicalInvolution.ModelFacts.map_twistedRootGroup_fixed p f hp2 hf
      hβ hfix, ← map_neg proj β,
    CFSG.ClassicalInvolution.ModelFacts.map_twistedRootGroup_fixed p f hp2 hf (IsRoot.neg hβ)
      hρneg]

theorem map_twistedRootGroup_theta (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    (twistedRootGroup (GaloisField p (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ p f)
        (proj e6Theta) ⊔
      twistedRootGroup (GaloisField p (2 * f)) (CFSG.LieType.Steinberg.Exceptional.frobQ p f)
        (-proj e6Theta)).map
      (CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi p f
        (AlgebraicClosure (GaloisField p (2 * f)))) =
      rankOneFix p (AlgebraicClosure (GaloisField p (2 * f))) f :=
  map_twistedRootGroup_sup_fixed hp2 hf isRoot_e6Theta perm_e6Theta

theorem twistedE6Layer : TwistedE6Layer p f := by
  classical
  intro hp2 hq n hadm
  obtain rfl : n = 0 := hadm.2.2
  have hf : 1 ≤ f := hadm.2.1
  set K0 := GaloisField p (2 * f) with hK0
  set k := AlgebraicClosure K0 with hk
  have hChark : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  have halg := CFSG.LieType.AlgebraicGroups.isAlgebraic_zmod_of_isAlgClosure p K0 k
  obtain ⟨L, hLR, hLq, hLC, hLP, hLcard⟩ := exists_twisted_layer (k := k) hp2 halg hf hq
  set Φ := CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi p f k with hΦ
  set Rθ : Subgroup (CFSG.LieType.Steinberg.Exceptional.twistedE6Group p f) :=
    twistedRootGroup K0 (CFSG.LieType.Steinberg.Exceptional.frobQ p f) (proj e6Theta) ⊔
      twistedRootGroup K0 (CFSG.LieType.Steinberg.Exceptional.frobQ p f) (-proj e6Theta) with hRθ
  have hRθmem : Rθ ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 p f Fact.out).D :=
    ⟨1, proj e6Theta, Or.inl (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_twistedDatum_proj
      (CFSG.LieType.Steinberg.Exceptional.frobQ p f) isRoot_e6Theta perm_e6Theta),
      (conjSub_one _).symm⟩
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .twistedE6 0 p f
    Fact.out trivial hadm (by decide) (by decide)
  have hperf := CFSG.ClassicalInvolution.ModelFacts.fundPerfect_twistedE6 p f hadm (by omega)
  have hmap : Rθ.map Φ = rankOneFix p k f := map_twistedRootGroup_theta hp2 hf
  have hrange := CFSG.ClassicalInvolution.ModelFacts.range_twistedE6Phi p f hp2 hf
  have hLθ : L ≤ Φ.range := by
    rw [hΦ, hrange]
    exact hLR
  have hlayer : LayerAt (fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 p f Fact.out).D)
      Rθ := by
    refine LayerAt.of_central_cover Φ
      (CFSG.ClassicalInvolution.ModelFacts.ker_twistedE6Phi_le_center p f k) hsingle hRθmem
      (hperf Rθ hRθmem) hLθ hLq ?_ ?_ ?_
    · rw [hmap]
      exact hLC
    · intro P hPΦ hPC hPperf
      rw [hmap] at hPC
      refine hLP P ?_ hPC hPperf
      rw [hΦ, hrange] at hPΦ
      exact hPΦ
    · rw [hmap]
      exact hLcard
  intro R₀ hR₀
  obtain ⟨g, hg⟩ := hsingle Rθ hRθmem R₀ hR₀
  rw [hg]
  exact LayerAt.conj (fun S hS g =>
    CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups hS g) hlayer g

theorem excLayer : ExcLayer p f :=
  excLayer_of_twistedE6 twistedE6Layer

theorem mfTwinExc : MFTwinExc p f :=
  mfTwinExc_of_layer excLayer

theorem mfTwin : MFTwin p f :=
  mfTwin_of_layer excLayer

end Layer

end CFSG.ClassicalInvolution.RouteD.Exotic
