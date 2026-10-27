module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Red

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E1

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Foote5.OddLieCore (oddFixed)

@[expose] noncomputable def entryLift
    {τ : Tag} {K : Type} [Field K] (S : Subgroup (ModGL τ K)) :
    S →* ModGL τ (AlgebraicClosure K) :=
  (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp S.subtype

theorem entryLift_injective
    {τ : Tag} {K : Type} [Field K] (S : Subgroup (ModGL τ K)) :
    Function.Injective (entryLift S) :=
  (baseChangeGL_injective _).comp Subtype.val_injective


variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_orbit_component_of_map {S : Type} [Group S] [Finite S] (α : MulAut S)
    (φ : S →* ModGL τ k) (hφ : Function.Injective φ) (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r₀ : ℕ}
    {reps : List (SignRep τ)}
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ r₀ (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    (hwit : ∀ m ∈ reps, ∃ β ∈ kernelRoots (signMaskChar τ m.mask),
      ∃ γ ∈ kernelRoots (signMaskChar τ m.mask), iform β γ = 1)
    {x : ModGL τ k}
    (hmap : (fixedSubgroup α).map φ =
      ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
        fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ centralizer {x})
    (hred : ∃ m ∈ reps, ∃ l ∈ m.omegaWords, ∃ g₁ ∈ adjointGroup τ k,
      g₁ * x * g₁⁻¹ = rootDiagUnit τ (signCharTuple (k := k) (signMaskChar τ m.mask)) ∧
        g₁ * (frobTwistGL τ k p e D g₁)⁻¹ = wordWeylMatrix τ k l) :
    ∃ (D' : OrthogonalSemilinearFixedRootDatum τ p k) (J' : Set.range D'.classOrbit)
      (w : ModGL τ k),
      GorensteinWalter.IsComponentOf ((conjOrbitGroup D' J' w).comap φ) (oddFixed α) ∧
        ((conjOrbitGroup D' J' w).comap φ).map φ = conjOrbitGroup D' J' w := by
  obtain ⟨D', J', w, hle, hsn, hq⟩ :=
    exists_conjOrbitGroup_component hp hk he hτ hA hB htheta hDX hDT hDG hpin hwit hred
  exact ⟨D', J', w, isComponentOf_oddFixed_of_map α φ hφ hmap hle hsn hq⟩

end CFSG.ComponentClassification.HarrisLit.L33.SR.E1
