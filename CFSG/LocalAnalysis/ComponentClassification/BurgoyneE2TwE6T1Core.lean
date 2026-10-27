module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Layer
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Root

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Q3 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped commutatorElement Pointwise


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_twenty_layer (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) :
    ∃ (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k) (u : ModGL TwistTag.E6.tag k),
      D.e = e ∧ D.χ = signMaskChar TwistTag.E6.tag 20 ∧
      (∀ γ, D.θ (toReal γ) =
        toReal (thetaMap (ToralSign.wordElt TwistTag.E6.tag []) TwistTag.E6.perm γ)) ∧
      Subsingleton (KernelComponent D.χ) ∧ CFSG.IsQuasisimple D.orbitGroup ∧
      u ∈ torusGroup TwistTag.E6.tag k ⊔
        rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 20)) ∧
      D.orbitGroup.map (MulAut.conj u).toMonoidHom ≤
        ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
          fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
        Subgroup.centralizer {(rootDiagUnit TwistTag.E6.tag
          (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag 20)))} ∧
      ∀ y ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) ⊓
        Subgroup.centralizer {(rootDiagUnit TwistTag.E6.tag
          (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag 20)))},
        (D.orbitGroup.map (MulAut.conj u).toMonoidHom).map (MulAut.conj y).toMonoidHom =
          D.orbitGroup.map (MulAut.conj u).toMonoidHom := by
  classical
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  obtain ⟨D, u, hDe, hDχ, hDθ, hsub, hqs, hu, hconj⟩ := exists_twenty_datum hp2 he hk
  refine ⟨D, u, hDe, hDχ, hDθ, hsub, hqs, hu, ?_⟩
  set F₁ := frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) with hF₁
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F₁ with hR
  set a := signCharTuple (k := k) (signMaskChar TwistTag.E6.tag 20) with ha
  set d := rootDiagUnit TwistTag.E6.tag a with hd
  set M := torusGroup TwistTag.E6.tag k ⊔
    rootSpan TwistTag.E6.tag k (kernelRoots (signMaskChar TwistTag.E6.tag 20)) with hM
  have hMZ : M = toralCentralizer TwistTag.E6.tag k a := by
    rw [← e6_toralRootGroup_eq hk2 (signCharTuple_sign _), toralRootGroup,
      rootCharKernel_signCharTuple hk2]
  set X₀ := fixedPointsIn M F₁ with hX₀
  have hX₀eq : X₀ = R ⊓ Subgroup.centralizer {d} := by
    ext y
    rw [hX₀, mem_fixedPointsIn, hMZ, mem_toralCentralizer, Subgroup.mem_inf, mem_fixedPointsIn,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨hyG, hyd⟩, hyF⟩
      refine ⟨⟨hyG, hyF⟩, ?_⟩
      calc y * d = (d * y * d⁻¹) * d := by rw [hyd]
        _ = d * y := by group
    · rintro ⟨⟨hyG, hyF⟩, hyd⟩
      refine ⟨⟨hyG, ?_⟩, hyF⟩
      rw [← hyd, mul_inv_cancel_right]
  set C' := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hC'
  have hCX : C' ≤ X₀ := by
    rintro _ ⟨c', hc', rfl⟩
    have h1 : c' ∈ D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype :=
      exc3_fixedGroup_le_totalFixedGroup D (exc3_orbitGroup_le_fixedGroup D hc')
    rw [← hconj]
    exact Subgroup.mem_map_of_mem _ h1
  have hqC : CFSG.IsQuasisimple C' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (D.orbitGroup.equivMapOfInjective _ (MulAut.conj u).injective) hqs
  have hperf : ⁅C', C'⁆ = C' := Subgroup.isPerfect_iff.1 hqC.1
  have hCR : C' ≤ R ⊓ Subgroup.centralizer {d} := hX₀eq ▸ hCX
  have hCeq : C' = ⁅⁅X₀, X₀⁆, ⁅X₀, X₀⁆⁆ := by
    rw [hC', orbitGroup_eq_derived_e6 D hqs, Subgroup.map_commutator, Subgroup.map_commutator,
      hconj]
  refine ⟨fun w hw => ⟨?_, (hCR hw).2⟩, fun y hy => ?_⟩
  · rw [← hperf] at hw
    exact Subgroup.commutator_mono (fun v hv => (hCR hv).1) (fun v hv => (hCR hv).1) hw
  · rw [← hX₀eq] at hy
    have hX0 : X₀.map (MulAut.conj y).toMonoidHom = X₀ := by
      refine le_antisymm ?_ fun v hv => ⟨y⁻¹ * v * y, mul_mem (mul_mem (inv_mem hy) hv) hy, ?_⟩
      · rintro _ ⟨v, hv, rfl⟩
        exact mul_mem (mul_mem hy hv) (inv_mem hy)
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    rw [hCeq, Subgroup.map_commutator, Subgroup.map_commutator, hX0]

section Four

variable (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)

theorem thetaMap_nil_four :
    thetaMap (ToralSign.wordElt TwistTag.E6.tag []) TwistTag.E6.perm (Pi.single (t1Node 3) 1) =
      Pi.single (t1Node 3) 1 := by
  rw [thetaMap, permLattice_single, wordElt_nil, one_smul]
  rfl

theorem thetaOrbit_four_e6
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt TwistTag.E6.tag []) TwistTag.E6.perm γ)) :
    thetaOrbit D.θ (Pi.single (t1Node 3) 1) = {Pi.single (t1Node 3) 1} := by
  have h1 : D.θ (toReal (Pi.single (t1Node 3) 1 : Fin TwistTag.E6.tag.rank → ℤ)) =
      toReal (Pi.single (t1Node 3) 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
    rw [hθ, thetaMap_nil_four]
  have hpow : ∀ m : ℕ, (D.θ ^ m)
      (toReal (Pi.single (t1Node 3) 1 : Fin TwistTag.E6.tag.rank → ℤ)) =
        toReal (Pi.single (t1Node 3) 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
    intro m
    induction m with
    | zero => rw [pow_zero, Module.End.one_apply]
    | succ m ih => rw [pow_succ, Module.End.mul_apply, h1, ih]
  ext β
  simp only [thetaOrbit, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm⟩
    rw [hpow] at hm
    exact (toReal_injective hm).symm
  · rintro rfl
    exact ⟨0, by rw [pow_zero, Module.End.one_apply]⟩

theorem rootSL2_mem_orbitGroup_four {K : Type} [Field K] [Finite K] [Algebra K k]
    (hK : Nat.card K = p ^ D.e)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt TwistTag.E6.tag []) TwistTag.E6.perm γ))
    (hΔ : Pi.single (t1Node 3) 1 ∈ D.simpleRootsJ) (B : SL2 K) :
    rootSL2 TwistTag.E6.tag k (Pi.single (t1Node 3) 1)
      (Matrix.SpecialLinearGroup.map (algebraMap K k) B) ∈ D.orbitGroup := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hO : ({Pi.single (t1Node 3) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ∈ D.orbits :=
    ⟨_, hΔ, (thetaOrbit_four_e6 D hθ).symm⟩
  have hcard : orbitCard ({Pi.single (t1Node 3) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)) = 1 :=
    Set.ncard_singleton _
  have hroot : orbitRoot ({Pi.single (t1Node 3) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)) =
      Pi.single (t1Node 3) 1 := D.orbitRoot_mem hO
  have hmap : ∀ A, D.orbitMap {Pi.single (t1Node 3) 1} A =
      rootSL2 TwistTag.E6.tag k (Pi.single (t1Node 3) 1)
        (Matrix.SpecialLinearGroup.map (D.orbitField {Pi.single (t1Node 3) 1}).subtype A) := by
    intro A
    rw [D.orbitMap_eq_prod, hcard, List.range_one, List.map_singleton, List.prod_singleton,
      D.orbitFactor_apply, D.orbitVec_zero, hroot, mul_zero, iterateFrobenius_zero]
    congr 1
  have hKO : ∀ c : K, algebraMap K k c ∈ D.orbitField {Pi.single (t1Node 3) 1} := by
    intro c
    rw [OrthogonalSemilinearFixedRootDatum.orbitField, hcard, mul_one,
      mem_frobeniusFixedField, ← hK, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set ι' : K →+* D.orbitField {Pi.single (t1Node 3) 1} :=
    (algebraMap K k).codRestrict _ hKO with hι'
  have h := D.orbitMap_mem_orbitGroup hO (Matrix.SpecialLinearGroup.map ι' B)
  have e : Matrix.SpecialLinearGroup.map (D.orbitField {Pi.single (t1Node 3) 1}).subtype
      (Matrix.SpecialLinearGroup.map ι' B) = Matrix.SpecialLinearGroup.map (algebraMap K k) B := by
    ext i j
    rfl
  rw [hmap, e] at h
  exact h

end Four

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
