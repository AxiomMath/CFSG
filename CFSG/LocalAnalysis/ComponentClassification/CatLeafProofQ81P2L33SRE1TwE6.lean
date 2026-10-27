module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Map
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Masks
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistReduction
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E1

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Foote5.OddLieCore (oddFixed)


theorem twisted_exists_lift (t : TwistTag) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (p ^ f) ^ t.order) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) [CharP (AlgebraicClosure F) p]
    (x : graphFixedRootGroup t F σ.toRingHom) :
    entryLift (graphFixedRootGroup t F σ.toRingHom) x ∈
        ⁅fixedPointsIn (adjointGroup t.tag (AlgebraicClosure F))
            (frobTwistGL t.tag (AlgebraicClosure F) p f (diagramMap t (AlgebraicClosure F))),
          fixedPointsIn (adjointGroup t.tag (AlgebraicClosure F))
            (frobTwistGL t.tag (AlgebraicClosure F) p f (diagramMap t (AlgebraicClosure F)))⁆ ∧
      (fixedSubgroup (MulAut.conj x)).map (entryLift (graphFixedRootGroup t F σ.toRingHom)) =
        ⁅fixedPointsIn (adjointGroup t.tag (AlgebraicClosure F))
            (frobTwistGL t.tag (AlgebraicClosure F) p f (diagramMap t (AlgebraicClosure F))),
          fixedPointsIn (adjointGroup t.tag (AlgebraicClosure F))
            (frobTwistGL t.tag (AlgebraicClosure F) p f (diagramMap t (AlgebraicClosure F)))⁆ ⊓
          centralizer {entryLift (graphFixedRootGroup t F σ.toRingHom) x} := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, -, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group t
    hp hf hodd F hF σ.toRingHom hσ (AlgebraicClosure F)
    (iterateFrobenius (AlgebraicClosure F) p f) (fun c => iterateFrobenius_def p f c)
  set ι := baseChangeGL (τ := t.tag) (algebraMap F (AlgebraicClosure F)) with hιdef
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  set R := fixedPointsIn (adjointGroup t.tag (AlgebraicClosure F))
    (frobTwistGL t.tag (AlgebraicClosure F) p f (diagramMap t (AlgebraicClosure F))) with hR
  have hRtw : R = twistedFixedGroup t (AlgebraicClosure F)
      (iterateFrobenius (AlgebraicClosure F) p f) := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL t.tag (AlgebraicClosure F) p f (diagramMap t (AlgebraicClosure F)) y = y ↔
      twistHom t (AlgebraicClosure F) (iterateFrobenius (AlgebraicClosure F) p f) y = y
    rw [frobTwistGL_apply, twistHom_apply]
  have hRA : ⁅R, R⁆ = (graphFixedRootGroup t F σ.toRingHom).map ι := by
    rw [hRtw]
    exact hder
  have hxl : entryLift (graphFixedRootGroup t F σ.toRingHom) x = ι x := rfl
  refine ⟨by rw [hRA, hxl]; exact ⟨_, x.2, rfl⟩, ?_⟩
  rw [hRA, hxl]
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, c.2, rfl⟩, ?_⟩
    have hc' : x * c * x⁻¹ = c := hc
    have hxc : x * c = c * x := mul_inv_eq_iff_eq_mul.1 hc'
    change ι (c : ModGL t.tag F) * ι x = ι x * ι (c : ModGL t.tag F)
    rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hxc]
  · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
    refine ⟨⟨c, hc⟩, ?_, rfl⟩
    have hcx' : ι c * ι x = ι x * ι c := hcx
    rw [← map_mul, ← map_mul] at hcx'
    have hxc : x * ⟨c, hc⟩ = ⟨c, hc⟩ * x := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact (hιinj hcx').symm
    change x * ⟨c, hc⟩ * x⁻¹ = ⟨c, hc⟩
    rw [hxc, mul_inv_cancel_right]

theorem twistedE6_orbit_component {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) [CharP (AlgebraicClosure F) p]
    {x : graphFixedRootGroup TwistTag.E6 F σ.toRingHom} (hx2 : x ^ 2 = 1) :
    ∃ (D' : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p (AlgebraicClosure F))
      (J' : Set.range D'.classOrbit) (w : ModGL TwistTag.E6.tag (AlgebraicClosure F)),
      GorensteinWalter.IsComponentOf ((conjOrbitGroup D' J' w).comap
          (entryLift (graphFixedRootGroup TwistTag.E6 F σ.toRingHom)))
          (oddFixed (MulAut.conj x)) ∧
        ((conjOrbitGroup D' J' w).comap
          (entryLift (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))).map
          (entryLift (graphFixedRootGroup TwistTag.E6 F σ.toRingHom)) =
          conjOrbitGroup D' J' w := by
  set k := AlgebraicClosure F
  have hF2 : Nat.card F = p ^ (f * 2) := by rw [hF, ← pow_mul]
  have : CharP F p := finite_field_prime_power_characteristic (Fact.out : p.Prime) (by omega) hF2
  have hk := isAlgebraic_zmod_of_isAlgClosure p F k
  obtain ⟨hxR', hmap⟩ := twisted_exists_lift TwistTag.E6 hp2 hf hF σ hσ x
  set x' := entryLift (graphFixedRootGroup TwistTag.E6 F σ.toRingHom) x with hx'
  have hxR : x' ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)) :=
    commutator_le_self _ hxR'
  have hx'2 : x' ^ 2 = 1 := by rw [hx', ← map_pow, hx2, map_one]
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp2 f hf
  have hdiag : Finite (fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k))) :=
    finite_fixedPointsIn_frobTwistGL p hf (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (iterateFrobenius k p f))
      (diagramMap_pow_order TwistTag.E6 k)
  have hred : ∃ m ∈ e6SignDiagramReps, ∃ l ∈ m.omegaWords,
      ∃ g₁ ∈ adjointGroup TwistTag.E6.tag k,
        g₁ * x' * g₁⁻¹ = rootDiagUnit TwistTag.E6.tag
          (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag m.mask)) ∧
        g₁ * (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k) g₁)⁻¹ =
          wordWeylMatrix TwistTag.E6.tag k l := by
    obtain ⟨r, hr, l, hl, -, -, g₁, hg₁, hg₁x, hg₁F, -⟩ :=
      isFiniteToralTwistReduction_of_reps_exact p hp2 hf
        (map_conj_diagramMap TwistTag.E6 k (Or.inl rfl)) TwistTag.E6.perm
        (fun b hb => frobTwistGL_diagramMap_rootDiagUnit_of_sign p TwistTag.E6 f hb)
        e6SignDiagramReps h6.permChar_eq h6.exists_rep h6.coe_kernelPosStabilizer hdiag hxR hx'2
    exact ⟨r, hr, l, hl, g₁, hg₁, hg₁x, hg₁F⟩
  exact exists_orbit_component_of_map (MulAut.conj x) (entryLift _) (entryLift_injective _) hp2
    hk hf (Or.inr (Or.inl rfl)) TwistTag.E6.cartan_perm symmetrizedCartan_perm_E6 h6.theta
    (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
    (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 _ (Or.inl rfl)) n6
    e6_exists_pair hmap hred

end CFSG.ComponentClassification.HarrisLit.L33.SR.E1
