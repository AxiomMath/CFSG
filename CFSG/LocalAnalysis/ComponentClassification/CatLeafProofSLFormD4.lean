module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormD4Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormUniform
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem oddTrialityInnerSLForm_holds
    :
    ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .trialityD4 0 p f →
      Blueprint.LieModel J .trialityD4 0 p f → ∀ α : MulAut J, orderOf α = 2 →
        α ∈ (MulAut.conj : J →* MulAut J).range →
        (∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L) ∧
          ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
            SLComponentForm K (fixedSubgroup α) := by
  classical
  intro J _ p f hp hp2 hadm hm α hα hαi
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have htw : TwistedChevalleyModel J .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hβi : β ∈ (MulAut.conj : C →* MulAut C).range := by
    change MulAut.congr e α ∈ OuterAutomorphisms.inner C
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαi
  obtain ⟨c, hc⟩ := hβi
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσ
  have hc2 : c ^ 2 = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hc, hβ2, map_one])
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have hK3' : Nat.card K = p ^ (3 * f) := by rw [hK3, ← pow_mul, mul_comm]
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3'
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have halg := isAlgebraic_zmod_of_isAlgClosure p K k
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.D4
    hp hf hodd K hK3 σ.toRingHom hσ k Fr hFr
  have hRF : fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) =
        twistedFixedGroup TwistTag.D4 k Fr := rfl
  set y := baseChangeGL ι (c : ModGL TwistTag.D4.tag K) with hydef
  have hyR : y ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) := by
    rw [hRF]
    exact hHR ⟨c, c.2, rfl⟩
  have hy2 : y ^ 2 = 1 := by
    rw [hydef, ← map_pow, ← Subgroup.coe_pow, hc2, Subgroup.coe_one, map_one]
  let φ : C →* ModGL TwistTag.D4.tag k := (baseChangeGL ι).comp C.subtype
  have hφ : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hmap : (fixedSubgroup (MulAut.conj c)).map φ =
      ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {y} := by
    rw [hRF, hder]
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a, a.2, rfl⟩, ?_⟩
      have ha' : c * a * c⁻¹ = a := ha
      have hac : a * c = c * a := by
        calc a * c = c * a * c⁻¹ * c := by rw [ha']
          _ = c * a := by group
      change baseChangeGL ι (a : ModGL TwistTag.D4.tag K) * y =
        y * baseChangeGL ι (a : ModGL TwistTag.D4.tag K)
      rw [hydef, ← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hac]
    · rintro ⟨⟨a, ha, rfl⟩, hay⟩
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      change c * ⟨a, ha⟩ * c⁻¹ = ⟨a, ha⟩
      have hac : (⟨a, ha⟩ : C) * c = c * ⟨a, ha⟩ := by
        refine Subtype.ext (baseChangeGL_injective ι ?_)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact hay
      rw [← hac]
      group
  set N := ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k))⁆ ⊓
      Subgroup.centralizer {y} with hN
  let Φ : fixedSubgroup (MulAut.conj c) ≃* N :=
    ((fixedSubgroup (MulAut.conj c)).equivMapOfInjective φ hφ).trans
      (MulEquiv.subgroupCongr hmap)
  let Ψ : fixedSubgroup α ≃* N := ((fixedSubgroupCongrEquiv e α).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc.symm))).trans Φ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite N := Finite.of_equiv _ Φ.toEquiv
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, -, n4⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp2 f hf
  obtain ⟨-, -, r4⟩ := rational_inner_involution_finite_toral_twist_reduction p k hp2 f hf
  have h2 : ∀ L₀ : Subgroup N, IsPComponent 2 L₀ → L₀.map N.subtype ≤ N ∧
      IsPComponent 2 ((L₀.map N.subtype).subgroupOf N) := fun L₀ hL₀ => by
    have hsub : (L₀.map N.subtype).subgroupOf N = L₀ :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective L₀
    exact ⟨Subgroup.map_subtype_le _, by rw [hsub]; exact hL₀⟩
  have key : ∀ L₀ : Subgroup N, IsPComponent 2 L₀ →
      ∃ Dd : OrthogonalSemilinearFixedRootDatum TwistTag.D4.tag p k,
        (∃ m ∈ d4SignDiagramReps, ∃ l ∈ m.omegaWords,
          Dd.χ = signMaskChar TwistTag.D4.tag m.mask ∧ ∀ γ, Dd.θ (toReal γ) =
            toReal (thetaMap (ToralSign.wordElt TwistTag.D4.tag l) TwistTag.D4.perm γ)) ∧
        Dd.e = f ∧ ∀ L : Subgroup N, IsPComponent 2 L → ∃ J' : Set.range Dd.classOrbit,
          IsQuasisimple (Dd.withOrbit J').orbitGroup ∧
            Nonempty (L ≃* (Dd.withOrbit J').orbitGroup) := by
    intro L₀ hL₀
    obtain ⟨Dd, hml, hDe, hXfin, hall⟩ := exists_datum_uniform_of_twistReduction p hp2 halg hf
      (τ := TwistTag.D4.tag) (Or.inl rfl) TwistTag.D4.cartan_perm symmetrizedCartan_perm_D4
      h4.theta (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.D4 l hγ)
      (diagramMap_mem_normalizer TwistTag.D4) (map_conj_diagramMap TwistTag.D4 _ (Or.inl rfl))
      n4 (r4 y hyR hy2) _ (h2 L₀ hL₀).1 (h2 L₀ hL₀).2
    refine ⟨Dd, hml, hDe, fun L hL => ?_⟩
    obtain ⟨J₀, hJ₀X, hJ₀c, ⟨eL⟩⟩ := hall _ (h2 L hL).1 (h2 L hL).2
    obtain ⟨J', hJ', hq⟩ := ExcSelector.exists_eq_orbitGroupC_of_isPComponent' Dd hXfin hJ₀X hJ₀c
    exact ⟨J', hq, ⟨((L.equivMapOfInjective _ N.subtype_injective).trans
      (eL.trans (MulEquiv.subgroupCongr hJ'))).trans
        (Subgroup.subgroupOfEquivOfLe (Dd.withOrbit J').orbitGroup_le_adjointGroup)⟩⟩
  refine ⟨fun L hL => ?_, ?_⟩
  ·
    have hL' : IsPComponent 2 (L.map Ψ.toMonoidHom) :=
      LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ hL
    obtain ⟨Dd, -, -, hall⟩ := key _ hL'
    obtain ⟨J', hq, ⟨eL⟩⟩ := hall _ hL'
    exact LocalCores.isQuasisimple_of_mulEquiv
      ((L.equivMapOfInjective _ Ψ.injective).trans eL).symm hq
  intro K' _ _ hKq
  refine slComponentForm_of_mulEquiv Ψ ?_
  by_cases hex : ∃ L₀ : Subgroup N, IsComponent L₀
  swap
  · intro L hL
    exact absurd ⟨L, hL⟩ hex
  obtain ⟨L₀, hL₀⟩ := hex
  obtain ⟨Dd, ⟨mr, hmr, l, hl, hDχ, hDθ⟩, hDe, hall⟩ :=
    key L₀ (isPComponent_two_of_isComponent hL₀)
  have hJ : ∀ L : Subgroup N, IsComponent L → ∃ J' : Set.range Dd.classOrbit,
      IsQuasisimple (Dd.withOrbit J').orbitGroup ∧
        Nonempty (L ≃* (Dd.withOrbit J').orbitGroup) :=
    fun L hL => hall L (isPComponent_two_of_isComponent hL)
  have hKe : Nat.card K' = p ^ Dd.e := by
    rw [hDe]
    exact hKq
  have hθ := h4.theta mr hmr l hl
  simp only [d4SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hmr
  rcases hmr with rfl | rfl
  ·
    simp only [d4OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    obtain ⟨hfix, hΔ⟩ := d4_zero_datum_classes Dd hDχ hDθ
    exact slComponentForm_of_datum_classes Dd hKe hJ (S := Set.range d4FundRoot) ⟨2, rfl⟩ hfix
      fun J' hq => Or.inl (hΔ J' hq)
  ·
    have hθ' : ThetaProperties TwistTag.D4.perm 3 Dd.χ
        (ToralSign.wordElt TwistTag.D4.tag l) := by
      rw [hDχ]
      exact hθ
    refine slComponentForm_of_SL_q_or_cube fun L hL => ?_
    obtain ⟨J', -, ⟨eL⟩⟩ := hJ L hL
    obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := d4_four_orbitGroup_mulEquiv_SL Dd hDχ hθ' hDθ J'
    refine ⟨F, inferInstance, inferInstance, ?_, ⟨eL.trans eF⟩⟩
    rw [hKe]
    exact hF

end CFSG.ComponentClassification.CatLeafProof
