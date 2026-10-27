module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieQuat
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameC3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormUniform
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddRational
public import CFSG.LocalAnalysis.SteinbergBMOddResidualE7Lift

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.ClassicalInvolution.ModelFacts
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem exists_quaternion_orbitGroup
    {τ : Tag} (D : OrthogonalSemilinearFixedRootDatum τ p k) {r₀ : ℕ}
    (hr₀ : ((τ = .E6 ∨ τ = .E7) ∧ r₀ = 2) ∨ (τ = .D4 ∧ r₀ = 3))
    {ρ : Equiv.Perm (Fin τ.rank)} {ω : WeylGroup τ} (hθ : ThetaProperties ρ r₀ D.χ ω)
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap ω ρ γ)) (J' : Set.range D.classOrbit)
    (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    ∃ H : Subgroup (D.withOrbit J').orbitGroup, Nonempty (H ≃* QuaternionGroup 2) := by
  obtain ⟨O, hO⟩ : (D.withOrbit J').orbits.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hbot : (D.withOrbit J').orbitGroup = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨O, hO, -⟩
      rw [hne] at hO
      exact absurd hO (Set.notMem_empty O)
    exact (Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq) hbot
  have hcard := orbitCard_eq_of_thetaProperties (D.withOrbit J') hθ hDθ hO
  have hne := ExcSelector.orbitMap_neg_one_ne_one (D.withOrbit J') hr₀ hO hcard
  have : Finite ((D.withOrbit J').orbitField O) :=
    ExcSelector.finite_orbitField' (D.withOrbit J') hO
  refine UnbalancedGS.SymplecticExclusion.exists_quaternion_of_sl2_hom
    (ExcSelector.ringChar_subfield_ne_two D.ringChar_ne_two _)
    ((D.withOrbit J').orbitGroupHom hO) fun h => hne ?_
  exact congrArg Subtype.val h

theorem quatComponentForm_of_twistReduction
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r₀ : ℕ}
    (hr₀ : ((τ = .E6 ∨ τ = .E7) ∧ r₀ = 2) ∨ (τ = .D4 ∧ r₀ = 3))
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
    {x : ModGL τ k} (hred : IsFiniteToralTwistReduction τ k p e D reps x)
    [Finite ↥(⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x})] :
    QuatComponentForm ↥(⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}) := by
  set N := ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}
    with hN
  intro L hL
  have hL2 : IsPComponent 2 L := isPComponent_two_of_isComponent hL
  have hsub : (L.map N.subtype).subgroupOf N = L :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective L
  have hL2' : IsPComponent 2 ((L.map N.subtype).subgroupOf N) := by rw [hsub]; exact hL2
  obtain ⟨Dd, ⟨m, hm, l, hl, hDχ, hDθ⟩, -, hXfin, hall⟩ :=
    exists_datum_uniform_of_twistReduction p hp hk he hτ hA hB htheta hDX hDT hDG hpin hred
      (L.map N.subtype) (Subgroup.map_subtype_le _) hL2'
  obtain ⟨J₀, hJ₀X, hJ₀c, ⟨eL⟩⟩ := hall _ (Subgroup.map_subtype_le _) hL2'
  obtain ⟨J', hJ', hq⟩ := ExcSelector.exists_eq_orbitGroupC_of_isPComponent' Dd hXfin hJ₀X hJ₀c
  have hθ : ThetaProperties ρ r₀ Dd.χ (ToralSign.wordElt τ l) := by
    rw [hDχ]
    exact htheta m hm l hl
  obtain ⟨H, ⟨eH⟩⟩ := exists_quaternion_orbitGroup Dd hr₀ hθ hDθ J' hq
  let eLO : L ≃* (Dd.withOrbit J').orbitGroup :=
    ((L.equivMapOfInjective _ N.subtype_injective).trans
      (eL.trans (MulEquiv.subgroupCongr hJ'))).trans
        (Subgroup.subgroupOfEquivOfLe (Dd.withOrbit J').orbitGroup_le_adjointGroup)
  exact ⟨H.map eLO.symm.toMonoidHom,
    ⟨(H.equivMapOfInjective _ eLO.symm.injective).symm.trans eH⟩⟩

@[expose] def OddExcInnerDiagQuatForm (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → orderOf α = 2 →
      QuatComponentForm (fixedSubgroup α)

theorem oddExcInnerDiagQuatForm_E7
    : OddExcInnerDiagQuatForm .E7 := by
  intro K _ _ p f hp hp2 hK α g a hαg hαo
  have hα2 : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hK).1
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K (AlgebraicClosure K)
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergBM.exists_mulEquiv_E7_inner_diagonal_fixed hp2 hf hK hαg hα2
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨n7, -, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure K) p hp2 f hf
  obtain ⟨r7, -, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure K) hp2 f hf
  set R := fixedPointsIn (adjointGroup .E7 (AlgebraicClosure K))
    (frobTwistGL .E7 (AlgebraicClosure K) p f 1) with hR
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p hf le_rfl (map_one _) (one_pow 1)
  have hNR : ⁅R, R⁆ ⊓ Subgroup.centralizer {x} ≤ R :=
    fun y hy => Subgroup.commutator_le_self _ hy.1
  have : Finite ↥(⁅R, R⁆ ⊓ Subgroup.centralizer {x}) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  exact quatComponentForm_of_mulEquiv eA
    (quatComponentForm_of_twistReduction p hp2 hk hf (Or.inr (Or.inr rfl)) (ρ := 1)
      (fun _ _ => rfl) (fun _ _ => rfl) (Or.inl ⟨Or.inr rfl, rfl⟩) h7.theta
      (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
      (map_conj_one_adjointGroup _ _) n7 (r7 x hxR hx2))

end CFSG.ComponentClassification.CatLeafProof
