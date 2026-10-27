module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Quat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Toral
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameC3
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

section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]

theorem orbitGroup_isEmpty_a6_of_odd
    (D : OrthogonalSemilinearFixedRootDatum τ p₀ k) {O P : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) (hP : P ∈ D.orbits)
    (hodd : Odd (ExcSelector.orbitPairing' D O (D.orbitVec P 0))) :
    IsEmpty (D.orbitGroup ⧸ Subgroup.center D.orbitGroup ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun eA => ?_⟩
  have : Finite (D.orbitField O) := ExcSelector.finite_orbitField' D hO
  have hF : ringChar (D.orbitField O) ≠ 2 :=
    ExcSelector.ringChar_subfield_ne_two D.ringChar_ne_two _
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero D.ringChar_ne_two
  have hconj := ExcSelector.orbitMap_neg_one_conj_orbitX D hO hP hodd 1
  refine false_of_sl2_hom_noncentral eA hF (D.orbitGroupHom hO) fun hz => ?_
  have hX : D.orbitX P 1 ∈ D.orbitGroup := D.orbitMap_mem_orbitGroup hP _
  have hc := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨_, hX⟩)
  change D.orbitX P 1 * D.orbitMap O (-1) = D.orbitMap O (-1) * D.orbitX P 1 at hc
  rw [← hc, mul_inv_cancel_right] at hconj
  have h1 := D.orbitX_injective hP hconj
  have h1' := congrArg (fun c : D.orbitField P => (c : k)) h1
  simp only [OneMemClass.coe_one, NegMemClass.coe_neg] at h1'
  exact h2 (by linear_combination h1')

theorem orbitGroup_a6_of_single
    (D : OrthogonalSemilinearFixedRootDatum τ p₀ k) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) (hA : D.orbits = {O}) (hne : D.orbitMap O (-1) ≠ 1) :
    IsPGroup 2 (Subgroup.center D.orbitGroup) := by
  have : Finite (D.orbitField O) := ExcSelector.finite_orbitField' D hO
  have hinj : Function.Injective (D.orbitGroupHom hO) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA'
    have h1 : D.orbitMap O A = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hA')
    rcases D.eq_one_or_neg_one_of_orbitMap_eq_one hO h1 with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · exact absurd (h ▸ h1) hne
  let e : SL2 (D.orbitField O) ≃* D.orbitGroup :=
    MulEquiv.ofBijective _ ⟨hinj, D.orbitGroupHom_surjective hO hA⟩
  exact isPGroup_center_of_mulEquiv_SL e.symm

theorem orbitGroup_a6
    (D : OrthogonalSemilinearFixedRootDatum τ p₀ k) [Nontrivial D.orbitGroup]
    (hsingle : ∀ O ∈ D.orbits, D.orbits = {O} → D.orbitMap O (-1) ≠ 1)
    (hA6 : Nonempty (D.orbitGroup ⧸ Subgroup.center D.orbitGroup ≃* alternatingGroup (Fin 6))) :
    IsPGroup 2 (Subgroup.center D.orbitGroup) := by
  by_cases h2 : 2 ≤ D.orbits.ncard
  · exfalso
    obtain ⟨eA⟩ := hA6
    obtain ⟨O₁, hO₁⟩ := Set.nonempty_of_ncard_ne_zero (s := D.orbits) (by omega)
    obtain ⟨P, hP, hne, hadj⟩ := D.exists_adjacent_orbit h2 hO₁
    rcases ExcSelector.exists_odd_orbitPairing' D hO₁ hP hne hadj with
      ⟨γ, hγ, hodd⟩ | ⟨β, hβ, hodd⟩
    · obtain ⟨i, -, rfl⟩ := D.exists_orbitVec_eq hP hγ
      rw [ExcSelector.orbitPairing_orbitVec D hO₁ hP] at hodd
      exact (orbitGroup_isEmpty_a6_of_odd D hO₁ hP hodd).false eA
    · obtain ⟨i, -, rfl⟩ := D.exists_orbitVec_eq hO₁ hβ
      rw [ExcSelector.orbitPairing_orbitVec D hP hO₁] at hodd
      exact (orbitGroup_isEmpty_a6_of_odd D hP hO₁ hodd).false eA
  · have hfin := ExcSelector.finite_orbits' D
    rcases Nat.lt_or_ge D.orbits.ncard 1 with h0 | h1
    · exfalso
      have he : D.orbits = ∅ := by
        rw [← Set.ncard_eq_zero hfin]
        omega
      have hbot : D.orbitGroup = ⊥ := by
        rw [eq_bot_iff]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨O, hO, -⟩
        rw [he] at hO
        exact absurd hO (Set.notMem_empty O)
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := exists_pair_ne D.orbitGroup
      rw [hbot, Subgroup.mem_bot] at hx hy
      exact hxy (Subtype.ext (hx.trans hy.symm))
    · obtain ⟨O, hO⟩ := Set.ncard_eq_one.1 (by omega : D.orbits.ncard = 1)
      have hOm : O ∈ D.orbits := by
        rw [hO]
        exact Set.mem_singleton O
      exact orbitGroup_a6_of_single D hOm hO (hsingle O hOm hO)

end Datum

theorem a6CentreForm_of_twistReduction
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
    A6CentreForm ↥(⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}) := by
  set N := ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}
    with hN
  intro L hL hA6
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
  let eLO : L ≃* (Dd.withOrbit J').orbitGroup :=
    ((L.equivMapOfInjective _ N.subtype_injective).trans
      (eL.trans (MulEquiv.subgroupCongr hJ'))).trans
        (Subgroup.subgroupOfEquivOfLe (Dd.withOrbit J').orbitGroup_le_adjointGroup)
  have : Nontrivial (Dd.withOrbit J').orbitGroup := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hsingle : ∀ O ∈ (Dd.withOrbit J').orbits, (Dd.withOrbit J').orbits = {O} →
      (Dd.withOrbit J').orbitMap O (-1) ≠ 1 := fun O hO _ =>
    ExcSelector.orbitMap_neg_one_ne_one (Dd.withOrbit J') hr₀ hO
      (orbitCard_eq_of_thetaProperties (Dd.withOrbit J') hθ hDθ hO)
  obtain ⟨eA⟩ := hA6
  have hA' : Nonempty ((Dd.withOrbit J').orbitGroup ⧸
      Subgroup.center (Dd.withOrbit J').orbitGroup ≃* alternatingGroup (Fin 6)) :=
    ⟨(QuotientGroup.congr _ _ eLO.symm (Subgroup.map_center_eq eLO.symm)).trans eA⟩
  exact (orbitGroup_a6 (Dd.withOrbit J') hsingle hA').of_equiv (Subgroup.centerCongr eLO).symm

theorem oddExcInnerDiagA6Form_E7
    : OddExcInnerDiagA6Form .E7 := by
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
  exact a6CentreForm_of_mulEquiv eA
    (a6CentreForm_of_twistReduction p hp2 hk hf (Or.inr (Or.inr rfl)) (ρ := 1)
      (fun _ _ => rfl) (fun _ _ => rfl) (Or.inl ⟨Or.inr rfl, rfl⟩) h7.theta
      (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
      (map_conj_one_adjointGroup _ _) n7 (r7 x hxR hx2))

end CFSG.ComponentClassification.CatLeafProof
