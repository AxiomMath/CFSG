module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormUniform
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Descent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6TwistedOuter
public import CFSG.LocalAnalysis.SteinbergCEOddResidualTwistedE6Inner
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddDatum

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem thetaMap_e6_alpha4 :
    thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm (Pi.single (e6Node 3) 1) =
      Pi.single (e6Node 3) 1 := by
  rw [thetaMap_e6_nil_apply]
  funext j
  change (Pi.single (e6Node 3) 1 : Fin (Tag.rank .E6) → ℤ) (TwistTag.E6.perm.symm j) =
    (Pi.single (e6Node 3) 1 : Fin (Tag.rank .E6) → ℤ) j
  have h : ∀ i : Fin 6, (Pi.single 3 1 : Fin 6 → ℤ)
      ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm i) = (Pi.single 3 1 : Fin 6 → ℤ) i := by
    decide
  exact h j

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem e6_twisted_datum_classes
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) {m : ℕ} (hm : m = 0 ∨ m = 20 ∨ m = 2)
    (hχ : D.χ = signMaskChar .E6 m)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ)) :
    D.θ (toReal (Pi.single (e6Node 3) 1)) = toReal (Pi.single (e6Node 3) 1) ∧
      ∃ S : Set (Fin (Tag.rank .E6) → ℤ), Pi.single (e6Node 3) 1 ∈ S ∧
        ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
          (D.withOrbit J').simpleRootsJ = S ∨
            ∃ β₀, (D.withOrbit J').simpleRootsJ = {β₀} ∧ D.θ (toReal β₀) = toReal β₀ := by
  have hne : ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
      (D.withOrbit J').simpleRootsJ ≠ ∅ := fun J' hq h0 =>
    (Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq)
      (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
  have hone : ∀ {S : Set (Fin (Tag.rank .E6) → ℤ)}, simpleUnion D.χ = S →
      (∀ i : KernelComponent D.χ, simpleUnion D.χ ∩ componentRoots D.χ i = ∅ ∨
        simpleUnion D.χ ∩ componentRoots D.χ i = S) →
      ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
        (D.withOrbit J').simpleRootsJ = S ∨
          ∃ β₀, (D.withOrbit J').simpleRootsJ = {β₀} ∧ D.θ (toReal β₀) = toReal β₀ := by
    intro S hS hcls J' hq
    rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hS hcls with h0 | h
    · exact absurd h0 (hne J' hq)
    · exact Or.inl h
  refine ⟨by rw [hθ, thetaMap_e6_alpha4], ?_⟩
  rcases hm with rfl | rfl | rfl
  · exact ⟨Set.range e6SimpleRoot, ⟨3, rfl⟩,
      hone (by rw [hχ]; exact simpleUnion_e6_zero) (e6_simple_inter_zero hχ)⟩
  · exact ⟨Set.range e6D5TwRoot, ⟨0, rfl⟩,
      hone (by rw [hχ]; exact simpleUnion_e6_twenty) (e6_simple_inter_twenty hχ)⟩
  · refine ⟨Set.range e6A5Root, ⟨2, rfl⟩, fun J' hq => ?_⟩
    rcases e6_two_simpleRootsJ D hχ hθ J' with h | h | h
    · exact absurd h (hne J' hq)
    · exact Or.inl h
    · exact Or.inr ⟨hiE6, h, by rw [hθ, thetaMap_e6_hiE6]⟩

theorem oddTwistedE6InnerSLForm_holds
    :
    ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .twistedE6 0 p f →
      Blueprint.LieModel J .twistedE6 0 p f → ∀ α : MulAut J, orderOf α = 2 →
        α ∈ (MulAut.conj : J →* MulAut J).range →
        (∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L) ∧
          ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
            SLComponentForm K (fixedSubgroup α) := by
  intro J _ p f hp hp2 hadm hm α hα hαi
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
  have : CharP F p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (show 1 ≤ f * 2 by omega) (by rw [hF2, ← pow_mul])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  have hα' : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hα'2 : MulAut.congr e α ^ 2 = 1 := by
    rw [← hα']
    exact pow_orderOf_eq_one _
  have hα'i : MulAut.congr e α ∈ twistedE6Inn F σ := by
    obtain ⟨g, hg⟩ := hαi
    exact ⟨e g, by rw [← hg, mulAut_congr_conj_twistedE6]⟩
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergCE.exists_mulEquiv_twisted_E6_inner_fixed hp2 hf hF2 σ hσ hα'2 hα'i
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure F) p hp2 f hf
  obtain ⟨-, r6, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure F) hp2 f hf
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure F))
    (frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
      (diagramMap TwistTag.E6 (AlgebraicClosure F))) with hR
  set N := ⁅R, R⁆ ⊓ Subgroup.centralizer {x} with hN
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p hf (by decide)
    (units_map_entrywiseHom_diagramMap (t := TwistTag.E6)
      (iterateFrobenius (AlgebraicClosure F) p f))
    (diagramMap_pow_order TwistTag.E6 (AlgebraicClosure F))
  have hNR : N ≤ R := fun y hy => Subgroup.commutator_le_self _ hy.1
  have hNfin : Finite N := Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  let Ψ : fixedSubgroup α ≃* N := (fixedSubgroupCongrEquiv e α).trans eA
  have h2 : ∀ L₀ : Subgroup N, IsPComponent 2 L₀ → L₀.map N.subtype ≤ N ∧
      IsPComponent 2 ((L₀.map N.subtype).subgroupOf N) := fun L₀ hL₀ => by
    have hsub : (L₀.map N.subtype).subgroupOf N = L₀ :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective L₀
    exact ⟨Subgroup.map_subtype_le _, by rw [hsub]; exact hL₀⟩
  have key : ∀ L₀ : Subgroup N, IsPComponent 2 L₀ →
      ∃ Dd : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p (AlgebraicClosure F),
        (∃ m ∈ e6SignDiagramReps, ∃ l ∈ m.omegaWords, Dd.χ = signMaskChar TwistTag.E6.tag m.mask ∧
          ∀ γ, Dd.θ (toReal γ) =
            toReal (thetaMap (ToralSign.wordElt TwistTag.E6.tag l) TwistTag.E6.perm γ)) ∧
        Dd.e = f ∧ ∀ L : Subgroup N, IsPComponent 2 L → ∃ J' : Set.range Dd.classOrbit,
          IsQuasisimple (Dd.withOrbit J').orbitGroup ∧
            Nonempty (L ≃* (Dd.withOrbit J').orbitGroup) := by
    intro L₀ hL₀
    obtain ⟨Dd, hml, hDe, hXfin, hall⟩ := exists_datum_uniform_of_twistReduction p hp2 hk hf
      (τ := TwistTag.E6.tag) (Or.inr (Or.inl rfl)) TwistTag.E6.cartan_perm
      symmetrizedCartan_perm_E6 h6.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
      (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 _ (Or.inl rfl))
      n6 (r6 x hxR hx2) _ (h2 L₀ hL₀).1 (h2 L₀ hL₀).2
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
  intro K _ _ hKq
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
  have hKe : Nat.card K = p ^ Dd.e := by
    rw [hDe]
    exact hKq
  have hml : (mr.mask = 0 ∨ mr.mask = 20 ∨ mr.mask = 2) ∧ l = [] := by
    simp only [e6SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hmr
    rcases hmr with rfl | rfl | rfl
    · simp only [e6OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact ⟨Or.inl rfl, hl⟩
    · simp only [e6OmegaWords20, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact ⟨Or.inr (Or.inl rfl), hl⟩
    · simp only [e6OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact ⟨Or.inr (Or.inr rfl), hl⟩
  obtain ⟨hmask, rfl⟩ := hml
  obtain ⟨hfix, S, hS, hΔ⟩ := e6_twisted_datum_classes Dd hmask hDχ hDθ
  exact slComponentForm_of_datum_classes Dd hKe hJ hS hfix hΔ

end CFSG.ComponentClassification.CatLeafProof
