module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcDatum
import CFSG.LocalAnalysis.SteinbergBMOddResidualE7Lift
import CFSG.LocalAnalysis.SteinbergCEOddResidualTwistedE6Inner
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.SteinbergCA
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.LieType.Chevalley.ToralSign

section Reduction

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem gomi_false_of_mulEquiv_inner_centralizer
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j)
    {reps : List (SignRep τ)}
    (hreps : ∀ m ∈ reps, gomiNeighOK τ (natBits m.mask) = true)
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ 2 (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    (hRfin : Finite (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))
    {x : ModGL τ k} (hred : IsFiniteToralTwistReduction τ k p e D reps x)
    {A : Type*} [Group A] (eA : A ≃* ↥(⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}))
    (L : Subgroup A) (hL : CFSG.IsComponent L) (hLs : IsSimpleGroup L)
    (hLnab : ∃ a b : L, a * b ≠ b * a) (hLcard : Nat.card L = 25920) : False := by
  classical
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 := Or.inr hτ
  let N : Subgroup (ModGL τ k) :=
    ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}
  have hNfin : Finite N := by
    have hNR : N ≤ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) :=
      inf_le_left.trans (Subgroup.commutator_le.2 fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))
    exact Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  let S' : Subgroup N := L.map eA.toMonoidHom
  let e' : L ≃* S' := L.equivMapOfInjective _ eA.injective
  have hS'comp : CFSG.IsComponent S' := CFSG.LocalCores.isComponent_map_mulEquiv eA hL
  have hLX : S'.map N.subtype ≤ N := Subgroup.map_subtype_le S'
  have hLsub : (S'.map N.subtype).subgroupOf N = S' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective S'
  have hL₂c : CFSG.Assembly.IsComponentOf (S'.map N.subtype) N :=
    (isComponentOf_iff_isComponent_subgroupOf hLX).2 (by rw [hLsub]; exact hS'comp)
  have hS'c : CFSG.IsPComponent 2 S' := by
    have := CFSG.ComponentClassification.ExcSelector.isPComponent_two_subgroupOf hL₂c
    rwa [hLsub] at this
  obtain ⟨Dd, J₀, ⟨m, hm, l, hl, hDχ, hDθ⟩, hXfin, hJ₀X, hJ₀c, ⟨eL⟩⟩ :=
    exists_datum_isPComponent_of_twistReduction p hp hk he hτ' hA hB htheta hDX hDT hDG hpin
      hred (S'.map N.subtype) hLX (by rw [hLsub]; exact hS'c)
  have hθ : ThetaProperties ρ 2 Dd.χ (ToralSign.wordElt τ l) := by
    rw [hDχ]
    exact htheta m hm l hl
  have horb : ∀ (J' : Set.range Dd.classOrbit) (O : Set (Fin τ.rank → ℤ)),
      O ∈ (Dd.withOrbit J').orbits → orbitCard O ≤ 2 := by
    intro J' O hO
    rcases CFSG.ClassicalInvolution.ModelFacts.orbitCard_eq_of_thetaProperties
      (Dd.withOrbit J') hθ hDθ hO with h | h <;> omega
  let eJ : J₀ ≃* L := (eL.symm.trans (S'.equivMapOfInjective _ N.subtype_injective).symm).trans
    e'.symm
  have hJ₀s : IsSimpleGroup J₀ := eJ.isSimpleGroup
  have hJ₀nab : ∃ a b : J₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLnab
    exact ⟨eJ.symm a, eJ.symm b, fun h' => hab (eJ.symm.injective
      ((MulEquiv.map_mul eJ.symm a b).trans (h'.trans (MulEquiv.map_mul eJ.symm b a).symm)))⟩
  have hJ₀card : Nat.card J₀ = 25920 := by
    rw [Nat.card_congr eJ.toEquiv]
    exact hLcard
  exact gomi_false_of_isPComponent_totalFixedGroup Dd hτ hDχ (hreps m hm) horb hXfin hJ₀X hJ₀c
    hJ₀s hJ₀nab hJ₀card

end Reduction

section Main

theorem gomi_E7_inner_false
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ n) {α : MulAut (adjointGroup .E7 F)}
    {g : adjointGroup .E7 F} {a : Fin Tag.E7.rank → Fˣ}
    (hαg : ∀ h : adjointGroup .E7 F, (α h : ModGL .E7 F) =
      (g : ModGL .E7 F) * rootDiagUnit .E7 a * h * (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 F)⁻¹)
    (hα : α ^ 2 = 1) (L : Subgroup ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 F))))
    (hL : CFSG.IsComponent L) (hLs : IsSimpleGroup L) (hLnab : ∃ x y : L, x * y ≠ y * x)
    (hLcard : Nat.card L = 25920) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := finite_field_prime_power_characteristic hp hn hF
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_mulEquiv_E7_inner_diagonal_fixed hp2 hn hF hαg hα
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨n7, -, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure F) p hp2 n hn
  obtain ⟨r7, -, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure F) hp2 n hn
  have hreps : ∀ m ∈ e7SignDiagramReps, gomiNeighOK Tag.E7 (natBits m.mask) = true := by
    intro m hm
    simp only [e7SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> exact gomi_neighOK_E7 _ (by simp)
  exact gomi_false_of_mulEquiv_inner_centralizer p hp2 hk hn (Or.inr rfl) (ρ := 1)
    (fun _ _ => rfl) (fun _ _ => rfl) hreps h7.theta
    (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
    (map_conj_one_adjointGroup _ _) n7
    (finite_fixedPointsIn_frobTwistGL p hn le_rfl (map_one _) (one_pow 1)) (r7 x hxR hx2) eA L hL
    hLs hLnab hLcard

theorem gomi_twistedE6_inner_false
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (F : Type) [Field F]
    [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.E6 F σ.toRingHom)) (hα : α ^ 2 = 1)
    (hαi : α ∈ twistedE6Inn F σ)
    (L : Subgroup ↥(α.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))))
    (hL : CFSG.IsComponent L) (hLs : IsSimpleGroup L) (hLnab : ∃ x y : L, x * y ≠ y * x)
    (hLcard : Nat.card L = 25920) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := finite_field_prime_power_characteristic hp (by omega : 1 ≤ 2 * f)
    (by rw [hF, ← pow_mul, mul_comm])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergCE.exists_mulEquiv_twisted_E6_inner_fixed hp2 hf hF σ hσ hα hαi
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure F) p hp2 f hf
  obtain ⟨-, r6, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure F) hp2 f hf
  have hreps : ∀ m ∈ e6SignDiagramReps, gomiNeighOK Tag.E6 (natBits m.mask) = true := by
    intro m hm
    simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact gomi_neighOK_E6 _ (by simp)
  exact gomi_false_of_mulEquiv_inner_centralizer p hp2 hk hf (Or.inl rfl)
    TwistTag.E6.cartan_perm symmetrizedCartan_perm_E6 hreps h6.theta
    (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
    (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 _ (Or.inl rfl)) n6
    (finite_fixedPointsIn_frobTwistGL p hf (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.E6)
        (iterateFrobenius (AlgebraicClosure F) p f))
      (diagramMap_pow_order TwistTag.E6 (AlgebraicClosure F)))
    (r6 x hxR hx2) eA L hL hLs hLnab hLcard

end Main

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
