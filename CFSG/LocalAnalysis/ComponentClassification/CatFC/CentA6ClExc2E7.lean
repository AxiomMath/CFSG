module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc2Classes
public import CFSG.LocalAnalysis.SteinbergCAOddResidualInner
public import CFSG.LocalAnalysis.SteinbergBMOddResidualE7Lift
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedComponentPrimes

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.LocalAnalysis.SteinbergCA
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

set_option linter.unusedSectionVars false


section Obstruction

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem a6_false_of_isPComponent_totalFixedGroup {τ : Tag}
    (D : OrthogonalSemilinearFixedRootDatum τ p k) (hτ : τ = .E6 ∨ τ = .E7)
    (horb : ∀ (J' : Set.range D.classOrbit) (O : Set (Fin τ.rank → ℤ)),
      O ∈ (D.withOrbit J').orbits → orbitCard O ≤ 2)
    (hX : Finite D.totalFixedGroup) {J₀ : Subgroup (adjointGroup τ k)}
    (hJ₀X : J₀ ≤ D.totalFixedGroup) (hJ₀c : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup))
    (hJ₀s : IsSimpleGroup J₀) (hJ₀nab : ∃ a b : J₀, a * b ≠ b * a)
    (eJ : J₀ ≃* alternatingGroup (Fin 6)) : False := by
  have hcomp : CFSG.IsComponent (J₀.subgroupOf D.totalFixedGroup) := by
    obtain ⟨-, -, hsub, -, -⟩ := hJ₀c
    refine ⟨?_, hsub⟩
    have : IsSimpleGroup (J₀.subgroupOf D.totalFixedGroup) :=
      (Subgroup.subgroupOfEquivOfLe hJ₀X).isSimpleGroup
    exact isQuasisimple_of_isSimpleGroup (by
      obtain ⟨a, b, hab⟩ := hJ₀nab
      refine ⟨(Subgroup.subgroupOfEquivOfLe hJ₀X).symm a,
        (Subgroup.subgroupOfEquivOfLe hJ₀X).symm b, fun h' => hab ?_⟩
      apply (Subgroup.subgroupOfEquivOfLe hJ₀X).symm.injective
      exact (MulEquiv.map_mul _ a b).trans (h'.trans (MulEquiv.map_mul _ b a).symm))
  obtain ⟨J', ⟨O, hO⟩, hJ₀eq⟩ := D.exists_eq_orbitGroupC_of_isComponent hX hJ₀X hcomp
  have : CharP ((D.withOrbit J').orbitField O) p :=
    CharP.subring k p ((D.withOrbit J').orbitField O).toSubring
  let φ : Matrix.SpecialLinearGroup (Fin 2) ((D.withOrbit J').orbitField O) →*
      adjointGroup τ k :=
    ((D.withOrbit J').orbitMapHom hO).codRestrict _
      (fun A => (D.withOrbit J').orbitMap_mem_adjointGroup O A)
  have hφ : ∀ A, ((φ A : adjointGroup τ k) : ModGL τ k) = (D.withOrbit J').orbitMap O A :=
    fun A => rfl
  have hφJ : ∀ A, φ A ∈ J₀ := fun A => by
    rw [hJ₀eq]
    exact (D.withOrbit J').mk_mem_orbitGroupC ((D.withOrbit J').orbitMap_mem_orbitGroup hO A)
  have hneg : φ (-1) ≠ 1 := fun h => by
    apply orbitMap_neg_one_ne_one (D.withOrbit J') hτ hO (horb J' O hO)
    rw [← hφ, h]
    rfl
  have hu : φ (uSL 1) ≠ 1 := fun h => by
    have h1 : (D.withOrbit J').orbitX O 1 = 1 := by
      change (D.withOrbit J').orbitMap O (uSL 1) = 1
      rw [← hφ, h]
      rfl
    have h2 := (D.withOrbit J').orderOf_orbitX_one hO
    rw [h1, orderOf_one] at h2
    exact (Fact.out : p.Prime).one_lt.ne h2
  exact false_of_hom_A6 eJ D.odd φ hφJ hneg hu


end Obstruction

section Inner

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem a6_false_of_mulEquiv_inner_centralizer
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j)
    {reps : List (SignRep τ)}
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
    (S : Subgroup A) (hSn : S.Normal) (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) (eS : S ≃* alternatingGroup (Fin 6)) : False := by
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
  let S' : Subgroup N := S.map eA.toMonoidHom
  let e' : S ≃* S' := S.equivMapOfInjective _ eA.injective
  have := hSs
  have hS'n : S'.Normal := hSn.map _ eA.surjective
  have hS's : IsSimpleGroup S' := e'.symm.isSimpleGroup
  have hS'nab : ∃ a b : S', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨e' a, e' b, fun h' => hab (e'.injective
      ((MulEquiv.map_mul e' a b).trans (h'.trans (MulEquiv.map_mul e' b a).symm)))⟩
  have hS'c : CFSG.IsPComponent 2 S' :=
    isPComponent_two_of_normal_simple S' hS'n hS's hS'nab (two_dvd_card_of_A6 (e'.symm.trans eS))
  have hLsub : (S'.map N.subtype).subgroupOf N = S' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective S'
  obtain ⟨Dd, J₀, ⟨m, hm, l, hl, hDχ, hDθ⟩, hXfin, hJ₀X, hJ₀c, ⟨eL⟩⟩ :=
    exists_datum_isPComponent_of_twistReduction p hp hk he hτ' hA hB htheta hDX hDT hDG hpin
      hred (S'.map N.subtype) (Subgroup.map_subtype_le S') (by rw [hLsub]; exact hS'c)
  have hθ : ThetaProperties ρ 2 Dd.χ (ToralSign.wordElt τ l) := by
    rw [hDχ]
    exact htheta m hm l hl
  have horb : ∀ (J' : Set.range Dd.classOrbit) (O : Set (Fin τ.rank → ℤ)),
      O ∈ (Dd.withOrbit J').orbits → orbitCard O ≤ 2 := by
    intro J' O hO
    rcases orbitCard_eq_of_thetaProperties (Dd.withOrbit J') hθ hDθ hO with h | h <;> omega
  let eJ : J₀ ≃* S := (eL.symm.trans (S'.equivMapOfInjective _ N.subtype_injective).symm).trans
    e'.symm
  have hJ₀s : IsSimpleGroup J₀ := eJ.isSimpleGroup
  have hJ₀nab : ∃ a b : J₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨eJ.symm a, eJ.symm b, fun h' => hab (eJ.symm.injective
      ((MulEquiv.map_mul eJ.symm a b).trans (h'.trans (MulEquiv.map_mul eJ.symm b a).symm)))⟩
  exact a6_false_of_isPComponent_totalFixedGroup Dd hτ horb hXfin hJ₀X hJ₀c hJ₀s hJ₀nab
    (eJ.trans eS)


end Inner

section Main

theorem a6_E7_inner_diagonal_false
    {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {α : MulAut (adjointGroup .E7 F)} {g : adjointGroup .E7 F}
    {a : Fin Tag.E7.rank → Fˣ}
    (hαg : ∀ h : adjointGroup .E7 F, (α h : ModGL .E7 F) =
      (g : ModGL .E7 F) * rootDiagUnit .E7 a * h * (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 F)⁻¹)
    (hα : α ^ 2 = 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 F)))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (eS : S ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨p, n, hp, hp2, hn, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hF
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := hchar ▸ ringChar.charP F
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_mulEquiv_E7_inner_diagonal_fixed hp2 hn hcard hαg hα
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨n7, -, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure F) p hp2 n hn
  obtain ⟨r7, -, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure F) hp2 n hn
  exact a6_false_of_mulEquiv_inner_centralizer p hp2 hk hn (Or.inr rfl) (ρ := 1) (fun _ _ => rfl)
    (fun _ _ => rfl) h7.theta (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ)
    (one_mem _) (map_conj_one_adjointGroup _ _) n7
    (finite_fixedPointsIn_frobTwistGL p hn le_rfl (map_one _) (one_pow 1)) (r7 x hxR hx2) eA S
    hSn hSs hSnab eS

theorem a6_E7_false {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (β : MulAut (adjointGroup .E7 F)) (hβ2 : β ^ 2 = 1)
    (S : Subgroup (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 F))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (eS : S ≃* alternatingGroup (Fin 6)) : False := by
  classical
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  rcases odd_E7_involution_inner_or_quadratic hodd hβ2 with ⟨g, a, hβg⟩ |
    ⟨q, e, hq, he, hFe, δ, hδ, g, a, hβg⟩
  · exact a6_E7_inner_diagonal_false hodd hβg hβ2 S hSn hSs hSnab eS
  · have hq2 : q ≠ 2 := fun h => by
      rw [h, ← pow_mul] at hFe
      rw [hFe] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
    exact a6_quadratic_field_coset_false hq hq2 he hFe δ hδ hβg hβ2 S hSn hSs hSnab eS

end Main

end CFSG.ComponentClassification.CatFC
