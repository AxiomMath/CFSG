module

public import CFSG.Adapters.TauCetiExceptional.TwistedE6Carrier
public import CFSG.Adapters.TauCetiExceptional.TwistedIsogeny
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell

variable (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)

abbrev e6Index : TypeTwistedE6LieIndex := ⟨⟨_, hv⟩, by simp⟩

abbrev e6Closure : Type := ValidLieTypeIndex.Closure ⟨_, hv⟩

abbrev e6Char : ℕ := ValidLieTypeIndex.characteristic ⟨_, hv⟩

theorem e6Char_eq : e6Char q hv = q.p := LieTypeIndex.characteristic_twistedE6 q

abbrev e6Fr : e6Closure q hv →+* e6Closure q hv :=
  iterateFrobenius (e6Closure q hv) (e6Char q hv) (ValidLieTypeIndex.fieldExponent ⟨_, hv⟩)

theorem graphPermE6_eq (i : Fin 6) : graphPermE6 i = TwistTag.E6.perm i := by
  fin_cases i
  · rw [show ((fun i => i) ⟨0, by decide⟩ : Fin 6) = 0 from rfl, graphPermE6_apply_zero]; rfl
  · rw [show ((fun i => i) ⟨1, by decide⟩ : Fin 6) = 1 from rfl, graphPermE6_apply_one]; rfl
  · rw [show ((fun i => i) ⟨2, by decide⟩ : Fin 6) = 2 from rfl, graphPermE6_apply_two]; rfl
  · rw [show ((fun i => i) ⟨3, by decide⟩ : Fin 6) = 3 from rfl, graphPermE6_apply_three]; rfl
  · rw [show ((fun i => i) ⟨4, by decide⟩ : Fin 6) = 4 from rfl, graphPermE6_apply_four]; rfl
  · rw [show ((fun i => i) ⟨5, by decide⟩ : Fin 6) = 5 from rfl, graphPermE6_apply_five]; rfl

theorem e6_steinberg_rootSubgroupPoints (k : Fin 6 ⊕ Fin 6) (c : e6Closure q hv) :
    (e6Index q hv).steinberg (E6DoubledMinuscule.rootSubgroupPoints k (e6Closure q hv)
        (Multiplicative.ofAdd c)) =
      E6DoubledMinuscule.rootSubgroupPoints (E6DoubledMinuscule.graphRootPerm k) (e6Closure q hv)
        (Multiplicative.ofAdd (e6Fr q hv c)) := by
  rw [TypeTwistedE6LieIndex.steinberg_def, MonoidHom.comp_apply,
    TypeTwistedE6LieIndex.frobenius_def, E6DoubledMinuscule.frobenius_rootSubgroupPoints,
    MulEquiv.coe_toMonoidHom, TypeTwistedE6LieIndex.graphAut_def,
    E6DoubledMinuscule.graphAutomorphismPoints_rootSubgroupPoints, toAdd_ofAdd,
    iterateFrobenius_def]

variable {q hv}

theorem e6_steinberg_u (i : Fin 6) (c : e6Closure q hv) :
    (e6Index q hv).steinberg (E6PushDown.u i c) =
      E6PushDown.u (TwistTag.E6.perm i) (e6Fr q hv c) := by
  rw [E6PushDown.u, e6_steinberg_rootSubgroupPoints, E6DoubledMinuscule.graphRootPerm_inl,
    graphPermE6_eq]

theorem e6_steinberg_v (i : Fin 6) (c : e6Closure q hv) :
    (e6Index q hv).steinberg (E6PushDown.v i c) =
      E6PushDown.v (TwistTag.E6.perm i) (e6Fr q hv c) := by
  rw [E6PushDown.v, e6_steinberg_rootSubgroupPoints, E6DoubledMinuscule.graphRootPerm_inr,
    graphPermE6_eq]

theorem e6_steinberg_surjective : Function.Surjective (e6Index q hv).steinberg := by
  rw [TypeTwistedE6LieIndex.steinberg_def, MonoidHom.coe_comp]
  refine (e6Index q hv).graphAut.surjective.comp ?_
  rw [TypeTwistedE6LieIndex.frobenius_def, E6DoubledMinuscule.frobenius_eq_map]
  set e := RingEquiv.ofBijective _ (bijective_iterateFrobenius (e6Closure q hv) (e6Char q hv)
    (ValidLieTypeIndex.fieldExponent ⟨_, hv⟩))
  intro g
  refine ⟨(E6DoubledMinuscule.pointsPresentation _).map
    (E6DoubledMinuscule.pointsPresentation _) e.symm.toRingHom g, ?_⟩
  have h := congrArg (fun φ => φ g) (GeneralLinear.IntegralPointsPresentation.map_comp
    (E6DoubledMinuscule.pointsPresentation (e6Closure q hv))
    (E6DoubledMinuscule.pointsPresentation (e6Closure q hv))
    (E6DoubledMinuscule.pointsPresentation (e6Closure q hv)) e.symm.toRingHom e.toRingHom)
  simp only [MonoidHom.comp_apply] at h
  rw [show (iterateFrobenius (e6Closure q hv) (e6Char q hv)
      (ValidLieTypeIndex.fieldExponent ⟨_, hv⟩)) = e.toRingHom from rfl, ← h,
    RingEquiv.toRingHom_comp_symm_toRingHom, GeneralLinear.IntegralPointsPresentation.map_id,
    MonoidHom.id_apply]

theorem E6PushDown.isTwistedIsogeny_steinberg
    (P : E6PushDown (e6Closure q hv)) (hp2 : q.p ≠ 2) :
    IsTwistedIsogeny .E6 (e6Closure q hv) (e6Fr q hv) (e6Index q hv).steinberg P.π := by
  have hp2' : e6Char q hv ≠ 2 := by rw [e6Char_eq]; exact hp2
  have h2 : (2 : e6Closure q hv) ≠ 0 := two_ne_zero_of_charP hp2'
  refine (P.blockCarrier h2).isTwistedIsogeny (t := .E6) (p := e6Char q hv) (by decide) hp2'
    P.zeros (e6Index q hv).steinberg (e6Fr q hv) e6_steinberg_u e6_steinberg_v fun k hk => ?_
  apply P.π_eq_one_of_mem_center
  have hc := Subgroup.mem_center_iff.1 ((P.blockCarrier h2).ker_center k hk)
  refine Subgroup.mem_center_iff.2 fun w => ?_
  obtain ⟨w', rfl⟩ := e6_steinberg_surjective w
  exact ((map_mul _ w' k).symm.trans (congrArg (e6Index q hv).steinberg (hc w'))).trans
    (map_mul _ k w')

theorem nonempty_mulEquiv_group_twistedE6
    (P : E6PushDown (e6Closure q hv)) (hp2 : q.p ≠ 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q.card ^ TwistTag.E6.order)
    (σ : K →+* K) (hσ : ∀ x, σ x = x ^ q.card) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .E6 K σ) ≃*
      ValidLieTypeIndex.Group ⟨LieTypeIndex.twistedE6 q, hv⟩) := by
  set p := e6Char q hv with hpdef
  set f := ValidLieTypeIndex.fieldExponent ⟨_, hv⟩ with hfdef
  have hq : q.card = p ^ f := by
    rw [← LieTypeIndex.fieldOrder_twistedE6 q]
    exact ValidLieTypeIndex.fieldOrder_eq_characteristic_pow ⟨_, hv⟩
  have hp : p.Prime := Fact.out
  have hf : 1 ≤ f := ValidLieTypeIndex.fieldExponent_pos ⟨_, hv⟩
  have hK' : Nat.card K = (p ^ f) ^ TwistTag.E6.order := by rw [hK, hq]
  have hσ' : ∀ c, σ c = c ^ (p ^ f) := fun c => by rw [hσ, hq]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := f * 2) (by omega) (by rw [hK', pow_mul]; rfl)
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have : Algebra.IsAlgebraic (ZMod p) K := Algebra.IsAlgebraic.of_finite (ZMod p) K
  let ι : K →ₐ[ZMod p] e6Closure q hv := IsAlgClosed.lift
  let : Algebra K (e6Closure q hv) := ι.toRingHom.toAlgebra
  have : IsScalarTower (ZMod p) K (e6Closure q hv) :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have : Algebra.IsAlgebraic K (e6Closure q hv) :=
    Algebra.IsAlgebraic.tower_top (K := ZMod p) K
  have : IsAlgClosure K (e6Closure q hv) := ⟨inferInstance, inferInstance⟩
  have hFr : ∀ c, e6Fr q hv c = c ^ (p ^ f) := fun c => by rw [iterateFrobenius_def]
  obtain ⟨e⟩ := nonempty_derivedCentralQuotient_equiv (t := .E6) (e6Closure q hv) (e6Fr q hv) hp
    hf hK' hσ' hFr (P.isTwistedIsogeny_steinberg hp2)
  exact ⟨e.symm⟩

theorem twistedBridge_twistedE6_of
    (hP : ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid), q.p ≠ 2 →
      E6PushDown (e6Closure q hv)) :
    TwistedBridge .E6 LieTypeIndex.twistedE6 := fun q hv hp2 K _ _ hK σ hσ =>
  nonempty_mulEquiv_group_twistedE6 (hP q hv hp2) hp2 K hK σ hσ

end CFSG.TauCetiBridge.Twisted
