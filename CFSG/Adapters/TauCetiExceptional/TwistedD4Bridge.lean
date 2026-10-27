module

public import CFSG.Adapters.TauCetiExceptional.TwistedD4Carrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import CFSG.Adapters.TauCetiExceptional.TwistedIsogeny

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell

variable (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)

abbrev d4Index : TypeTrialityD4LieIndex := ⟨⟨_, hv⟩, by simp⟩

abbrev d4Closure : Type := ValidLieTypeIndex.Closure ⟨_, hv⟩

abbrev d4Char : ℕ := ValidLieTypeIndex.characteristic ⟨_, hv⟩

theorem d4Char_eq : d4Char q hv = q.p := LieTypeIndex.characteristic_trialityD4 q

abbrev d4Fr : d4Closure q hv →+* d4Closure q hv :=
  iterateFrobenius (d4Closure q hv) (d4Char q hv) (ValidLieTypeIndex.fieldExponent ⟨_, hv⟩)

theorem d4Fr_apply (c : d4Closure q hv) : d4Fr q hv c = c ^ q.card := by
  rw [iterateFrobenius_def, ← LieTypeIndex.fieldOrder_trialityD4 q]
  exact congrArg (c ^ ·) (ValidLieTypeIndex.fieldOrder_eq_characteristic_pow ⟨_, hv⟩).symm

theorem trialityPermD4_d4Node_symm (i : Fin (Tag.rank .D4)) :
    trialityPermD4 (d4Node.symm i) = d4Node.symm (TwistTag.D4.perm i) := by
  have h := d4Node_trialityPermD4 (d4Node.symm i)
  simp only [Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply]

theorem d4_steinberg_rootSubgroupPoints (k : Fin 4 ⊕ Fin 4) (c : d4Closure q hv) :
    (d4Index q hv).steinberg (D4Tripled.rootSubgroupPoints k (d4Closure q hv)
        (Multiplicative.ofAdd c)) =
      D4Tripled.rootSubgroupPoints (D4Tripled.trialitySymmetry.rootPerm k) (d4Closure q hv)
        (Multiplicative.ofAdd (d4Fr q hv c)) := by
  rw [TypeTrialityD4LieIndex.steinberg_def, MonoidHom.comp_apply,
    TypeTrialityD4LieIndex.frobenius_def, D4Tripled.frobenius_rootSubgroupPoints,
    MulEquiv.coe_toMonoidHom, TypeTrialityD4LieIndex.graphAut_def,
    D4Tripled.trialityPoints_rootSubgroupPoints, toAdd_ofAdd, iterateFrobenius_def]

variable {q hv}

theorem d4_steinberg_u (i : Fin (Tag.rank .D4)) (c : d4Closure q hv) :
    (d4Index q hv).steinberg (D4PushDown.u i c) =
      D4PushDown.u (TwistTag.D4.perm i) (d4Fr q hv c) := by
  rw [D4PushDown.u, d4_steinberg_rootSubgroupPoints, MinusculeWeightTable.Symmetry.rootPerm_inl,
    D4Tripled.trialitySymmetry_nodePerm, trialityPermD4_d4Node_symm]

theorem d4_steinberg_v (i : Fin (Tag.rank .D4)) (c : d4Closure q hv) :
    (d4Index q hv).steinberg (D4PushDown.v i c) =
      D4PushDown.v (TwistTag.D4.perm i) (d4Fr q hv c) := by
  rw [D4PushDown.v, d4_steinberg_rootSubgroupPoints, MinusculeWeightTable.Symmetry.rootPerm_inr,
    D4Tripled.trialitySymmetry_nodePerm, trialityPermD4_d4Node_symm]

theorem d4_steinberg_surjective : Function.Surjective (d4Index q hv).steinberg := by
  rw [TypeTrialityD4LieIndex.steinberg_def, MonoidHom.coe_comp]
  refine (d4Index q hv).graphAut.surjective.comp ?_
  rw [TypeTrialityD4LieIndex.frobenius_def, D4Tripled.frobenius_eq_pointsMap]
  set e := RingEquiv.ofBijective _ (bijective_iterateFrobenius (d4Closure q hv) (d4Char q hv)
    (ValidLieTypeIndex.fieldExponent ⟨_, hv⟩))
  intro g
  refine ⟨D4Tripled.pointsMap e.symm.toRingHom g, ?_⟩
  have h := congrArg (fun φ => φ g) (D4Tripled.pointsMap_comp e.symm.toRingHom e.toRingHom)
  simp only [MonoidHom.comp_apply] at h
  rw [show (iterateFrobenius (d4Closure q hv) (d4Char q hv)
      (ValidLieTypeIndex.fieldExponent ⟨_, hv⟩)) = e.toRingHom from rfl, ← h,
    RingEquiv.toRingHom_comp_symm_toRingHom, D4Tripled.pointsMap_id, MonoidHom.id_apply]

theorem D4PushDown.isTwistedIsogeny_steinberg
    (P : D4PushDown (d4Closure q hv)) (hp2 : q.p ≠ 2) :
    IsTwistedIsogeny .D4 (d4Closure q hv) (d4Fr q hv) (d4Index q hv).steinberg P.π := by
  have hp2' : d4Char q hv ≠ 2 := by rw [d4Char_eq]; exact hp2
  have h2 : (2 : d4Closure q hv) ≠ 0 := two_ne_zero_of_charP hp2'
  refine (P.blockCarrier h2).isTwistedIsogeny (t := .D4) (p := d4Char q hv) (by decide) hp2'
    P.zeros (d4Index q hv).steinberg (d4Fr q hv) d4_steinberg_u d4_steinberg_v fun k hk => ?_
  apply P.π_eq_one_of_mem_center
  have hc := Subgroup.mem_center_iff.1 ((P.blockCarrier h2).ker_center k hk)
  refine Subgroup.mem_center_iff.2 fun w => ?_
  obtain ⟨w', rfl⟩ := d4_steinberg_surjective w
  exact ((map_mul _ w' k).symm.trans (congrArg (d4Index q hv).steinberg (hc w'))).trans
    (map_mul _ k w')

theorem nonempty_mulEquiv_group_trialityD4
    (P : D4PushDown (d4Closure q hv)) (hp2 : q.p ≠ 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q.card ^ TwistTag.D4.order)
    (σ : K →+* K) (hσ : ∀ x, σ x = x ^ q.card) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ) ≃*
      ValidLieTypeIndex.Group ⟨LieTypeIndex.trialityD4 q, hv⟩) := by
  set p := d4Char q hv with hpdef
  set f := ValidLieTypeIndex.fieldExponent ⟨_, hv⟩ with hfdef
  have hq : q.card = p ^ f := by
    rw [← LieTypeIndex.fieldOrder_trialityD4 q]
    exact ValidLieTypeIndex.fieldOrder_eq_characteristic_pow ⟨_, hv⟩
  have hp : p.Prime := Fact.out
  have hf : 1 ≤ f := ValidLieTypeIndex.fieldExponent_pos ⟨_, hv⟩
  have hK' : Nat.card K = (p ^ f) ^ TwistTag.D4.order := by rw [hK, hq]
  have hσ' : ∀ c, σ c = c ^ (p ^ f) := fun c => by rw [hσ, hq]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := f * 3) (by omega) (by rw [hK', pow_mul]; rfl)
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have : Algebra.IsAlgebraic (ZMod p) K := Algebra.IsAlgebraic.of_finite (ZMod p) K
  let ι : K →ₐ[ZMod p] d4Closure q hv := IsAlgClosed.lift
  let : Algebra K (d4Closure q hv) := ι.toRingHom.toAlgebra
  have : IsScalarTower (ZMod p) K (d4Closure q hv) :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have : Algebra.IsAlgebraic K (d4Closure q hv) :=
    Algebra.IsAlgebraic.tower_top (K := ZMod p) K
  have : IsAlgClosure K (d4Closure q hv) := ⟨inferInstance, inferInstance⟩
  have hFr : ∀ c, d4Fr q hv c = c ^ (p ^ f) := fun c => by rw [iterateFrobenius_def]
  obtain ⟨e⟩ := nonempty_derivedCentralQuotient_equiv (t := .D4) (d4Closure q hv) (d4Fr q hv) hp
    hf hK' hσ' hFr (P.isTwistedIsogeny_steinberg hp2)
  exact ⟨e.symm⟩

theorem twistedBridge_trialityD4_of
    (hP : ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p ≠ 2 →
      D4PushDown (d4Closure q hv)) :
    TwistedBridge .D4 LieTypeIndex.trialityD4 := fun q hv hp2 K _ _ hK σ hσ =>
  nonempty_mulEquiv_group_trialityD4 (hP q hv hp2) hp2 K hK σ hσ

end CFSG.TauCetiBridge.Twisted
