module

public import CFSG.Adapters.TauCetiExceptional.EvenE6d
public import CFSG.Adapters.TauCetiExceptional.EvenInterface
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import CFSG.Adapters.TauCetiExceptional.TwistedE6Push

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell Twisted

variable {q : PrimePower} {hv : (LieTypeIndex.twistedE6 q).Valid}

theorem isTwistedIsogeny_steinberg_e6_two
    (P : Twisted.E6PushDown (e6Closure q hv))
    (hp2 : q.p = 2) :
    IsTwistedIsogeny .E6 (e6Closure q hv) (e6Fr q hv) (e6Index q hv).steinberg P.π := by
  have hp2' : e6Char q hv = 2 := by rw [e6Char_eq]; exact hp2
  refine isTwistedIsogeny_two (t := .E6) (E6PushDown.blockCarrierTwo P) (p := e6Char q hv) hp2'
    (by decide) (exclTwo_e6 P) P.zeros (e6Index q hv).steinberg (e6Fr q hv) e6_steinberg_u
    e6_steinberg_v fun k hk => ?_
  apply P.π_eq_one_of_mem_center
  have hc := Subgroup.mem_center_iff.1 ((E6PushDown.blockCarrierTwo P).ker_center k hk)
  refine Subgroup.mem_center_iff.2 fun w => ?_
  obtain ⟨w', rfl⟩ := e6_steinberg_surjective w
  exact ((map_mul _ w' k).symm.trans (congrArg (e6Index q hv).steinberg (hc w'))).trans
    (map_mul _ k w')

theorem nonempty_mulEquiv_group_twistedE6_two
    (P : Twisted.E6PushDown (e6Closure q hv))
    (hp2 : q.p = 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q.card ^ TwistTag.E6.order) (σ : K →+* K) (hσ : ∀ x, σ x = x ^ q.card) :
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
    hf hK' hσ' hFr (isTwistedIsogeny_steinberg_e6_two P hp2)
  exact ⟨e.symm⟩

theorem twistedBridgeEven_twistedE6
    : TwistedBridgeEven .E6 LieTypeIndex.twistedE6 :=
  fun q hv hp2 K _ _ hK σ hσ =>
    nonempty_mulEquiv_group_twistedE6_two (e6PushDown (e6Closure q hv)) hp2 K hK σ hσ

end CFSG.TauCetiBridge.Even
