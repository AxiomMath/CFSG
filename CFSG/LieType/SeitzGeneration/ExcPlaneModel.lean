module

public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

theorem exists_field_pow (q : PrimePower) {m : ℕ} (hm : 0 < m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ^ m ∧ CharP K q.p := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  exact ⟨GaloisField q.p (q.exponent * m), inferInstance, inferInstance, by
    rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos hm).ne', PrimePower.card_def, pow_mul],
    inferInstance⟩

theorem not_dvd_card_of_ne {q : PrimePower} {p : ℕ} (hp : p.Prime) (h : p ≠ q.p) :
    ¬ p ∣ q.card := by
  intro hd
  rw [PrimePower.card_def] at hd
  exact h ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow hd))

section Adjoint


theorem exists_catEquiv_adjointGroup {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : Even.UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧ CharP K q.p ∧
      Nonempty (Cat ⟨c q, hv⟩ ≃* ↥(adjointGroup τ K)) := by
  obtain ⟨K, _, _, hK, hKchar⟩ := exists_field_pow q Nat.one_pos
  rw [pow_one] at hK
  obtain ⟨φ⟩ := hB q hv K hK
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨K, inferInstance, inferInstance, hK, hKchar,
    ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

end Adjoint

section Triality


theorem chevalleyModel_cat_trialityD4 {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) :
    ChevalleyExceptionalModel (Cat ⟨.trialityD4 q, hv⟩) .trialityD4 q.p q.exponent := by
  obtain ⟨K, _, _, hK, -⟩ := exists_field_pow q (m := TwistTag.D4.order) TwistTag.D4.order_pos
  rw [PrimePower.card_def] at hK
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p q.exponent_pos K hK
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.trialityD4 q hv K (by rw [PrimePower.card_def]; exact hK)
    σ.toRingHom hσ'
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance, inferInstance, hK, σ.toRingHom,
    hσ'', ⟨φ.symm⟩⟩

end Triality

section ReeF4


theorem reeTitsModel_cat_reeF4 {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid) :
    ReeTitsModel (Cat ⟨.reeF4 m, hv⟩) .twistedF4 2 (2 * m + 1) := by
  have hm1 : 1 ≤ m :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  exact ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
    ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
      ⟨e₁.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩

end ReeF4

end CFSG.LieType.SeitzGeneration
