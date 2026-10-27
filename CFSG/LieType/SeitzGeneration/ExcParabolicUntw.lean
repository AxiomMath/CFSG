module

public import CFSG.LieType.SeitzGeneration.ExcParabolicModel
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge

theorem isSimpleGroup_adjointGroup_of_isQuasisimple
    {τ : Tag} {K : Type} [Field K] [Finite K]
    (hq : IsQuasisimple ↥(adjointGroup τ K)) : IsSimpleGroup ↥(adjointGroup τ K) :=
  CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
    ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := τ) (K := K))).trans
      QuotientGroup.quotientBot).symm

section Generic


theorem seitzExcParabolicFor_untwisted (τ : Tag) (c : TauCeti.PrimePower → TauCeti.LieTypeIndex)
    (hchar : ∀ q, (c q).characteristic = q.p) (hB : Even.UntwistedBridgeAll τ c)
    (hS : ∀ q : TauCeti.PrimePower, (c q).Valid → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = q.card → IsSimpleGroup ↥(adjointGroup τ K)) :
    SeitzExcParabolicFor fun d => ∃ q, d = c q := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, ⟨q, rfl⟩, R, hR1, hRp, hRn⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrp : q.p ≠ p := fun h => hpd (by simp [hchar, h])
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = q.card ∧ CharP K q.p :=
    ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, by
      rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def], inferInstance⟩
  obtain ⟨φ⟩ := hB q hv K hK
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let e : Cat ⟨c q, hv⟩ ≃* ↥(adjointGroup τ K) :=
    φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have : IsSimpleGroup ↥(adjointGroup τ K) := hS q hv K hK
  have hgen : RootInvariantGeneration (adjointGroup τ K) q.p p := by
    intro A R hAC hA hcard hRC hRr hR hAR
    have := hA
    exact ordinary_root_invariant_prime_subgroup_centralizer_generation τ K q.p p hrp A hAC hcard
      R hRC hRr hR hAR
  exact planeGen_of_native e hZ hgen hE hc hin ⟨R, hR1, by simpa [hchar] using hRp, hRn⟩

end Generic

section G2


theorem isSimpleGroup_adjointGroup_G2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q.card) : IsSimpleGroup ↥(adjointGroup .G2 K) :=
  isSimpleGroup_adjointGroup_of_isQuasisimple
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K (by
      rw [hK]
      exact ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)))

end G2

section All


theorem seitzExcParabolicUntw : SeitzExcParabolicUntw :=
  SeitzExcParabolicFor.union
    (seitzExcParabolicFor_untwisted .G2 TauCeti.LieTypeIndex.G2
      (fun _ => TauCeti.LieTypeIndex.characteristic_G2 _) Even.chevalleyBridgesAll.g2
      isSimpleGroup_adjointGroup_G2)
    (SeitzExcParabolicFor.union
      (seitzExcParabolicFor_untwisted .F4 TauCeti.LieTypeIndex.F4
        (fun _ => TauCeti.LieTypeIndex.characteristic_F4 _) Even.chevalleyBridgesAll.f4
        fun _ _ K _ _ _ => isSimpleGroup_adjointGroup_of_isQuasisimple
          (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K))
      (SeitzExcParabolicFor.union
        (seitzExcParabolicFor_untwisted .E6 TauCeti.LieTypeIndex.E6
          (fun _ => TauCeti.LieTypeIndex.characteristic_E6 _) Even.chevalleyBridgesAll.e6
          fun _ _ K _ _ _ => isSimpleGroup_adjointGroup_of_isQuasisimple
            (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K))
        (SeitzExcParabolicFor.union
          (seitzExcParabolicFor_untwisted .E7 TauCeti.LieTypeIndex.E7
            (fun _ => TauCeti.LieTypeIndex.characteristic_E7 _) Even.chevalleyBridgesAll.e7
            fun _ _ K _ _ _ => isSimpleGroup_adjointGroup_of_isQuasisimple
              (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K))
          (seitzExcParabolicFor_untwisted .E8 TauCeti.LieTypeIndex.E8
            (fun _ => TauCeti.LieTypeIndex.characteristic_E8 _) Even.chevalleyBridgesAll.e8
            fun _ _ K _ _ _ => isSimpleGroup_adjointGroup_of_isQuasisimple
              (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K)))))

end All

end CFSG.LieType.SeitzGeneration
