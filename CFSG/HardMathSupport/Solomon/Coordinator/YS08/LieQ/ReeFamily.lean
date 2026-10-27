module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Descent
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Two
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.ReeLITwo
public import CFSG.LieType.ChevTwo.OppositeFixedExcTits
public import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.BorelTits CFSG.Open CFSG.LieType.ChevTwo
  CFSG.LieType.ChevTwo.Semi

set_option linter.unusedSectionVars false

section Fam

theorem radRigid_twistedF4_of_LI {S : Type} [Group S] {a : ℕ} (ha : 1 ≤ a)
    (h : ReeTitsModel S .twistedF4 2 (2 * a + 1))
    (hLI : ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
      Nat.card K = 2 ^ (2 * a + 1) → ReeLI K a) : RadRigid 2 S := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_reeGamma ha h
  exact RadRigid.of_mulEquiv e.symm (radRigid_reeGamma_of_LI (hLI K hK))

theorem radRigid_tits_of_LI {S : Type} [Group S] (h : ReeTitsModel S .Tits 2 1)
    (hLI : ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
      Nat.card K = 2 → ∀ j, ReeLIOddAt K 0 j) : RadRigid 2 S := by
  have hS := CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier S 2 1 h
  obtain ⟨-, a, hf, hmodel⟩ := h
  have ha : a = 0 := by omega
  subst ha
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := hc
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have e' := e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K 0)).trans
      ((reeFixed ReeTag.F4 K 0).equivMapOfInjective _ Subtype.val_injective).symm))
  let e1 : S ≃* ↥(commutator ↥(reeFixed ReeTag.F4 K 0)) :=
    e'.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.Sporadic.Schreier.Tits.center_commutator_reeFixed hK2)).trans
      QuotientGroup.quotientBot)
  have hΓ : RadRigidInner 2 ↥(reeFixed ReeTag.F4 K 0) :=
    RadRigidInner.of_mulEquiv (reeFixedEquivReeGamma K 0).symm
      (radRigidInner_reeGamma_of_oddLI (hLI K hK2))
  have hT : RadRigidInner 2 ↥(commutator ↥(reeFixed ReeTag.F4 K 0)) :=
    radRigidInner_of_normal _ hΓ
  have hinner : ∀ α : MulAut ↥(commutator ↥(reeFixed ReeTag.F4 K 0)), Odd (orderOf α) →
      α ∈ (MulAut.conj : ↥(commutator ↥(reeFixed ReeTag.F4 K 0)) →*
        MulAut ↥(commutator ↥(reeFixed ReeTag.F4 K 0))).range := by
    intro α hα
    have hα' : Odd (orderOf (MulAut.congr e1.symm α)) := by
      rwa [MulEquiv.orderOf_eq]
    obtain ⟨s, hs⟩ := inner_of_odd_orderOf_of_outer hS.1 _ hα'
    refine ⟨e1 s, ?_⟩
    have h1 : MulAut.conj (e1 s) = MulAut.congr e1 (MulAut.conj s) :=
      (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e1 s).symm
    rw [h1]
    change MulAut.congr e1 (MulAut.conj s) = α
    rw [show (MulAut.conj s : MulAut S) = MulAut.congr e1.symm α from hs]
    ext x
    simp [MulAut.congr_apply]
  exact RadRigid.of_mulEquiv e1.symm
    (radRigid_two_of_inner (CFSG.Sporadic.Schreier.Tits.center_commutator_reeFixed hK2) hinner hT)

end Fam

section Final

theorem reeFamily_of_LI
    (hLI : ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (a : ℕ), 1 ≤ a →
      Nat.card K = 2 ^ (2 * a + 1) → ReeLI K a)
    (hT : ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
      Nat.card K = 2 → ∀ j, ReeLIOddAt K 0 j) : ReeFamily := by
  intro S _ _ hs t f ht h hBT
  rcases ht with rfl | rfl
  · obtain ⟨a, hfa⟩ : ∃ a : ℕ, f = 2 * a + 1 := ⟨_, h.2.choose_spec.1⟩
    have h3 : 3 ≤ f := h.1.2.2.2.2.2
    subst hfa
    exact radRigid_twistedF4_of_LI (by omega) h fun K _ _ _ hK => hLI K a (by omega) hK
  · have hf : f = 1 := h.1.2.2.2.2
    subst hf
    exact radRigid_tits_of_LI h hT

@[expose] def TitsLI : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
    ∀ j, ReeLIOddAt K 0 j

theorem reeFamily_of_titsLI (hT : TitsLI) : ReeFamily :=
  reeFamily_of_LI (fun _ _ _ _ _ ha hK => reeLI_of_one_le ha hK) hT

theorem lieQConstrained_two_of_titsLI (hT : TitsLI) : LieQConstrained 2 :=
  lieQConstrained_two_of_ree (reeFamily_of_titsLI hT)

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
