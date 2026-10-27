module

public import CFSG.LieType.ChevTwo.OppositeFixedExcE78
public import CFSG.LieType.Ree.ReeGenericPerfect
public import CFSG.LieType.Ree.LargeReeCenterTrivial
public import CFSG.LieType.BorelTits.DerivedQuotient

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

section Cert


theorem nonempty_derivedCentralQuotient_equiv_reeGamma {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {H : Subgroup (ModGL ReeTag.F4.tag K)} (hH : H = ReeTag.F4.reeGamma K a) :
    Nonempty (DerivedCentralQuotient H ≃* ↥(ReeTag.F4.reeGamma K a)) := by
  have hc : _root_.commutator ↥(ReeTag.F4.reeGamma K a) = ⊤ :=
    commutator_reeGamma_eq_top ha hK
  have hZ : Subgroup.center ↥(ReeTag.F4.reeGamma K a) = ⊥ :=
    large_Ree_fixed_group_center_trivial a K hK
  let e1 := CFSG.LieType.BorelTits.derivedCentralQuotientEquiv H (MulEquiv.subgroupCongr hH)
  let f : ↥(_root_.commutator ↥(ReeTag.F4.reeGamma K a)) ≃* ↥(ReeTag.F4.reeGamma K a) :=
    (MulEquiv.subgroupCongr hc).trans Subgroup.topEquiv
  have hfc : (Subgroup.center ↥(_root_.commutator ↥(ReeTag.F4.reeGamma K a))).map
      f.toMonoidHom = ⊥ := by
    exact (Subgroup.map_center_eq f).trans hZ
  exact ⟨e1.trans ((QuotientGroup.congr _ ⊥ f hfc).trans QuotientGroup.quotientBot)⟩

theorem exists_mulEquiv_reeGamma {S : Type} [Group S] {a : ℕ} (ha : 1 ≤ a)
    (h : ReeTitsModel S .twistedF4 2 (2 * a + 1)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      Nat.card K = 2 ^ (2 * a + 1) ∧ Nonempty (S ≃* ↥(ReeTag.F4.reeGamma K a)) := by
  obtain ⟨-, a', ha', hrel⟩ := h
  have hrel' : ReeTitsRelationModel S .F4 reeF4Perm reeF4Long 2 (2 * a + 1) a' := hrel
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := hrel'
  have haa : a' = a := by omega
  subst haa
  haveI : CharP K 2 := charP_two_of_card_two_pow hcard
  haveI : CharP K ReeTag.F4.prime := (inferInstance : CharP K 2)
  have hH : reeFixedGroup .F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a' else 2 ^ (a' + 1)) =
      ReeTag.F4.reeGamma K a' :=
    (reeGamma_eq_reeFixedGroup (t := ReeTag.F4) (K := K) (a := a')).symm
  obtain ⟨e2⟩ := nonempty_derivedCentralQuotient_equiv_reeGamma (K := K) ha hcard hH
  exact ⟨K, inferInstance, inferInstance, inferInstance, hcard, ⟨e.trans e2⟩⟩

end Cert

end CFSG.LieType.ChevTwo.Semi
