module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8MinDeg
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.BinRep
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.RouteB
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.CentralExt.FieldTwo
  CFSG.LocalAnalysis.ComponentInitial CFSG.Open

section E8Two


theorem adjointGroup_E8_two_autInner (φ : adjointGroup .E8 (ZMod 2) ≃* adjointGroup .E8 (ZMod 2)) :
    ∃ s : adjointGroup .E8 (ZMod 2), ∀ x, φ x = s * x * s⁻¹ := by
  obtain ⟨Θ, -, -, hker, -⟩ := (even_E7_E8_exact_inner_field_automorphism_normal_form
    (f := 1) le_rfl (ZMod 2) (by simp) .E8 (Or.inr rfl)).2
  have h1 : Θ φ = 1 := Subsingleton.elim _ _
  have h2 : φ ∈ Θ.ker := h1
  rw [hker] at h2
  obtain ⟨s, hs⟩ := h2
  exact ⟨s, fun x => by rw [← hs]; rfl⟩

@[expose] def adjointQuotientEquiv (K : Type) [Field K] [Finite K] :
    AdjointQuotient .E8 K ≃* adjointGroup .E8 K :=
  (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot

theorem center_eq_bot_of_E8_two {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : L ⧸ Subgroup.center L ≃* AdjointQuotient .E8 K) : Subgroup.center L = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 1) le_rfl
    (by simpa using hK)
  obtain ⟨-, hM⟩ := e8_two_hopfMultiplier hK
  have hfin : Finite (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) :=
    Finite.of_subsingleton
  have h1 := GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hL e
  have h2 : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) = 1 :=
    Nat.card_unique
  rw [h2] at h1
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 h1)


theorem noIrrFFOffender_E8_two (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (hq : q.p = 2)
    (hq1 : q.exponent = 1) : NoIrrFFOffender (CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  intro W _ _ hW L E hql hirr ⟨e⟩ hEN hE hel _
  obtain ⟨K, _, _, hK, ⟨e0⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 q hv hq (MulEquiv.refl _)
  have hK2 : Nat.card K = 2 := by rw [hK, hq, hq1, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card]
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
  let eS : ↥L ⧸ Subgroup.center ↥L ≃* adjointGroup .E8 (ZMod 2) :=
    e.trans (e0.trans ((CFSG.TauCetiBridge.adjointQuotientCongr φ).trans
      (adjointQuotientEquiv (ZMod 2))))
  have hLfin : Finite ↥L := inferInstance
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_E8_two hql hK2 (e.trans e0)
  let f : ↥L →* adjointGroup .E8 (ZMod 2) :=
    eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, eS.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    have h1 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk y :=
      eS.injective hxy
    rw [QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  let ι : adjointGroup .E8 (ZMod 2) ≃* ↥L := (MulEquiv.ofBijective f hf).symm
  obtain ⟨V, _, _, _, ρ, hρ, hfaith, hVW⟩ := exists_simpleRep_of_isIrrOn hW hirr ι
  have hdim := e8_two_min_degree hρ hfaith
  have hVcard : 2 ^ 248 ≤ Nat.card W := by
    rw [← hVW, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by norm_num) hdim
  have hSord : Nat.card (adjointGroup .E8 (ZMod 2)) < 2 ^ 248 := by
    rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, Nat.card_zmod]
    unfold ordE8
    norm_num
  refine exclusion_of_card_lt_of_outer hW hql hirr hEN hE hel (k := 1) eS
    (fun B _ _ => card_le_of_autInner adjointGroup_E8_two_autInner B) ?_
  rw [hZ, Subgroup.card_bot, one_mul, one_mul]
  exact lt_of_lt_of_le hSord hVcard

end E8Two

end CFSG.HardMathSupport.Cooperstein.Coordinator
