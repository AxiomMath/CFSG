module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableHN
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpERed
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNLeaf
public import CFSG.Sporadic.HNOddCore.AlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdReduction

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def HNFixedComponents : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .HN) →
    ∀ Q : Subgroup (MulAut S), (∀ q ∈ Q, q * q = 1) → Nat.card Q ≤ 2 →
    ∀ T : Subgroup S, T ≤ EvenPump.autFixed Q →
      IsPComponent 2 (T.subgroupOf (EvenPump.autFixed Q)) →
      Nat.card (↥T ⧸ Open.fusionZStar ↥T) = 273030912000000 ∨
        Nat.card (↥T ⧸ Open.fusionZStar ↥T) = 44352000 ∨
        Nat.card (↥T ⧸ Open.fusionZStar ↥T) = 1814400

theorem lt_card_of_hnFixedComponents (h : HNFixedComponents) {S : Type} [Group S] [Finite S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HN) {Q : Subgroup (MulAut S)}
    (hQ2 : ∀ q ∈ Q, q * q = 1) (hQc : Nat.card Q ≤ 2) {T : Subgroup S}
    (hTF : T ≤ EvenPump.autFixed Q) (hT : IsPComponent 2 (T.subgroupOf (EvenPump.autFixed Q))) :
    360 < Nat.card (↥T ⧸ Open.fusionZStar ↥T) := by
  rcases h S ⟨e⟩ Q hQ2 hQc T hTF hT with h1 | h1 | h1 <;> rw [h1] <;> norm_num

private theorem card_quotient_fusionZStar_eq {K : Type*} [Group K] (hK : pPrimeCore 2 K = ⊥) :
    Nat.card (K ⧸ Open.fusionZStar K) = Nat.card (K ⧸ center K) :=
  Nat.card_congr ((Sol78.coreQuotientCenterEquiv K).symm.trans (Sol78.centerQuotCongr
    ((QuotientGroup.quotientMulEquivOfEq hK).trans QuotientGroup.quotientBot))).toEquiv

private theorem pPrimeCore_eq_bot_of_isSubnormal {X : Type*} [Group X] [Finite X]
    (hX : pPrimeCore 2 X = ⊥) {N : Subgroup X} (hN : N.IsSubnormal) : pPrimeCore 2 N = ⊥ := by
  have h := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hN
  rw [hX, inf_bot_eq] at h
  exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp h

private theorem isSimpleGroup_of_hn
    {S : Type} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HN) :
    IsSimpleGroup S ∧ ∃ a b : S, a * b ≠ b * a := by
  have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .HN) :=
    Sporadic.HNSchreier.fam_hn_certified_simplicity.2
  have hS : IsSimpleGroup S := e.isSimpleGroup
  refine ⟨hS, CatFC.nonabelian_of_simple_of_card_ne_prime ?_⟩
  rw [Nat.card_congr e.toEquiv, EvenPump.card_carrier_HN]
  norm_num

private theorem pPrimeCore_fixedSubgroup_eq_bot
    {S : Type} [Group S] [Finite S] (e : S ≃* Blueprint.NativeSporadic.Carrier .HN)
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) {σ : MulAut S}
    (hσ : orderOf σ = 2) : pPrimeCore 2 (fixedSubgroup σ) = ⊥ := by
  rcases CatLeaf.exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · have hu : orderOf u = 2 := SeitzReduction.OmegaPilot.orderOf_eq_two_of_conj hS hna hσ
    have hZ : center S = ⊥ := BMCase.center_eq_bot_of_isSimpleGroup hna
    have h := (Sporadic.HNOddCore.ctuc_hn_almost_simple_involution_centralizer_odd_core_trivial
      (⊤ : Subgroup S) ⟨Subgroup.topEquiv.trans e⟩
      (by rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ])).2 u hu
    rw [SeitzReduction.F4Pilot.fixedSubgroup_conj, ← Sol78.oddCore_eq_pPrimeCore]
    exact h
  · obtain ⟨φ⟩ := Sporadic.HNOddCore.hn_outer_involution_fixSub e σ hσ hout
    let ψ : fixedSubgroup σ ≃* Equiv.Perm (Fin 10) :=
      (MulEquiv.subgroupCongr (SeitzReduction.SporadicRefine.fixedSubgroup_eq_fixSub σ)).trans φ
    have h10 : pPrimeCore 2 (Equiv.Perm (Fin 10)) = ⊥ := by
      rw [← Sol78.oddCore_eq_pPrimeCore]
      exact (SmallLocal.symmetric_group_odd_core (Fin 10)).2 (by simp)
    have h1 := pPrimeCore_map_iso 2 ψ
    rw [h10] at h1
    exact (map_eq_bot_iff_of_injective _ ψ.injective).mp h1

private theorem card_of_fixedSubgroup
    {S : Type} [Group S] [Finite S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HN) (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {σ : MulAut S} (hσ : orderOf σ = 2) {T : Subgroup S}
    (hTF : T ≤ fixedSubgroup σ) (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup σ))) :
    Nat.card (↥T ⧸ Open.fusionZStar ↥T) = 44352000 ∨
      Nat.card (↥T ⧸ Open.fusionZStar ↥T) = 1814400 := by
  have hO := pPrimeCore_fixedSubgroup_eq_bot e hS hna hσ
  have hD : IsComponent (T.subgroupOf (fixedSubgroup σ)) :=
    RestrictedStd.isComponent_of_isPComponent_two hO hT
  have hc : Nat.card (↥T ⧸ Open.fusionZStar ↥T) =
      Nat.card (↥(T.subgroupOf (fixedSubgroup σ)) ⧸
        center ↥(T.subgroupOf (fixedSubgroup σ))) := by
    rw [← card_quotient_fusionZStar_eq (pPrimeCore_eq_bot_of_isSubnormal hO hD.2)]
    exact Nat.card_congr (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hTF).symm).toEquiv
  obtain ⟨hin, hout⟩ := CatFC.sporadic_rows_hn hS hna e hσ hD
  rw [hc]
  by_cases h : σ ∈ (MulAut.conj : S →* MulAut S).range
  · exact Or.inl (hin h)
  · exact Or.inr (hout h)

theorem hnFixedComponents_holds :
    HNFixedComponents := by
  intro S _ _ ⟨e⟩ Q hQ2 hQc T hTF hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, hna⟩ := isSimpleGroup_of_hn e
  have : Finite (MulAut S) := Finite.of_injective (fun e : MulAut S => e.toEquiv)
    fun _ _ h => MulEquiv.ext fun x => congrArg (fun f : S ≃ S => f x) h
  rcases (show Nat.card Q = 1 ∨ Nat.card Q = 2 by
      have := Nat.card_pos (α := Q)
      omega) with hQ1 | hQ2'
  ·
    left
    have hQb : Q = ⊥ := Subgroup.eq_bot_of_card_eq Q hQ1
    have hFtop : EvenPump.autFixed Q = ⊤ := by
      rw [eq_top_iff]
      intro l _ q hq
      rw [hQb, mem_bot] at hq
      rw [hq]
      rfl
    have hO : pPrimeCore 2 S = ⊥ := by
      rcases (pPrimeCore_normal (p := 2) (G := S)).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        have hc := pPrimeCore_coprime_card (p := 2) (G := S)
        rw [h, Subgroup.card_top, Nat.card_congr e.toEquiv, EvenPump.card_carrier_HN] at hc
        exact absurd hc (by norm_num)
    have hTp : IsPComponent 2 T :=
      (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 T (EvenPump.autFixed Q) hTF
        (by rw [hFtop]; exact Subgroup.IsSubnormal.top)).mp hT
    have hTc : IsComponent T := RestrictedStd.isComponent_of_isPComponent_two hO hTp
    have hTtop : T = ⊤ := by
      refine (hTc.2.eq_bot_or_top_of_isSimpleGroup hS).resolve_left fun hbot => ?_
      have : Nontrivial (↥T ⧸ center ↥T) := hTc.1.2.1.toNontrivial
      exact (Subgroup.nontrivial_iff_ne_bot T).mp
        (QuotientGroup.mk'_surjective (center ↥T)).nontrivial hbot
    let eT : ↥T ≃* S := (MulEquiv.subgroupCongr hTtop).trans Subgroup.topEquiv
    rw [Nat.card_congr (Sol78.fusionZStarQuotCongr eT).toEquiv, card_quotient_fusionZStar_eq hO,
      CatFC.card_quotient_center_of_simple hna, Nat.card_congr e.toEquiv,
      EvenPump.card_carrier_HN]
  ·
    right
    obtain ⟨⟨σ, hσQ⟩, hq₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQ2'
    have hσ1 : σ ≠ 1 := fun h => hq₀ (Subtype.ext h)
    have hσ : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hQ2 σ hσQ) hσ1
    have hF : EvenPump.autFixed Q = fixedSubgroup σ := by
      ext x
      rw [EvenPump.mem_autFixed, LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff]
      refine ⟨fun h => h σ hσQ, fun h q hq => ?_⟩
      by_cases hq1 : (⟨q, hq⟩ : ↥Q) = 1
      · rw [show q = 1 from congrArg Subtype.val hq1]
        rfl
      · rw [show q = σ from congrArg Subtype.val (huniq _ hq1)]
        exact h
    rw [hF] at hTF hT
    exact card_of_fixedSubgroup e hS hna hσ hTF hT

end CFSG.ComponentClassification.GSThmB.A10T
