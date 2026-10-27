module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6AlignChain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg
open scoped commutatorElement

local instance f4PilotQ2E6AlignGenNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

theorem commutator_f4Par_long {K : Type} [Field K] [CharP K 2] {α β : Fin (Tag.rank .F4) → ℤ}
    (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hsum : IsRoot .F4 (α + β)) (hsub : ¬ IsRoot .F4 (β - α))
    (h12 : ¬ IsRoot .F4 (α + 2 • β)) (h21 : ¬ IsRoot .F4 (2 • α + β)) (c d : K) :
    ⁅Adjoint.f4Par K α c, Adjoint.f4Par K β d⁆ = Adjoint.f4Par K (α + β) (c * d) := by
  rw [Adjoint.commutator_xPar Adjoint.f4Data_valid Adjoint.noG2_F4 hα hβ hne hne',
    Adjoint.xPar_of_not_isRoot h12, Adjoint.xPar_of_not_isRoot h21, mul_one, mul_one]
  have hN : (Adjoint.RootOperatorFamily'.coeff11 (CFSG.LieType.Chevalley.rootOperatorFamily .F4)
      Adjoint.f4Data_valid ⟨α, hα⟩ ⟨β, hβ⟩).natAbs = 1 := by
    rw [Adjoint.RootOperatorFamily'.coeff11,
      Adjoint.RootOperatorFamily'.bracketCoeff_natAbs
        (CFSG.LieType.Chevalley.rootOperatorFamily .F4) Adjoint.f4Data_valid
        (fun h => hne' (by rw [show β = -α from h, neg_neg])) hsum]
    exact Adjoint.stringNorm_of_not_isRoot hsub
  have h1 : ((Adjoint.RootOperatorFamily'.coeff11 (CFSG.LieType.Chevalley.rootOperatorFamily .F4)
      Adjoint.f4Data_valid ⟨α, hα⟩ ⟨β, hβ⟩ : ℤ) : K) = 1 := by
    rcases Int.natAbs_eq_iff.1 hN with h | h <;> rw [h]
    · simp
    · push_cast
      exact CharTwo.neg_eq (1 : K)
  rw [h1, one_mul]

theorem conj_f4Par_long {K : Type} [Field K] [CharP K 2] {α β : Fin (Tag.rank .F4) → ℤ}
    (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hsum : IsRoot .F4 (α + β)) (hsub : ¬ IsRoot .F4 (β - α))
    (h12 : ¬ IsRoot .F4 (α + 2 • β)) (h21 : ¬ IsRoot .F4 (2 • α + β)) (c d : K) :
    Adjoint.f4Par K α c * Adjoint.f4Par K β d * (Adjoint.f4Par K α c)⁻¹ =
      Adjoint.f4Par K (α + β) (c * d) * Adjoint.f4Par K β d := by
  rw [← commutator_f4Par_long hα hβ hne hne' hsum hsub h12 h21, commutatorElement_def]
  group

theorem commute_f4Par {K : Type} [Field K] {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hδ : IsRoot .F4 δ) (hne : γ + δ ≠ 0) (hn : ¬ IsRoot .F4 (γ + δ)) (a b : K) :
    Commute (Adjoint.f4Par K γ a) (Adjoint.f4Par K δ b) :=
  Adjoint.commute_xPar Adjoint.f4Data_valid Adjoint.noG2_F4 hγ hδ hne hn a b

theorem mem_closure_of_relay {H : Type*} [Group H] {S : Set H} {xt xg xd xa xb : H}
    (h1 : xt * xg * xt⁻¹ = xd * xg) (h2 : Commute xt xa) (h3 : Commute xd xg)
    (h4 : ⁅xb, xd⁆ = xa) (ht : xt ∈ closure S) (hb : xb ∈ closure S)
    (hu : xa * xg ∈ closure S) : xa ∈ closure S := by
  have hd : xd = (xa * xg)⁻¹ * (xt * (xa * xg) * xt⁻¹) := by
    have e1 : xt * (xa * xg) * xt⁻¹ = xa * (xd * xg) := by
      have e2 : xt * xa * xt⁻¹ = xa := by rw [h2.eq, mul_inv_cancel_right]
      calc xt * (xa * xg) * xt⁻¹ = (xt * xa * xt⁻¹) * (xt * xg * xt⁻¹) := by group
        _ = xa * (xd * xg) := by rw [e2, h1]
    rw [e1, h3.eq]
    group
  have hdS : xd ∈ closure S := by
    rw [hd]
    exact mul_mem (inv_mem hu) (mul_mem (mul_mem ht hu) (inv_mem ht))
  rw [← h4, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hb hdS) (inv_mem hb)) (inv_mem hdS)

@[expose] def RelayRootData (t g d a b : Fin (Tag.rank .F4) → ℤ) : Prop :=
  t ∈ rootFinset .F4 ∧ g ∈ rootFinset .F4 ∧ d ∈ rootFinset .F4 ∧ a ∈ rootFinset .F4 ∧
    b ∈ rootFinset .F4 ∧ t + g = d ∧ t ≠ g ∧ t ≠ -g ∧ g - t ∉ rootFinset .F4 ∧
    t + 2 • g ∉ rootFinset .F4 ∧ 2 • t + g ∉ rootFinset .F4 ∧ t + a ≠ 0 ∧
    t + a ∉ rootFinset .F4 ∧ d + g ≠ 0 ∧ d + g ∉ rootFinset .F4 ∧ b + d = a ∧ b ≠ d ∧
    b ≠ -d ∧ d - b ∉ rootFinset .F4 ∧ b + 2 • d ∉ rootFinset .F4 ∧ 2 • b + d ∉ rootFinset .F4

theorem f4Par_mem_closure_of_relay {K : Type} [Field K] [CharP K 2]
    {S : Set (adjointGroup .F4 K)} {t g d a b : Fin (Tag.rank .F4) → ℤ}
    (hD : RelayRootData t g d a b) (ht : Adjoint.f4Par K t 1 ∈ closure S)
    (hb : Adjoint.f4Par K b 1 ∈ closure S)
    (hu : Adjoint.f4Par K a 1 * Adjoint.f4Par K g 1 ∈ closure S) :
    Adjoint.f4Par K a 1 ∈ closure S := by
  obtain ⟨htr, hgr, hdr, har, hbr, htg, h1, h2, h3, h4, h5, h6, h7, h8, h9, hbd, h10, h11, h12,
    h13, h14⟩ := hD
  have htr' := mem_rootFinset.1 htr
  have hgr' := mem_rootFinset.1 hgr
  have hdr' := mem_rootFinset.1 hdr
  have har' := mem_rootFinset.1 har
  have hbr' := mem_rootFinset.1 hbr
  have hC1 := conj_f4Par_long (K := K) htr' hgr' h1 h2 (by rw [htg]; exact hdr')
    (fun h => h3 (mem_rootFinset.2 h)) (fun h => h4 (mem_rootFinset.2 h))
    (fun h => h5 (mem_rootFinset.2 h)) 1 1
  rw [htg, mul_one] at hC1
  have hC2 := commute_f4Par (K := K) htr' har' h6 (fun h => h7 (mem_rootFinset.2 h)) 1 1
  have hC3 := commute_f4Par (K := K) hdr' hgr' h8 (fun h => h9 (mem_rootFinset.2 h)) 1 1
  have hC4 := commutator_f4Par_long (K := K) hbr' hdr' h10 h11 (by rw [hbd]; exact har')
    (fun h => h12 (mem_rootFinset.2 h)) (fun h => h13 (mem_rootFinset.2 h))
    (fun h => h14 (mem_rootFinset.2 h)) 1 1
  rw [hbd, mul_one] at hC4
  exact mem_closure_of_relay hC1 hC2 hC3 hC4 ht hb hu

set_option maxRecDepth 100000 in
theorem relayRootData_check :
    RelayRootData rootR (-root1242) (f4Vec 1 1 0 0) (Pi.single 0 1) (-Pi.single 1 1) ∧
      RelayRootData (-rootR) root1242 (-f4Vec 1 1 0 0) (-Pi.single 0 1) (Pi.single 1 1) ∧
      RelayRootData rootR (-rootE2pE3Align) (f4Vec 1 1 2 2) (Pi.single 0 1)
        (-rootE1mE2Align) ∧
      RelayRootData (-rootR) rootE2pE3Align (-f4Vec 1 1 2 2) (-Pi.single 0 1)
        rootE1mE2Align := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold RelayRootData <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

theorem rankOne_zero_le_closure_of_mem {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {S : Set (adjointGroup .F4 K)} (hp : Adjoint.f4Par K (Pi.single 0 1) 1 ∈ closure S)
    (hn : Adjoint.f4Par K (-Pi.single 0 1) 1 ∈ closure S) :
    CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup 0 ≤ closure S := by
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have := Fintype.ofFinite K
      have h' := FiniteField.pow_card_sub_one_eq_one c hc
      rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h'
  refine sup_le (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff (isRoot_single _ 0) y).1 hy
    rcases h01 c with rfl | rfl
    · rw [Adjoint.xPar_zero]
      exact one_mem _
    · exact hp
  · obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff (isRoot_neg_single _ 0) y).1 hy
    rcases h01 c with rfl | rfl
    · rw [Adjoint.xPar_zero]
      exact one_mem _
    · exact hn

theorem twoA3GenInput_holds : TwoA3GenInput := by
  intro K _ _ _ hK
  obtain ⟨d1, d2, d3, d4⟩ := relayRootData_check
  constructor
  · have hθ : Adjoint.f4Par K rootR 1 ∈ closure ((f4RootPairAlign K rootR : Set _) ∪
        (f4RootPairAlign K (Pi.single 1 1) : Set _) ∪
          {relayAlign K root1242, relayAlign' K root1242}) :=
      subset_closure (Or.inl (Or.inl (mem_sup_left (Adjoint.xPar_mem (mem_rootFinset.1 d1.1) 1))))
    have hθ' : Adjoint.f4Par K (-rootR) 1 ∈ closure ((f4RootPairAlign K rootR : Set _) ∪
        (f4RootPairAlign K (Pi.single 1 1) : Set _) ∪
          {relayAlign K root1242, relayAlign' K root1242}) :=
      subset_closure (Or.inl (Or.inl (mem_sup_right (Adjoint.xPar_mem (mem_rootFinset.1 d2.1) 1))))
    have hb : Adjoint.f4Par K (-Pi.single 1 1) 1 ∈ closure ((f4RootPairAlign K rootR : Set _) ∪
        (f4RootPairAlign K (Pi.single 1 1) : Set _) ∪
          {relayAlign K root1242, relayAlign' K root1242}) :=
      subset_closure (Or.inl (Or.inr (mem_sup_right
        (Adjoint.xPar_mem (isRoot_neg_single _ 1) 1))))
    have hb' : Adjoint.f4Par K (Pi.single 1 1) 1 ∈ closure ((f4RootPairAlign K rootR : Set _) ∪
        (f4RootPairAlign K (Pi.single 1 1) : Set _) ∪
          {relayAlign K root1242, relayAlign' K root1242}) :=
      subset_closure (Or.inl (Or.inr (mem_sup_left (Adjoint.xPar_mem (isRoot_single _ 1) 1))))
    exact rankOne_zero_le_closure_of_mem hK
      (f4Par_mem_closure_of_relay d1 hθ hb (subset_closure (Or.inr (Or.inl rfl))))
      (f4Par_mem_closure_of_relay d2 hθ' hb' (subset_closure (Or.inr (Or.inr rfl))))
  · have hθ : Adjoint.f4Par K rootR 1 ∈ closure ((f4RootPairAlign K rootR : Set _) ∪
        (f4RootPairAlign K rootE1mE2Align : Set _) ∪
          {relayAlign K rootE2pE3Align, relayAlign' K rootE2pE3Align}) :=
      subset_closure (Or.inl (Or.inl (mem_sup_left (Adjoint.xPar_mem (mem_rootFinset.1 d3.1) 1))))
    have hθ' : Adjoint.f4Par K (-rootR) 1 ∈ closure ((f4RootPairAlign K rootR : Set _) ∪
        (f4RootPairAlign K rootE1mE2Align : Set _) ∪
          {relayAlign K rootE2pE3Align, relayAlign' K rootE2pE3Align}) :=
      subset_closure (Or.inl (Or.inl (mem_sup_right (Adjoint.xPar_mem (mem_rootFinset.1 d4.1) 1))))
    have hb : Adjoint.f4Par K (-rootE1mE2Align) 1 ∈ closure ((f4RootPairAlign K rootR : Set _) ∪
        (f4RootPairAlign K rootE1mE2Align : Set _) ∪
          {relayAlign K rootE2pE3Align, relayAlign' K rootE2pE3Align}) :=
      subset_closure (Or.inl (Or.inr (mem_sup_right
        (Adjoint.xPar_mem (mem_rootFinset.1 d3.2.2.2.2.1) 1))))
    have hb' : Adjoint.f4Par K rootE1mE2Align 1 ∈ closure ((f4RootPairAlign K rootR : Set _) ∪
        (f4RootPairAlign K rootE1mE2Align : Set _) ∪
          {relayAlign K rootE2pE3Align, relayAlign' K rootE2pE3Align}) :=
      subset_closure (Or.inl (Or.inr (mem_sup_left
        (Adjoint.xPar_mem (mem_rootFinset.1 d4.2.2.2.2.1) 1))))
    exact rankOne_zero_le_closure_of_mem hK
      (f4Par_mem_closure_of_relay d3 hθ hb (subset_closure (Or.inr (Or.inl rfl))))
      (f4Par_mem_closure_of_relay d4 hθ' hb' (subset_closure (Or.inr (Or.inr rfl))))

theorem twoTwistedE6AlignInput_of_chainInput' (hC : TwoTwistedE6ChainInput) :
    TwoTwistedE6AlignInput :=
  twoTwistedE6AlignInput_of_chainInput twoA3GenInput_holds hC

theorem twoE6PairInput_of_chainInput' (hC : TwoE6ChainInput) (hU : TwoE6UniqueInput) :
    TwoE6PairInput :=
  twoE6PairInput_of_chainInput twoA3GenInput_holds hC hU

end CFSG.SeitzReduction.F4Pilot
