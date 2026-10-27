module

public import CFSG.HardMathSupport.Dickson.BMRows.Defs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeAGlue
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeBNoComp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.B CFSG.Monster.Existence
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.HardMathSupport.Dickson.I271
  CFSG.Yardstones.Md0ec50421ce4

namespace CensusB3

@[expose] def IsFi22 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group)

theorem IsFi22.of_equiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T') (h : IsFi22 T) :
    IsFi22 T' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

section TypeThree


theorem shapeRkAt_fi22_typeThree
    (hBr : Nonempty (NativeSporadic.Fi22 ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group))
    {v w : CVert} (hw : w ∈ sphereThree v)
    (hcard : Nat.card (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) ≤
      3 * Nat.card (vStab v ⊓ vStab w : Subgroup Shat)) :
    ShapeRkAt 3 IsFi22 (fun (T : Type) [Group T] => True) (clabelS v * clabelS w) := by
  obtain ⟨hHQ, hHnorm, hcenter, hCQH⟩ : cnGroup v w ≤ vStab v ⊓ vStab w ∧
      ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w)).Normal ∧
      Subgroup.center (cnGroup v w) = ⊥ ∧
      (∀ q ∈ vStab v ⊓ vStab w, (∀ h ∈ cnGroup v w, q * h = h * q) → q = 1) := by
    obtain ⟨θ₀, -, hTT⟩ := native_order_three_common_neighbor_three_transposition_group
    obtain ⟨h1, h2, -, -, -, -, -, -, -, h10, -, -, -, h14, -⟩ := hTT v w hw
    exact ⟨h1, h2, h10, h14⟩
  obtain ⟨hsimp, hcardH, hcomm⟩ : IsSimpleGroup (cnGroup v w) ∧
      Nat.card (cnGroup v w) = 64561751654400 ∧ commutator (cnGroup v w) = ⊤ := by
    obtain ⟨h1, -, h3, h4, -⟩ := native_three_transposition_group_simple v w hw
    exact ⟨h1, h3, h4⟩
  obtain ⟨eF⟩ := native_three_transposition_group_nonempty_mulEquiv_Fi22 hw
  have h3 : orderOf (clabel v * clabel w) = 3 :=
    ((native_order_three_label_products_and_dihedral_triples v).1 w hw).1
  have hd2 : clabelS v * clabelS v = 1 := by
    have := pow_orderOf_eq_one (clabelS v)
    rwa [orderOf_clabelS, sq] at this
  have he2 : clabelS w * clabelS w = 1 := by
    have := pow_orderOf_eq_one (clabelS w)
    rwa [orderOf_clabelS, sq] at this
  have hso : orderOf (clabelS v * clabelS w) = 3 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, coe_clabelS, coe_clabelS]
    exact h3
  obtain ⟨s, hs⟩ : ∃ s : Shat, s = clabelS v * clabelS w := ⟨_, rfl⟩
  rw [← hs] at hcard hso ⊢
  have hs3 : s * s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hso, pow_three'] at this
  have hqs : ∀ q ∈ vStab v ⊓ vStab w, q * s = s * q := by
    intro q hq
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).1
    have h2 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).2
    rw [hs]
    calc q * (clabelS v * clabelS w) = q * clabelS v * clabelS w := by rw [mul_assoc]
      _ = clabelS v * q * clabelS w := by rw [h1]
      _ = clabelS v * (q * clabelS w) := by rw [mul_assoc]
      _ = clabelS v * (clabelS w * q) := by rw [h2]
      _ = clabelS v * clabelS w * q := by rw [mul_assoc]
  have hQC : vStab v ⊓ vStab w ≤ Subgroup.centralizer ({s} : Set Shat) :=
    fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hqs q hq)
  have hsQ : s ∉ vStab v ⊓ vStab w := by
    intro hsQ
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hsQ).1
    rw [hs] at h1
    have h2 : s * s = 1 := by
      rw [hs]
      calc clabelS v * clabelS w * (clabelS v * clabelS w)
          = clabelS v * clabelS w * clabelS v * clabelS w := by simp only [mul_assoc]
        _ = clabelS v * (clabelS v * clabelS w) * clabelS w := by rw [h1]
        _ = 1 := by rw [← mul_assoc, hd2, one_mul, he2]
    have h4 : s = 1 := by
      calc s = s * s * s * (s * s)⁻¹ := by group
        _ = 1 := by rw [hs3, h2, inv_one, one_mul]
    rw [h4, orderOf_one] at hso
    exact absurd hso (by norm_num)
  have hdecomp := mem_pow_mul_of_card_le (Subgroup.mem_centralizer_singleton_iff.2 rfl) hQC hs3
    hsQ hcard
  have hHn : ∀ q ∈ vStab v ⊓ vStab w, ∀ h ∈ cnGroup v w, q * h * q⁻¹ ∈ cnGroup v w := by
    intro q hq h hh
    have := hHnorm.conj_mem ⟨h, hHQ hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨q, hq⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hLq : CFSG.Open.IsQuasisimple ↥(cnGroup v w) :=
    ⟨hcomm, MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      QuotientGroup.quotientBot)⟩
  have hpL : 3 ∣ Nat.card ↥(cnGroup v w) := by rw [hcardH]; norm_num
  have hcore : GLAPPrimeCore 3 ↥(cnGroup v w) = ⊥ :=
    glaPPrimeCore_eq_bot_of_simple Nat.prime_three hpL
  obtain ⟨eB⟩ := hBr
  have hG : IsFi22 (PSimple 3 (cnGroup v w)) :=
    ⟨(pSimpleEquivSelf (cnGroup v w) hcore hcenter).trans (eF.trans eB)⟩
  have hs3' : s ^ 3 = 1 := by rw [pow_three']; exact hs3
  exact tabBThree_shapeRkAt_of_decomp Nat.prime_three hs3' hqs hHQ hdecomp hHn hLq hpL hCQH hG
    trivial

end TypeThree

section Inverted


theorem shapeRkAt'_fi22_of_inverted
    (hBr : Nonempty (NativeSporadic.Fi22 ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group))
    (hA : TabBThreeACard) {s d : NativeSporadic.B} (hs : orderOf s = 3) (hd : BabyInv 0 d)
    (hinv : d * s * d⁻¹ = s⁻¹) :
    ShapeRkAt' 3 IsFi22 (fun (T : Type) [Group T] => True) s := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨v, w, hw, hvw⟩ := tabBThree_typeThree_of_inverted hs hd hinv
  have hQ := (native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.2.2.2
  have hcard : Nat.card (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) ≤
      3 * Nat.card (vStab v ⊓ vStab w : Subgroup Shat) := by
    rw [hQ, ← hvw, tabBThree_card_centralizer_babyToShat]
    exact (hA s hs ⟨d, hd, hinv⟩).trans (by norm_num)
  have hS := shapeRkAt_fi22_typeThree hBr hw hcard
  have h : ShapeRkAt 3 IsFi22 (fun (T : Type) [Group T] => True)
      (babyToShat.symm (clabelS v * clabelS w)) := by
    with_reducible_and_instances
      exact ShapeRkAt.of_equiv Nat.prime_three (fun _ _ _ _ e h => IsFi22.of_equiv e h)
        (fun _ _ _ _ _ h => h) babyToShat.symm hS
  rw [← hvw, MulEquiv.symm_apply_apply] at h
  exact h.toWeak Nat.prime_three

end Inverted

end CensusB3

section NoComp


theorem census_B_three_of_noComp (h : TabBThreeBNoComp) :
    PCompCensus 3 (NativeSporadic.Carrier .B) (· = .sporadic .Fi22) := by
  show PCompCensus 3 NativeSporadic.B (· = .sporadic .Fi22)
  intro x hx J hJ
  by_cases hinv : ∃ d : NativeSporadic.B, BabyInv 0 d ∧ d * x * d⁻¹ = x⁻¹
  · obtain ⟨d, hd, hdx⟩ := hinv
    rcases CensusB3.shapeRkAt'_fi22_of_inverted CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
        tabBThreeACard_thm hx hd hdx with hno | ⟨J', hJ', hu, hG, -⟩
    · exact absurd hJ (hno J)
    · rw [hu J hJ]
      exact ⟨.sporadic .Fi22, rfl, hG⟩
  · exact absurd hJ (h x hx (fun d hd hdx => hinv ⟨d, hd, hdx⟩) J)

end NoComp

section KGroup


theorem census_B_three
    (hK : CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) :
    PCompCensus 3 (NativeSporadic.Carrier .B) (· = .sporadic .Fi22) :=
  census_B_three_of_noComp (tabBThreeBNoComp_of_kGroup
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll
    (sporadicMultipliers_of_census
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group hK)

end KGroup

end CFSG.HardMathSupport.Dickson.BMRows
