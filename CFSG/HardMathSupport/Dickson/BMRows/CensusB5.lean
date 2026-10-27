module

public import CFSG.HardMathSupport.Dickson.BMRows.Defs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveNoCompK
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.B.Pinned CFSG.RankThree.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Dickson.I271 CFSG.Yardstones.Md0ec50421ce4

namespace CensusB5

@[expose] def IsHS (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .HS).Group)

theorem IsHS.of_equiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T') (h : IsHS T) :
    IsHS T' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

section HSShape


theorem shapeRkAt'_isHS_five {Q : Type} [Group Q] [Finite Q] {t : Q} (ht5 : orderOf t = 5)
    (hO : GLAPPrimeCoreOf 5 (Subgroup.centralizer ({t} : Set Q)) = ⊥)
    {E : Subgroup Q} (hEC : E ≤ Subgroup.centralizer ({t} : Set Q))
    (eE : ↥E ≃* NativeSporadic.HS)
    (hC : Nat.card ↥(Subgroup.centralizer ({t} : Set Q)) < 665280000) :
    ShapeRkAt' 5 IsHS (fun (T : Type) [Group T] => True) t := by
  have hsimple : IsSimpleGroup NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  haveI : IsSimpleGroup ↥E := @MulEquiv.isSimpleGroup _ _ NativeSporadic.HS _ hsimple eE
  have hcard : Nat.card ↥E = 44352000 := by
    rw [Nat.card_congr eE.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  have hnab : ∃ a b : ↥E, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    letI : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := ↥E)
    rw [hcard] at hp
    norm_num at hp
  have hZ : Subgroup.center ↥E = ⊥ := center_eq_bot_of_simple_nonab hnab
  have h5 : 5 ∣ Nat.card ↥E := by rw [hcard]; norm_num
  have hcore : GLAPPrimeCore 5 ↥E = ⊥ := glaPPrimeCore_eq_bot_of_simple Nat.prime_five h5
  have hnd : ∀ n ≤ 14, ¬ Nat.card ↥E ∣ n.factorial := by
    intro n hn
    rw [hcard]
    interval_cases n <;> norm_num [Nat.factorial]
  have hC' : Nat.card ↥(Subgroup.centralizer ({t} : Set Q)) < 15 * Nat.card ↥E := by
    rw [hcard]
    omega
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .HS ≃* (TauCeti.CFSGIndex.sporadic .HS).Group := b
  have hG : IsHS (PSimple 5 E) := ⟨(pSimpleEquivSelf E hcore hZ).trans (eE.trans b₀)⟩
  exact shapeRkAt'_of_simple_small_index_five ht5 hO E hEC inferInstance hnab h5 hnd hC' hG trivial

end HSShape

end CensusB5

section NoComp


theorem census_B_five_of_noComp
    (h : TabBFiveBNoComp) :
    PCompCensus 5 (NativeSporadic.Carrier .B) (· = .sporadic .HS) := by
  show PCompCensus 5 NativeSporadic.B (· = .sporadic .HS)
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨E, hEC, ⟨eE⟩⟩ := tabBFiveAHS_of_cert
  have hD : CentShapeRk' 5 CensusB5.IsHS (fun (T : Type) [Group T] => True)
      NativeSporadic.B :=
    centShapeRk'_of_two_classes (fun _ _ _ _ e h => CensusB5.IsHS.of_equiv e h)
      (fun _ _ _ _ _ h => h) bFiveRel.orderOf_z orderOf_sFiveA tabBFive_hconj (Or.inl h)
      (CensusB5.shapeRkAt'_isHS_five orderOf_sFiveA gLAPPrimeCoreOf_centralizer_sFiveA_eq_bot hEC
        eE TabBFiveCent.tabBFiveACard_holds)
  intro x hx J hJ
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hx5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  rcases hD x hx1 hx5 with hno | ⟨J', hJ', hu, hG, -⟩
  · exact absurd hJ (hno J)
  · rw [hu J hJ]
    exact ⟨.sporadic .HS, rfl, hG⟩

end NoComp

section KGroup


theorem census_B_five
    (hK : CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) :
    PCompCensus 5 (NativeSporadic.Carrier .B) (· = .sporadic .HS) :=
  census_B_five_of_noComp (tabBFiveBNoComp_of_kGroup
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (sporadicMultipliers_of_census
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds) hK)

end KGroup

end CFSG.HardMathSupport.Dickson.BMRows
