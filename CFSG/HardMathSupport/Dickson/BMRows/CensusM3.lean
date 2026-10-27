module

public import CFSG.HardMathSupport.Dickson.BMRows.CensusShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAMain
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeAGlue
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeCMain
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.MonsterThreeBRank
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.MonsterThreeBPair
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterRank
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271

section Th


theorem census_M_three_shape_of_th (hBr : SporadicBridges) {G : Type} [Group G] [Finite G]
    {k α : G} (hk : orderOf k = 3) (hα : α * k * α⁻¹ = k⁻¹) {H : Subgroup G}
    (hHα : H ≤ Subgroup.centralizer ({α} : Set G)) (hHk : H ≤ Subgroup.centralizer ({k} : Set G))
    (e : ↥H ≃* NativeSporadic.Th)
    (hbound : Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 3 * 90745943887872000) :
    ShapeRkAt' 3 (fun T _ => catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
      (fun _ _ => True) k := by
  have hcard : Nat.card ↥H = 90745943887872000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.PartOne.CTP.card_Th
  have hs : IsSimpleGroup ↥H :=
    @MulEquiv.isSimpleGroup ↥H _ NativeSporadic.Th Units.instGroup
      (CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th
        CFSG.Sporadic.Th.th_kernel_facts) e
  have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    letI : CommGroup ↥H := { (inferInstance : Group ↥H) with mul_comm := hcon }
    have hpr := IsSimpleGroup.prime_card (α := ↥H)
    rw [hcard] at hpr
    norm_num at hpr
  exact tabMFive_shapeRkAt'_of_inverted
    (Good := fun T _ => catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
    (Rk := fun _ _ => True) Nat.prime_three (by norm_num) catalogIs_of_mulEquiv
    (fun _ _ _ _ _ h => h) hk hα hHα hHk hs hnab (by rw [hcard]; norm_num)
    (by rw [hcard]; exact hbound) ⟨.sporadic .Th, Or.inr rfl, ⟨e.trans (hBr .Th).some⟩⟩ trivial

end Th

section Cover


theorem census_M_three_shape_of_cover
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) {G : Type} [Group G] [Finite G] {k : G} (hk : orderOf k = 3)
    (hq : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({k} : Set G)))
    (e : ↥(Subgroup.centralizer ({k} : Set G)) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({k} : Set G)) ≃* NativeSporadic.Fi24prime) :
    ShapeRkAt' 3 (fun T _ => catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
      (fun _ _ => True) k := by
  set C : Subgroup G := Subgroup.centralizer ({k} : Set G) with hCdef
  have hkC : k ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have eS : ↥C ⧸ Subgroup.center ↥C ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    e.trans (hBr .Fi24Prime).some
  have hZ : Nat.card ↥(Subgroup.center ↥C) ∣ 3 :=
    card_center_dvd_multiplier hSpM hq .Fi24Prime eS
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥C) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card ↥(Subgroup.center ↥C) = 3 ^ n := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.of_card hn
  have hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (C : Set G)) := by
    intro g
    have hgc : (⟨(g : G), g.2.1⟩ : ↥C) ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 g.2.2 (b : G) b.2)
    obtain ⟨m, hm⟩ := hZp ⟨_, hgc⟩
    refine ⟨m, Subtype.ext ?_⟩
    have := congrArg (fun x : ↥(Subgroup.center ↥C) => ((x : ↥C) : G)) hm
    simpa using this
  have hLn : ∀ g ∈ C, ∀ l ∈ C, g * l * g⁻¹ ∈ C := fun g hg l hl =>
    C.mul_mem (C.mul_mem hg hl) (C.inv_mem hg)
  have hpL : 3 ∣ Nat.card ↥C := by
    have := Subgroup.orderOf_dvd_natCard C hkC
    rwa [hk] at this
  have hcore : GLAPPrimeCore 3 ↥C = ⊥ :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three le_rfl hLn hq hpL hcent
  have eP : PSimple 3 C ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    (pSimpleEquivCenterQuot C hcore).trans eS
  exact (shapeRkAt_of_normal_quasisimple
    (Good := fun T _ => catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
    (Rk := fun _ _ => True) Nat.prime_three le_rfl hLn hq hpL hcent
    ⟨.sporadic .Fi24Prime, Or.inl rfl, ⟨eP⟩⟩ trivial).toWeak Nat.prime_three

end Cover

section Generic


theorem census_M_three_centShape {G : Type} [Group G] (hE : MonsterExistenceStatement G)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hA : CentThreeA G) (hB : CentThreeBNoComp G) (hC : CentThreeC G) :
    CentShapeRk' 3 (fun T _ => catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th))
      (fun _ _ => True) G := by
  haveI : Finite G := (twoA_data_of_existence hE).1
  intro k hk1 hk3
  have hk : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  by_cases hinv : InvertedByTwoA k
  · obtain ⟨α, hα2, hαc, hαk, i, hi, hsh⟩ :=
      invertedByTwoA_data_twoA hE Nat.prime_three (by norm_num) hk hinv
    have hi34 : i = 3 ∨ i = 4 := by
      clear hsh
      revert i
      decide
    rcases hi34 with rfl | rfl
    · obtain ⟨hq, ⟨e⟩⟩ := hA k α hk hα2 hαc hαk hsh
      exact census_M_three_shape_of_cover hSpM hBr hk hq e
    · obtain ⟨e⟩ := hsh
      exact census_M_three_shape_of_th hBr hk hαk inf_le_left inf_le_right e
        (hC k α hk hα2 hαc hαk ⟨e⟩)
  · exact Or.inl fun J hJ => hB k hk hinv J hJ

end Generic

section Census


theorem census_M_three_of_noComp (h : M3ResBNoComp) :
    PCompCensus 3 (NativeSporadic.Carrier .M)
      (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : MGriess ≃* NativeSporadic.Carrier .M := e₀
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := (twoA_data_of_existence hE).1
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv MGriess e.toEquiv
  have hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers :=
    sporadicMultipliers_of_census
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have hBr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  exact pCompCensus_of_centShapeRk' Nat.prime_three (CentShapeRk'.of_equiv Nat.prime_three
    catalogIs_of_mulEquiv (fun _ _ _ _ _ h => h) e
    (census_M_three_centShape hE hSpM hBr (CentThreeA.of_equiv e (centThreeA_M tabBThreeACard_thm))
      (CentThreeBNoComp.of_equiv e (centThreeBNoComp_M_of_m3ResBNoComp h))
      (CentThreeC.of_equiv e centThreeC_M)))

end Census

section KGroup


theorem census_M_three (hK : CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) :
    PCompCensus 3 (NativeSporadic.Carrier .M)
      (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th) := by
  have hB3 : OPrimeCoreTrivialAt 3 NativeSporadic.B := BThreeFi23.oPrimeCoreTrivialAt_B_three
  have hM3 : OPrimeCoreTrivialAt 3 CFSG.Monster.Generated.Gmat :=
    oPrimeCoreTrivialAt_gmat_of_uninverted Nat.prime_three (by norm_num)
      (uninvertedOPrimeTrivial_gmat_of_twoAPureKlein Nat.prime_three (by norm_num) hB3
        ThreeBNF.twoAPureKlein_three_Gmat)
  exact census_M_three_of_noComp
    (MonsterThreeBRank.m3ResBNoComp_of_rank_of_certificates
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
      CFSG.HardMathSupport.Timmesfeld.DefChar.lieOuterRank_proved
      (isKGroup_gmat_of_carrier hK) hM3)

end KGroup

end CFSG.HardMathSupport.Dickson.BMRows
