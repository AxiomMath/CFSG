module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBMFi24Inv

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4

section Th


theorem tabMThree_shapeRkAt'_of_th (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) {G : Type} [Group G] [Finite G] {k α : G} (hk : orderOf k = 3)
    (hα : α * k * α⁻¹ = k⁻¹) {H : Subgroup G}
    (hHα : H ≤ Subgroup.centralizer ({α} : Set G)) (hHk : H ≤ Subgroup.centralizer ({k} : Set G))
    (e : ↥H ≃* NativeSporadic.Th)
    (hbound : Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 3 * 90745943887872000) :
    ShapeRkAt' 3 (GoodSpor 3 [.Fi24Prime, .Th]) (RkSpor 3 [.Fi24Prime, .Th]) k := by
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
  have hZ : Subgroup.center ↥H = ⊥ := by
    haveI := hs
    exact center_eq_bot_of_simple_nonab hnab
  have hq : CFSG.Open.IsQuasisimple ↥H := by
    haveI := hs
    exact tabMFive_quasisimple_of_simple_nonab hnab
  have eTh : ↥H ≃* (TauCeti.CFSGIndex.sporadic .Th).Group := e.trans (hBr .Th).some
  have eQ : ↥H ⧸ Subgroup.center ↥H ≃* (TauCeti.CFSGIndex.sporadic .Th).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eTh
  refine tabMFive_shapeRkAt'_of_inverted Nat.prime_three (by norm_num)
    (fun T T' _ _ f h => GoodSpor.of_equiv f h) (fun T T' _ _ f h => RkSpor.of_equiv f h)
    hk hα hHα hHk hs hnab (by rw [hcard]; norm_num) (by rw [hcard]; exact hbound) ?_
    (rkSpor_M_three_of_quasisimple hOut hSpM hBr hq (Or.inr ⟨eQ⟩))
  exact Or.inr (Or.inr ⟨.Th, by simp, ⟨eTh⟩⟩)

end Th

section Cover


theorem tabMThree_shapeRkAt'_of_cover (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) {G : Type} [Group G] [Finite G] {k : G} (hk : orderOf k = 3)
    (hq : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({k} : Set G)))
    (e : ↥(Subgroup.centralizer ({k} : Set G)) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({k} : Set G)) ≃* NativeSporadic.Fi24prime) :
    ShapeRkAt' 3 (GoodSpor 3 [.Fi24Prime, .Th]) (RkSpor 3 [.Fi24Prime, .Th]) k := by
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
  have hJ : GLAPComponent 3 C C := glaPComponent_of_normal_quasisimple le_rfl hLn hq hcore
  have eP : PSimple 3 C ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    (pSimpleEquivCenterQuot C hcore).trans eS
  have hG : GoodSpor 3 [.Fi24Prime, .Th] (PSimple 3 C) :=
    Or.inr (Or.inr ⟨.Fi24Prime, by simp, ⟨eP⟩⟩)
  have hR : RkSpor 3 [.Fi24Prime, .Th] (PQuot 3 C) :=
    rkSpor_M_three_pQuot hOut hSpM hBr hJ (Or.inl ⟨eP⟩)
  exact (shapeRkAt_of_normal_quasisimple Nat.prime_three le_rfl hLn hq hpL hcent hG hR).toWeak
    Nat.prime_three

end Cover

end CFSG.HardMathSupport.Dickson.I271
