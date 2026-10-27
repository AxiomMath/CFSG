module

public import CFSG.ClassicalInvolution.Q3.Q3WATwinD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TS

open scoped MatrixGroups
open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Universal.Spin CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups
  FundamentalSingleClass IsLongestRoot modelUniv)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem exists_theta_sl4_plusDatum3 :
    ∃ Θ : SL(4, GaloisField 3 1) →* spinGroup (quadPlus 5 (GaloisField 3 1)),
      Θ.ker ≤ Subgroup.center _ ∧
      (∀ k : Fin 3, (rankOne (SpecialLinear.rootGroup 3 (GaloisField 3 1)) k).map Θ =
        rankOne (plusDatum 5 (GaloisField 3 1) (by omega)).rootGroup (nodeA3 k)) ∧
      Θ.range = ⨆ k : Fin 3, rankOne (plusDatum 5 (GaloisField 3 1) (by omega)).rootGroup
        (nodeA3 k) := by
  set F := GaloisField 3 1 with hFdef
  have hn3 : 3 ≤ 5 := by omega
  set L : Fin 3 → Subgroup (spinGroup (quadPlus 5 F)) := fun k =>
    rankOne (plusDatum 5 F hn3).rootGroup (nodeA3 k) with hL
  have h34 : cartanD 5 (3 : Fin 5) 4 = 0 := by
    refine (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD ?_ ?_ ?_).1 <;> decide
  obtain ⟨Θ, hker, hrange, hblk⟩ := exists_psi_of_chain3 (K := F) card_gf3 (m := 1) (by norm_num)
    (G := spinGroup (quadPlus 5 F)) (U := L)
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exact commutes_rankOne_plusDatum hn3 h34)
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      · have hedge : edgeD 5 (2 : Fin 5) 3 := by unfold edgeD; decide
        obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hn3 hedge
        exact ⟨W, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW⟩
      · have hedge : edgeD 5 (2 : Fin 5) 4 := by unfold edgeD; decide
        exact standardPair_plusDatum_edge (F := F) hn3 hedge)
  refine ⟨Θ, hker, fun k => ?_, hrange⟩
  rw [WeakCT.rankOne_eq_range (K := F) (n := 3) k]
  exact hblk k

section Model


theorem nonempty_extModel3U_D5
    (hscT : FundamentalSingleClass .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by omega)))
    (hscY : FundamentalSingleClass .PSL (SpecialLinear.rootDatum 3 (GaloisField 3 1)))
    (hlong : ∀ k : Fin 3,
      IsLongestRoot (SpecialLinear.rootDatum 3 (GaloisField 3 1)) (Pi.single k 1)) :
    Nonempty (ExtModel3U .POmegaPlus .PSL
      ⟨spinGroup (quadPlus 5 (GaloisField 3 1)), plusDatum 5 (GaloisField 3 1) (by omega)⟩
      ⟨SL(4, GaloisField 3 1), SpecialLinear.rootDatum 3 (GaloisField 3 1)⟩ 2) := by
  have hn3 : 3 ≤ 5 := by omega
  set F := GaloisField 3 1 with hFdef
  obtain ⟨Θ, hker, hnode, hrange⟩ := exists_theta_sl4_plusDatum3
  set DT := plusDatum 5 F hn3 with hDT
  set DY := SpecialLinear.rootDatum 3 F with hDY
  set X : Subgroup (spinGroup (quadPlus 5 F)) :=
    ⨆ k : Fin 3, rankOne DT.rootGroup (nodeA3 k) with hX
  have hcommX0 : ∀ k : Fin 3,
      Commutes (rankOne DT.rootGroup (0 : Fin 5)) (rankOne DT.rootGroup (nodeA3 k)) := by
    intro k
    refine commutes_rankOne_plusDatum hn3 ?_
    refine (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD ?_ ?_ ?_).1
    · fin_cases k <;> decide
    · fin_cases k <;> decide
    · fin_cases k <;> decide
  have hcommXθ : Commutes X (rootθD 5 F hn3) := by
    refine commutes_iSup_left.mpr fun k => ?_
    exact (commutes_rootθD_rankOne hn3 (by omega) (k := nodeA3 k)
      (by fin_cases k <;> decide)).symm
  have hcommX0' : Commutes X (rankOne DT.rootGroup (0 : Fin 5)) :=
    commutes_iSup_left.mpr fun k => (hcommX0 k).symm
  have himg : ∀ R ∈ fundamentalSubgroups .PSL DY, ∃ g : SL(4, F),
      R.map Θ = conjSub (Θ g) (rankOne DT.rootGroup (nodeA3 0)) := by
    intro R hR
    obtain ⟨g, hg⟩ := hscY (rankOne DY.rootGroup (0 : Fin 3))
      (rankOne_mem_fundamental DY (hlong 0)) R hR
    refine ⟨g, ?_⟩
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map]
    exact congrArg _ (hnode 0)
  have h01 : edgeD 5 (0 : Fin 5) (1 : Fin 5) := by unfold edgeD; decide
  obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hn3 h01
  have hRY : rankOne DY.rootGroup (0 : Fin 3) = (WeakCT.blockSL2 F 3 0).range :=
    WeakCT.rankOne_eq_range (K := F) (n := 3) 0
  refine ⟨{
    Rθ := rootθD 5 F hn3
    twin := fun _ => rankOne DT.rootGroup (0 : Fin 5)
    Θ := Θ
    Rθ_mem := rootθD_mem_fundamentalSubgroups hn3 (by omega)
    twin_mem := fun _ => rankOne_mem_fundamentalSubgroups_plusDatum hn3 _
    Θ_ker := hker
    Θ_mem := ?_
    Θ_comm := ?_
    twin_comm := ?_
    twin_comm_Θ := ?_
    twin_inj := fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega)
    pow_T := pow3_of_mem_fundamental hscT
      (rankOne_mem_fundamentalSubgroups_plusDatum hn3 (0 : Fin 5)) (pow3_of_stdPair card_gf3 hW).1
    pow_Y := pow3_of_mem_fundamental hscY (rankOne_mem_fundamental DY (hlong 0))
      (by rw [hRY]; exact pow3_range_sl2 card_gf3 _)
    cop_T := fun z hz => ?_
    cop_Y := fun z hz => orderOf_not_dvd_three_of_center card_gf3 (by norm_num : 1 ≤ 4) hz }⟩
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    exact conjSub_mem_fundamentalSubgroups (rankOne_mem_fundamentalSubgroups_plusDatum hn3 _) _
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 : conjSub (Θ g) (rootθD 5 F hn3) = rootθD 5 F hn3 :=
      CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommXθ
    have h2 : Commutes (rankOne DT.rootGroup (nodeA3 0)) (rootθD 5 F hn3) :=
      (commutes_rootθD_rankOne hn3 (by omega) (k := nodeA3 0) (by decide)).symm
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2
    rwa [h1] at h3
  · intro i
    exact (commutes_rootθD_rankOne hn3 (by omega) (k := (0 : Fin 5)) (by decide)).symm
  · intro i R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommX0'
    have h2 := hcommX0 0
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2
    rwa [h1] at h3
  · have h4 := pow_four_of_mem_center_spinPlus hn3 hz
    intro h3
    exact absurd (h3.trans (orderOf_dvd_of_pow_eq_one h4)) (by norm_num)

theorem nonempty_extModel3_D5 : Nonempty (ExtModel3 .POmegaPlus 5 .PSL 4 2) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ 5 := by omega
  have hadmT : StatedLieAdmissible .POmegaPlus 5 3 1 := ⟨hp, le_rfl, by show 4 ≤ 5; omega⟩
  have hadmY : StatedLieAdmissible .PSL 4 3 1 :=
    ⟨hp, le_rfl, by show 2 ≤ 4; omega, fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have e1 := modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3
  have e2 : modelUniv .PSL 4 3 1 hp =
      ⟨SL(4, GaloisField 3 1), SpecialLinear.rootDatum 3 (GaloisField 3 1)⟩ :=
    modelUniv_PSL_eq (m := 3)
  have hscT : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 5 3 1 hp).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus 5 3 1 hp trivial
      hadmT (by decide) (by decide)
  have hscY : FundamentalSingleClass .PSL (modelUniv .PSL 4 3 1 hp).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .PSL 4 3 1 hp trivial hadmY
      (by decide) (by decide)
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum 5 (GaloisField 3 1) hn3) := by
    revert hscT
    rw [e1]
    exact id
  have hscY' : FundamentalSingleClass .PSL (SpecialLinear.rootDatum 3 (GaloisField 3 1)) := by
    revert hscY
    rw [e2]
    exact id
  have hlong : ∀ k : Fin 3,
      IsLongestRoot (SpecialLinear.rootDatum 3 (GaloisField 3 1)) (Pi.single k 1) := by
    have h := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .PSL 4 3 1 hp trivial hadmY
    exact fun k => h k trivial
  show Nonempty (ExtModel3U .POmegaPlus .PSL (modelUniv .POmegaPlus 5 3 1 hp)
    (modelUniv .PSL 4 3 1 hp) 2)
  rw [e1, e2]
  exact nonempty_extModel3U_D5 hscT' hscY' hlong

end Model

end CFSG.ClassicalInvolution.Q3.Q3TS
