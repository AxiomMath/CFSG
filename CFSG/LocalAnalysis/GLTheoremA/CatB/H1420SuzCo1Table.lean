module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowCent
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzCo1Centre
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeMoore
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Five
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHe3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZCo1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14ChevFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows1
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7
public import Certificates.Data.TabCo1ThreeE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Schreier.NormalThree
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot
  CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabCo1
  CFSG.LieType.Multipliers.U43

local notation "RkCo1" =>
  fun (T : Type) [Group T] => Nat.card (Subgroup.center T) = 9 ∨
    Nat.card T ≠ Nat.card (Subgroup.center T) * 3265920

private theorem co1CentRk_of_equiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : RkCo1 T) : RkCo1 T' := by
  have h1 : Nat.card T' = Nat.card T := (Nat.card_congr e.toEquiv).symm
  have h2 : Nat.card (Subgroup.center T') = Nat.card (Subgroup.center T) :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
  show Nat.card (Subgroup.center T') = 9 ∨ Nat.card T' ≠ Nat.card (Subgroup.center T') * 3265920
  rw [h1, h2]
  exact h

private theorem rkCo1_alt9 {G : Type} [Group G] {L : Subgroup G} (hs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hcardL : Nat.card ↥L = 181440) : RkCo1 ↥L := by
  haveI := hs
  refine Or.inr ?_
  rw [center_eq_bot_of_simple_nonab hnab, Subgroup.card_bot, hcardL]
  norm_num

private theorem rkCo1_suz3 {G : Type} [Group G] {J : Subgroup G}
    (hcard3 : Nat.card ↥(Subgroup.center ↥J) = 3)
    (hqcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = 448345497600) : RkCo1 ↥J := by
  refine Or.inr ?_
  have hJc : Nat.card ↥J = 448345497600 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J), hqcard, hcard3]
  rw [hJc, hcard3]
  norm_num

private theorem hGoodTrue : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True :=
  fun _ _ _ _ _ h => h

private theorem hRkCo1 : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' →
    RkCo1 T → RkCo1 T' := fun _ _ _ _ e h => co1CentRk_of_equiv e h


private theorem shapeRkAt_threeB (x : ↥GA) (hx : MRep (rootRows3B ()) (x : GL24)) :
    ShapeRkAt 3 (fun _ _ => True) RkCo1 x := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨J, hJC, hJn, hq, hp3, hZ3, hcent, -, hc9⟩ := suzCo1_threeB_data hx
  exact shapeRkAt_of_subgroup_data_quasi Nat.prime_three hGoodTrue hRkCo1 GA x J hJC hJn hq hp3
    hZ3 hcent trivial (Or.inl hc9)

private theorem shapeRkAt_threeD (x : ↥GA) (hx : MRep (rootRows3D ()) (x : GL24)) :
    ShapeRkAt 3 (fun _ _ => True) RkCo1 x := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨hx1, hx3, hxy, hM, hy1⟩ := moore_data (x := (x : GL24)) hx
  have hpres := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 9)
    (by norm_num) mooreM hM).2.2.2.2.2 (by norm_num) ⟨1, ⟨le_rfl, by norm_num⟩, hy1⟩
  obtain ⟨-, ⟨e⟩⟩ := hpres
  set L : Subgroup GL24 := Subgroup.closure (mooreM '' Set.Icc 1 (9 - 2)) with hL
  have hLC : L ≤ Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, ⟨hj1, hj7⟩, rfl⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (hxy j hj1 (by omega)).symm, mooreM_mem j⟩
  obtain ⟨hs, hnab, hcardL⟩ := alt9_subgroup_data e
  have hbound : Nat.card ↥(Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA) ≤
      3 * Nat.card ↥L := by
    rw [← card_centralizer_GA_eq_inf GA x, hcardL]
    exact TabCo1ThreeDRoot.card_cent_threeD_root_le x hx
  exact shapeRkAt_of_bound Nat.prime_three hGoodTrue hRkCo1 GA x L hLC hs hnab
    (by rw [hcardL]; norm_num) hx1 hx3 hbound trivial (rkCo1_alt9 hs hnab hcardL)

private theorem shapeRkAt_threeA
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group))
    (x : ↥GA) (hx : MRep (mul (mul (aRows 1) (aRows 4)) (aRows 5)) (x : GL24)) :
    ShapeRkAt 3 (fun _ _ => True) RkCo1 x := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨J, hJC, hJn, hq, hp3, hcard3, hcent, hqcard, -⟩ := threeA_data hb hx
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥J) :=
    IsPGroup.of_card (n := 1) (by rw [hcard3]; norm_num)
  exact shapeRkAt_of_subgroup_data_quasi Nat.prime_three hGoodTrue hRkCo1 GA x J hJC hJn hq hp3
    hZp hcent trivial (rkCo1_suz3 hcard3 hqcard)

theorem suzCo1_centShapeRk_three
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group)) :
    CentShapeRk 3 (fun _ _ => True) RkCo1 ↥GA := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro k hk1 hk3
  obtain ⟨g, x, hx, hcases⟩ := tabCo1_census_three k (orderOf_eq_prime hk3 hk1)
  have hshape : ShapeRkAt 3 (fun _ _ => True) RkCo1 x := by
    rcases hcases with h | h | h | h
    · exact Or.inl (tabCo1_threeC x h)
    · exact shapeRkAt_threeB x h
    · exact shapeRkAt_threeD x h
    · exact shapeRkAt_threeA hb x h
  rw [hx]
  exact @shapeRkAt_conj ↥GA (Subgroup.toGroup GA) inferInstance 3 Nat.prime_three _ _ hGoodTrue
    hRkCo1 x hshape g

theorem centRow_co1 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    CentRow .Co1 fun (T : Type) [Group T] =>
      Nat.card (Subgroup.center T) = 9 ∨ Nat.card T ≠ Nat.card (Subgroup.center T) * 3265920 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  exact @centRow_of_centShapeRk .Co1 ↥GA _ hfin hs hOut b hnc _ _ hGoodTrue hRkCo1
    (suzCo1_centShapeRk_three (hbr .Suz))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
