module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Co13Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Co13ThreeB
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporCo15
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Three
public import Certificates.Certificate10146

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co13

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native
  Timmesfeld.Co1Leaf CFSG.HardMathSupport.Dickson.I271.TabCo1

section EQ


theorem card_T : Nat.card eSplit.T = 729 := by
  rw [SplitData.T, MonoidHom.range_eq_map, Subgroup.card_map_of_injective eSplit.φ_injective,
    Subgroup.card_top, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.card_vec, aGA_length]
  norm_num

theorem le_T {A : Subgroup ↥GA}
    (hAQ : A ≤ Qg) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h729 : Nat.card eSplit.T ≤ Nat.card A) : A ≤ eSplit.T := by
  rw [card_T] at h729
  rw [eSplit.T_eq_closure]
  exact Certificates.certificate10146.1 A hAQ hA h729

end EQ

section Comp


theorem comps_threeB (xA : ↥GA) (hx : MRep (CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.rootRows3B ())
    (xA : GL24)) :
    ∃ zA : ↥GA, (zA : GL24) = kG CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext 91 ∧
      Nat.card ↥(Subgroup.closure ({(xA : GL24), (zA : GL24)} : Set GL24)) = 9 ∧
      ∃ K : Subgroup ↥GA, GLAPComponent 3 (Subgroup.centralizer ({xA} : Set ↥GA)) K ∧
        GLAPComponent 3 (Subgroup.centralizer ({xA, zA} : Set ↥GA)) K := by
  have := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨-, hzG, hcard, J, hJGA, hJ1, hJ2, hJn, hq, h3⟩ := threeB_data_center hx
  refine ⟨⟨_, hzG⟩, rfl, hcard, J.subgroupOf GA, ?_, ?_⟩
  · refine Co15.glaPComponent_subgroupOf GA Nat.prime_three {xA} hJGA ?_ ?_ hq h3
    · intro l hl s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact Subgroup.mem_centralizer_singleton_iff.1 (hJ1 hl)
    · intro g hg hgs l hl
      exact hJn g (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
        (hgs xA rfl), hg⟩) l hl
  · refine Co15.glaPComponent_subgroupOf GA Nat.prime_three {xA, ⟨_, hzG⟩} hJGA ?_ ?_ hq h3
    · intro l hl s hs
      rcases hs with rfl | hs
      · exact Subgroup.mem_centralizer_singleton_iff.1 (hJ1 hl)
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Subgroup.mem_centralizer_singleton_iff.1 (hJ2 hl)
    · intro g hg hgs l hl
      exact hJn g (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
        (hgs xA (Set.mem_insert _ _)), hg⟩) l hl

end Comp

section Row


theorem plane_data :
    ∃ n zA : ↥GA, n⁻¹ * root 1 * n ∈ eSplit.T ∧ n⁻¹ * zA * n ∈ eSplit.T ∧
      Nat.card ↥(Subgroup.closure ({((root 1 : ↥GA) : GL24), (zA : GL24)} : Set GL24)) = 9 ∧
      ∃ K : Subgroup ↥GA, GLAPComponent 3 (Subgroup.centralizer ({root 1} : Set ↥GA)) K ∧
        GLAPComponent 3 (Subgroup.centralizer ({root 1, zA} : Set ↥GA)) K := by
  have hx : MRep (CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.rootRows3B ())
      ((root 1 : ↥GA) : GL24) := wordL_rep _
  obtain ⟨zA, hzA, hcard, K, hK1, hK2⟩ := comps_threeB (root 1) hx
  obtain ⟨n, hn1, hnz⟩ := Certificates.certificate10146.2
  have hz : zA = ⟨kG CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext 91, kG_mem _ 91⟩ :=
    Subtype.ext hzA
  rw [← eSplit.T_eq_closure, ← hz] at hnz
  rw [← eSplit.T_eq_closure] at hn1
  exact ⟨n, zA, hn1, hnz, hcard, K, hK1, hK2⟩

theorem card_Qg_full : Nat.card Qg = 3 ^ (Nat.card ↥GA).factorization 3 := by
  have h := factorization_card_GA
  rw [Subgroup.card_top] at h
  rw [card_Qg, h]

theorem kd264RowData_Co1_three : KD264RowData 3 ↥GA := by
  have := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨n, zA, hyT, hzT, hcard, K, hK1, hK2⟩ := plane_data
  rw [← Co15.card_closure_pair_subtype] at hcard
  exact Co15.kd264RowData_three_of_plane card_Qg_full eSplit.T_elemAbelian
    (fun A hAQ hA h => le_T hAQ hA h) n (root 1) zA hyT hzT hcard hK1 hK2

end Row

section RowCo1


set_option maxRecDepth 100000 in
theorem kd264SporAt_Co1_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KD264SporAt 3 .Co1 := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  have e : CFSG.Blueprint.NativeSporadic.Co1 ≃* ↥GA := CFSG.Sporadic.Co1Block.co1MatEquiv
  haveI : IsSimpleGroup ↥GA :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co1.isSimpleGroup_Co1 e.symm
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  have hp : ¬ (Nat.card ↥GA).Prime := by rw [card_GA_eq]; norm_num
  have hnc : ∃ x y : ↥GA, x * y ≠ y * x :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (S := ↥GA) hp
  have hb : ↥GA ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group := e.symm.trans b
  have hrd : KD264RowData 3 ↥GA := kd264RowData_Co1_three
  refine kd264SporAt_of_model (p := 3) (s := .Co1) (Q := ↥GA) hOut Nat.prime_three (by decide) ?_
    ?_ ?_
  · exact hnc
  · exact hb
  · intro _ _ _
    exact hrd

end RowCo1

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co13

end
