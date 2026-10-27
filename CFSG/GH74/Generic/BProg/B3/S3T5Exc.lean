module

public import CFSG.GH74.Generic.BProg.B3.S3T5ExcG2
public import CFSG.GH74.Generic.S3.LyB2Closure
public import CFSG.GH74.Generic.S3.LyB2Term
public import CFSG.GH74.GLS.TwoThin.G.Final
public import CFSG.GH74.KGroups.TwoM12Vertical
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.GH74.E2.FactsK

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5X

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.S3 (G2Table IsExcB2 closure_exc)

theorem twoThinU33Centralizers_local : TwoThinU33Centralizers := by
  intro K _ _ hK hc z hz
  obtain ⟨e⟩ := KGroups.U33.equiv_of_lieModel hK
  refine KGroups.U33.fixed_solvable e (MulAut.conj z) ?_ ?_ _ fun x hx => ?_
  · rw [← map_pow, show z ^ 2 = 1 from hz ▸ pow_orderOf_eq_one z, map_one]
  · intro h
    have hzc : z ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := DFunLike.congr_fun h g
      rw [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * z = z * g * z⁻¹ * z := by rw [hg]
        _ = z * g := by group
    rw [hc, Subgroup.mem_bot] at hzc
    rw [hzc, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · rw [Subgroup.mem_centralizer_iff] at hx
    rw [MulAut.conj_apply, hx z (Set.mem_singleton z), mul_inv_cancel_right]

theorem twoThinKGroupFactQ_gen4Cen
    : TwoThinKGroupFactQ Gen4Cen :=
  twoThinKGroupFactQ_of_coreP (fun _ _ _ hH L => gen4Comp_of_gen4Cen hH L)
    (twoThinKGroupCoreGC_of_tables
      (genericKnownFacts_of_griess
        CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
      E2.e2ComponentFacts twoThinU33Centralizers_local KGroups.TwoM12.twoThinC2VerticalG_2M12)

theorem false_of_excB2Pair
    {G : Type} [Group G] [Finite G] (hyp : Hyp2 G) {x : G}
    {K : Subgroup G} (hc : IsJ2Circ x K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) {t : G}
    {J : Subgroup G} (hJ : IsILo 2 t J) (hExc : IsExcB2 (kBar J)) : False := by
  have hKP : IsKProperSimple G := ⟨hyp.simple, hyp.nonab, CFSG.GH74.kProper_of_kgh hyp.kgh⟩
  have hF : GenericKnownFacts := genericKnownFacts_of_griess
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have h3G : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact hyp.rank
  have hR : ∀ z : G, orderOf z = 2 → 3 ≤ pRank 2 ↥(centralizer ({z} : Set G)) :=
    fun z hz => rankThreeCentralizers G hyp.simple hyp.nonab h3G z hz
  have hG2 : G2Table G := g2Table_of_depth hF hyp.simple hyp.nonab hyp.gen4 hyp.kgh
    (fun u hu L hL hL2 => seven_le_d2 hyp.simple hyp.nonab h3G hc h3 u hu L hL hL2)
  have hclosed : ClsClosed (G := G)
      (fun _ K' => ¬ HasSL2Model (↥K' ⧸ pPrimeCore 2 ↥K') Odd) :=
    fun _ _ _ _ hP hcl hlt htype =>
      closure_exc hyp.gen4 hKP twoThinKGroupFactQ_gen4Cen hG2 hP hcl hlt htype
  exact hyp.noThin (hasTwoThinConfiguration_of_cls _ hR hclosed ⟨t, J, ⟨hJ, hExc.1⟩, hExc.2⟩)

end S3T5X

end CFSG.GH74.Generic.BProg.B3
