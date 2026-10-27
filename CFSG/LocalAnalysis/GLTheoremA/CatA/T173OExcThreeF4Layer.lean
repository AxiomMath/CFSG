module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeCommutator
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitLayer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OConj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
open CFSG.LieType.Steinberg (Sp.x)
open CFSG.RankThree.CentralCover (sl2Upper coe_sl2Upper sl2Upper_add sl2Upper_zero)
open scoped commutatorElement MatrixGroups

local instance f4NeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

private noncomputable abbrev f4WR : WeylGroup .F4 :=
  simple .F4 0 * simple .F4 1 * simple .F4 2 * simple .F4 3 * simple .F4 1 * simple .F4 2 *
    simple .F4 0

private theorem f4WR_smul_single_one : f4WR • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = rootR := by
  simp only [f4WR, mul_smul, simple_smul]
  decide


variable {F : Type} [Field F] [Finite F]

private theorem map_conj_canonicalRep_rootPair_one :
    (rootSubgroup .F4 F (Pi.single 1 1) ⊔ rootSubgroup .F4 F (-Pi.single 1 1)).map
        (MulAut.conj (canonicalRep (coxeterSystem .F4) F f4WR)).toMonoidHom = rootSL2R F := by
  rw [Subgroup.map_sup, (canonical_weyl_root_transport .F4 F).2.1 f4WR _ (IsRoot.basis 1),
    (canonical_weyl_root_transport .F4 F).2.1 f4WR _ (IsRoot.neg (IsRoot.basis 1)), smul_neg,
    f4WR_smul_single_one]
  rfl

private theorem stdLayer_eq_C3Levi_of_mem_rootSL2R [CharP F 2] (hF : Nat.card F = 2)
    {x : ↥(adjointGroup .F4 F)} (hxJ : (x : ModGL .F4 F) ∈ rootSL2R F) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : stdLayer x = C3Levi F := by
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hXJ : Subgroup.zpowers x ≤ (highestRootRankOne F).subgroupOf (adjointGroup .F4 F) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf, highestRootRankOne_eq_rootSL2R]
    exact hxJ
  have hcard : Nat.card (Subgroup.zpowers x) = Nat.card F + 1 := by
    rw [Nat.card_zpowers, hord, hF]
  have hcyc : IsCyclic (Subgroup.zpowers x) := inferInstance
  have h5 : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup _) : Set ↥(adjointGroup .F4 F)) =
      Subgroup.centralizer ({x} : Set ↥(adjointGroup .F4 F)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨hC, -, -⟩ := centralizer_nonsplit hXJ hcyc hcard
  have hDX : C3Levi F ≤ Subgroup.centralizer ({x} : Set ↥(adjointGroup .F4 F)) := by
    rw [← h5, hC]
    exact le_sup_right
  have hcomm : ⁅Subgroup.centralizer ({x} : Set ↥(adjointGroup .F4 F)),
      Subgroup.centralizer ({x} : Set ↥(adjointGroup .F4 F))⁆ ≤ C3Levi F := by
    rw [Subgroup.commutator_le]
    intro c₁ hc₁ c₂ hc₂
    rw [commutatorElement_def]
    rw [← h5] at hc₁ hc₂
    exact commutator_mem_C3Levi_of_mem_centralizer_nonsplit hXJ hcyc hcard hc₁ hc₂
  exact (CFSG.LocalAnalysis.GLTheoremA.S172B.Cent.glaLayer_eq_of_commutator_le hDX hcomm
    isQuasisimple_C3Levi).1

private theorem exists_conj_mem_rootSL2R [CharP F 2] (g : ↥(StatedSp 3 F)) :
    ∃ h : ↥(adjointGroup .F4 F),
      ((h * ((c3LeviEquiv F (g * ⁅Sp.x 3 F (Pi.single 2 1) 1, Sp.x 3 F (-Pi.single 2 1) 1⁆ *
        g⁻¹) : C3Levi F) : ↥(adjointGroup .F4 F)) * h⁻¹ : ↥(adjointGroup .F4 F)) :
          ModGL .F4 F) ∈ rootSL2R F := by
  set c : ↥(adjointGroup .F4 F) := ((c3LeviEquiv F g : C3Levi F) : ↥(adjointGroup .F4 F))
  set a : ↥(adjointGroup .F4 F) :=
    ⟨pinnedX .F4 F (Pi.single 1 1) 1, pinnedX_mem_adjointGroup _ 1⟩
  set b : ↥(adjointGroup .F4 F) :=
    ⟨pinnedX .F4 F (-Pi.single 1 1) 1, pinnedX_mem_adjointGroup _ 1⟩
  have he : ((c3LeviEquiv F (g * ⁅Sp.x 3 F (Pi.single 2 1) 1, Sp.x 3 F (-Pi.single 2 1) 1⁆ *
      g⁻¹) : C3Levi F) : ↥(adjointGroup .F4 F)) = c * ⁅a, b⁆ * c⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_commutatorElement]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    rw [c3LeviEquiv_x_single_two, c3LeviEquiv_x_neg_single_two]
  set n : ↥(adjointGroup .F4 F) := ⟨canonicalRep (coxeterSystem .F4) F f4WR,
    canonicalRep_mem_adjointGroup (coxeterSystem .F4) F f4WR⟩
  refine ⟨n * c⁻¹, ?_⟩
  rw [he, show n * c⁻¹ * (c * ⁅a, b⁆ * c⁻¹) * (n * c⁻¹)⁻¹ = n * ⁅a, b⁆ * n⁻¹ by group,
    ← map_conj_canonicalRep_rootPair_one]
  refine ⟨((⁅a, b⁆ : ↥(adjointGroup .F4 F)) : ModGL .F4 F), ?_, rfl⟩
  have ha : (a : ModGL .F4 F) ∈
      rootSubgroup .F4 F (Pi.single 1 1) ⊔ rootSubgroup .F4 F (-Pi.single 1 1) :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨1, rfl⟩)
  have hb : (b : ModGL .F4 F) ∈
      rootSubgroup .F4 F (Pi.single 1 1) ⊔ rootSubgroup .F4 F (-Pi.single 1 1) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨1, rfl⟩)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem false_of_stdLayer_le_C3Levi (hF : Nat.card F = 2) [Finite ↥(adjointGroup .F4 F)]
    {A : Subgroup ↥(adjointGroup .F4 F)} {d : ↥(adjointGroup .F4 F)} (hd : IsStdElt 3 A d)
    (hAM : A ≤ C3Levi F) (hKM : stdLayer d ≤ C3Levi F) : False := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  obtain ⟨hdA, hd1, hd3, hcompd, -⟩ := hd
  have hdM : d ∈ C3Levi F := hAM hdA
  set e := c3LeviEquiv F
  have hcomp := isComponentOf_centralizer_map_symm e hdM hcompd hKM
  have hd₀1 : e.symm ⟨d, hdM⟩ ≠ 1 := fun h =>
    hd1 (congrArg Subtype.val ((MulEquiv.map_eq_one_iff e.symm).1 h))
  have hdM3 : (⟨d, hdM⟩ : C3Levi F) ^ 3 = 1 := Subtype.ext hd3
  have hd₀3 : (e.symm ⟨d, hdM⟩) ^ 3 = 1 := by rw [← map_pow, hdM3, map_one]
  obtain ⟨g, hg⟩ := exists_conj_eq_commutator_x_of_isComponentOf hF hd₀1 hd₀3 hcomp
  have hdg : d = ((e (g * ⁅Sp.x 3 F (Pi.single 2 1) 1, Sp.x 3 F (-Pi.single 2 1) 1⁆ * g⁻¹) :
      C3Levi F) : ↥(adjointGroup .F4 F)) := by
    rw [← hg, MulEquiv.apply_symm_apply]
  obtain ⟨h, hh⟩ := exists_conj_mem_rootSL2R g
  rw [← hdg] at hh
  have hx3 : (h * d * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hd3, mul_one, mul_inv_cancel]
  have hx1 : h * d * h⁻¹ ≠ 1 := fun h' => hd1 (conj_eq_one_iff.1 h')
  have hx := stdLayer_eq_C3Levi_of_mem_rootSL2R hF hh hx3 hx1
  have hmap := stdLayer_map_mulEquiv (MulAut.conj h) d
  rw [MulAut.conj_apply, hx] at hmap
  have hcardeq : Nat.card (stdLayer d) = Nat.card (C3Levi F) := by
    rw [hmap, Subgroup.card_map_of_injective (MulAut.conj h).injective]
  have hEq : stdLayer d = C3Levi F := Subgroup.eq_of_le_of_card_ge hKM hcardeq.symm.le
  have hcent : (⟨d, hdM⟩ : C3Levi F) ∈ Subgroup.center (C3Levi F) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hz : (z : ↥(adjointGroup .F4 F)) ∈ Subgroup.centralizer ({d} : Set _) :=
      hcompd.1 (hEq.symm ▸ z.2)
    exact Subgroup.mem_centralizer_singleton_iff.1 hz
  rw [center_C3Levi_eq_bot, Subgroup.mem_bot] at hcent
  exact hd1 (congrArg Subtype.val hcent)

theorem false_of_stdLayer_le_B3Levi (hF : Nat.card F = 2) [Finite ↥(adjointGroup .F4 F)]
    {A : Subgroup ↥(adjointGroup .F4 F)} {d : ↥(adjointGroup .F4 F)} (hd : IsStdElt 3 A d)
    (hAM : A ≤ B3Levi F) (hKM : stdLayer d ≤ B3Levi F) : False := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  haveI : CharP F CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP F 2›
  have hB : (B3Levi F).map (graphAutF4 F).symm.toMonoidHom = C3Levi F := by
    rw [← map_graphAutF4_C3Levi]
    exact CFSG.RankThreeEvenClassification.Helpers.subgroup_map_equiv_symm _ _
  refine false_of_stdLayer_le_C3Levi hF (isStdElt_map (graphAutF4 F).symm hd)
    ((Subgroup.map_mono hAM).trans hB.le) ?_
  rw [stdLayer_map_mulEquiv, ← hB]
  exact Subgroup.map_mono hKM

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
