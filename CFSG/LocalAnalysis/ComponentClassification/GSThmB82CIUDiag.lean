module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82SecondCentral
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPDiag
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB10
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Final
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalB

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Eight2

namespace CtxA0

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

theorem secB0_le_centralizer_b : c.s.h.secB0 c.s.y ≤ centralizer ({c.b} : Set X) := fun _ hw =>
  mem_centralizer_singleton_iff.mpr (c.b_comm_of_mem_S0 (mem_inf.mpr
    ⟨c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y hw), le_normalizer hw⟩)).symm

theorem centralizer_b_ne_top : centralizer ({c.b} : Set X) ≠ ⊤ := by
  have := c.s.isSimpleGroup
  intro htop
  apply c.b_ne_one
  have hcen : c.b ∈ center X := by
    rw [mem_center_iff]
    intro w
    have hw : w ∈ centralizer ({c.b} : Set X) := by
      rw [htop]
      exact mem_top w
    exact mem_centralizer_singleton_iff.mp hw
  have hbot : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨u, v, huv⟩ := c.s.nonab
      exact huv ((mem_center_iff.mp (h1 ▸ mem_top v : v ∈ center X)) u)
  rw [hbot] at hcen
  exact mem_bot.mp hcen

theorem zpowers_b_le_coreActionKernel : zpowers c.b ≤ coreActionKernel c.s.h.J :=
  (zpowers_le.mpr c.hbB).trans ((Hyp52.secB0_le_P (h := c.s.h) (y := c.s.y)).trans inf_le_right)

theorem isPGroup_zpowers_b : IsPGroup 2 (zpowers c.b) :=
  Pump516.isPGroup_zpowers_of_pow ⟨1, by rw [pow_one, pow_two, c.hbb]⟩

theorem Jb_le : GSLit.fixedLayer c.s.h.J (zpowers c.b) ≤
    centralizer ({c.s.h.a} : Set X) ⊓ centralizer ({c.b} : Set X) := by
  refine le_inf (((GSLit.fixedLayer_le_inf _ _).trans inf_le_left).trans c.s.h.J_le) ?_
  have h1 := (GSLit.fixedLayer_le_inf c.s.h.J (zpowers c.b)).trans inf_le_right
  rwa [centralizer_zpowers_eq] at h1

theorem isPComponent_Jb : IsPComponent 2 ((GSLit.fixedLayer c.s.h.J (zpowers c.b)).subgroupOf
    (centralizer ({c.s.h.a} : Set X) ⊓ centralizer ({c.b} : Set X))) := by
  have hbCa : zpowers c.b ≤ centralizer ({c.s.h.a} : Set X) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
      (c.s.h.comm_a (c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y c.hbB))))
  obtain ⟨-, -, hJs, -, -⟩ := id c.s.h.isPComponent_J
  have h1 := GSLit.fixedLayer_isPComponent c.s.h.J_le hJs hbCa c.zpowers_b_le_coreActionKernel
    c.isPGroup_zpowers_b (B5a.isQuasisimple_J c.s.h)
  rwa [centralizer_zpowers_eq] at h1

theorem J0_le_Jb : c.s.h.secJ0 c.s.y ≤ GSLit.fixedLayer c.s.h.J (zpowers c.b) ∧
    c.s.h.secJ0 c.s.y ⊔ (pPrimeCore 2 ↥(GSLit.fixedLayer c.s.h.J (zpowers c.b))).map
      (GSLit.fixedLayer c.s.h.J (zpowers c.b)).subtype =
      GSLit.fixedLayer c.s.h.J (zpowers c.b) :=
  GSLit.fixedLayer_nested (B5a.isQuasisimple_J c.s.h)
    ((Hyp52.secB0_le_P (h := c.s.h) (y := c.s.y)).trans inf_le_right) (c.s.h.isPGroup_secB0 c.s.y)
    (zpowers_le.mpr c.hbB)

theorem exists_pComponent_le_sup (hS : SchreierFor Blueprint.Catalog) :
    ∃ M : Subgroup X, M ≤ centralizer ({c.b} : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({c.b} : Set X))) ∧
      Seven.Lay c.s.h c.s.y ≤ M ⊔ oddCoreIn (centralizer ({c.b} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbB0 : c.b ∈ c.s.h.secB0 c.s.y := c.hbB
  have habL : c.s.h.a * c.b ∈ Seven.Lay c.s.h c.s.y := by
    have hzL : c.Z.z ∈ Seven.Lay c.s.h c.s.y :=
      Seven.J0_le_Lay c.s.h c.s.y (c.s.D_le_J0 c.Z.hzD)
    rw [← c.hzb]
    exact mul_mem (mul_mem (inv_mem c.htL) hzL) c.htL
  set Y := centralizer ({c.b} : Set X) with hYdef
  have hYS := schreierSections_of_isKGroupCat hS
    (isKGroupCat_of_ne_top' c.s.kProper c.centralizer_b_ne_top)
  have hB0Y : c.s.h.secB0 c.s.y ≤ Y := c.secB0_le_centralizer_b
  have hCB0Y : centralizer (c.s.h.secB0 c.s.y : Set X) ≤ Y :=
    centralizer_le (Set.singleton_subset_iff.mpr hbB0)
  have hLY : Seven.Lay c.s.h c.s.y ≤ Y := c.s.Lay_le_centralizer.trans hCB0Y
  have haY : c.s.h.a ∈ Y := mem_centralizer_singleton_iff.mpr
    (c.s.h.comm_a (c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y hbB0))).symm
  have hbY : c.b ∈ Y := mem_centralizer_singleton_iff.mpr rfl
  set Jb := GSLit.fixedLayer c.s.h.J (zpowers c.b) with hJbdef
  have hJ0C := c.s.h.secJ0_le c.s.y
  have hJ0pc := Hyp52.isPComponent_secJ0 (h := c.s.h) (y := c.s.y)
  have hJ0p : ⁅c.s.h.secJ0 c.s.y, c.s.h.secJ0 c.s.y⁆ = c.s.h.secJ0 c.s.y :=
    Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf hJ0C hJ0pc)
  have hJ01 : c.s.h.secJ0 c.s.y ≠ ⊥ := by
    intro hbot
    have := B5a.nontrivial_of_isPComponent_subgroupOf hJ0C hJ0pc
    rw [hbot] at this
    exact not_nontrivial _ this
  set a' : Y := ⟨c.s.h.a, haY⟩ with ha'
  set b' : Y := ⟨c.b, hbY⟩ with hb'def
  have ha2 : a' * a' = 1 := Subtype.ext (Six.a_mul_a_self c.s.h)
  have hbZ : b' ∈ center Y := mem_center_iff.mpr fun w => Subtype.ext
    (mem_centralizer_singleton_iff.mp w.2)
  set P : Subgroup Y := (c.s.h.secB0 c.s.y).subgroupOf Y with hPdef
  have hP : IsPGroup 2 P := (c.s.h.isPGroup_secB0 c.s.y).comap_subtype
  have hCP : centralizer (P : Set Y) = (centralizer (c.s.h.secB0 c.s.y : Set X)).subgroupOf Y :=
    B5a.centralizer_subgroupOf hB0Y
  set K : Subgroup Y := (Seven.Lay c.s.h c.s.y).subgroupOf Y with hKdef
  have hKC : K ≤ centralizer (P : Set Y) := by
    rw [hCP]
    exact fun w hw => c.s.Lay_le_centralizer hw
  have hKpc : IsPComponent 2 (K.subgroupOf (centralizer (P : Set Y))) := by
    rw [hCP]
    exact (isPComponent_subgroupOf_subgroupOf_iff' hCB0Y 2 Nat.prime_two).mpr c.s.L_pc
  set J : Subgroup Y := Jb.subgroupOf Y with hJdef
  have hCaY : (centralizer ({c.s.h.a} : Set X) ⊓ Y).subgroupOf Y =
      centralizer ({a'} : Set Y) := by
    ext w
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, and_true,
      mem_centralizer_singleton_iff]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩
  have hJC : J ≤ centralizer ({a'} : Set Y) := by
    rw [← hCaY]
    exact fun w hw => c.Jb_le hw
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({a'} : Set Y))) := by
    rw [← hCaY]
    exact (isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two).mpr
      c.isPComponent_Jb
  set JB : Subgroup Y := (c.s.h.secJ0 c.s.y).subgroupOf Y with hJBdef
  have hJ0L : c.s.h.secJ0 c.s.y ≤ Seven.Lay c.s.h c.s.y := Seven.J0_le_Lay c.s.h c.s.y
  have hJ0Y : c.s.h.secJ0 c.s.y ≤ Y := hJ0L.trans hLY
  have hJBK : JB ≤ K := fun w hw => hJ0L hw
  have hJBJ : JB ≤ J := fun w hw => c.J0_le_Jb.1 hw
  have hJBp : ⁅JB, JB⁆ = JB := by
    apply map_injective Y.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJ0Y, hJ0p]
  have hJB1 : JB ≠ ⊥ := by
    intro hbot
    apply hJ01
    have h1 : JB.map Y.subtype = c.s.h.secJ0 c.s.y := map_subgroupOf_eq_of_le hJ0Y
    rw [← h1, hbot, Subgroup.map_bot]
  have habK : a' * b' ∈ K := habL
  obtain ⟨L₀, hL₀, hKL₀⟩ := Seven.exists_isComponent_le_of_inner hYS hP ha2 hbZ hKC hKpc hJC
    hJpc habK hJBK hJBJ hJBp hJB1
  obtain ⟨M', hM', -, hKM'⟩ := Seven.exists_pComponent_le_sup_of_map_le hL₀ hKL₀
  refine ⟨M'.map Y.subtype, map_subtype_le _, ?_, ?_⟩
  · rwa [show (M'.map Y.subtype).subgroupOf Y = M' from
      comap_map_eq_self_of_injective Y.subtype_injective M']
  · have h1 := map_mono (f := Y.subtype) hKM'
    rw [map_subgroupOf_eq_of_le hLY, Subgroup.map_sup] at h1
    exact h1

end CtxA0

end Eight2

end CFSG.ComponentClassification.GSThmB
