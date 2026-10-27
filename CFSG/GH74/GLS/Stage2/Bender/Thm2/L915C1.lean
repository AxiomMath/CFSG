module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915A1
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Trans
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutD1Aut
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Quot

variable {P Q : Type} [Group P] [Group Q]

@[expose] noncomputable def quotientCenterEquiv (hP : Group.IsPerfect P) (f : P →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ center P) : (P ⧸ center P) ≃* (Q ⧸ center Q) :=
  have hc : center P = ((QuotientGroup.mk' (center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker]
  (QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))

end Quot

section CaseC

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {N A B : Subgroup G}

theorem exists_caseC_J (hC : Ctx9 G z k S M p) (h : Hyp95 z M p N A B)
    (hAE : ¬ A ≤ centralizer (Em N : Set G))
    (hcC : C43c (zSec z N (z_mem_N h) (pCore p ↥N)) p (xBar p N (A1 z M N p))) :
    ∃ (J : Subgroup ↥N) (n : ℕ), 1 ≤ n ∧ IsComponent J ∧
      (∀ y : ↥N, y ∈ normalizer (J : Set ↥N)) ∧ pCore p ↥N ≤ centralizer (J : Set ↥N) ∧
      J.map (QuotientGroup.mk' (pCore p ↥N)) = ncl (xBar p N (A1 z M N p)) ∧
      (⟨z, z_mem_N h⟩ : ↥N) ∈ J ∧ (A1 z M N p).subgroupOf N ≤ J ∧
      LieModel (↥J ⧸ center ↥J) .PSL 3 p n ∧ ¬ A.subgroupOf N ≤ centralizer (J : Set ↥N) ∧
      IsElementaryAbelian p ↥(xBar p N (A1 z M N p)) ∧
      Nat.card ↥(xBar p N (A1 z M N p)) = p ^ (2 * n) := by
  have hp := hC.prime
  have hzN : z ∈ N := z_mem_N h
  obtain ⟨n, hn, hLie, hXz, hmax, hOp, hel, hcard⟩ := hcC
  obtain ⟨J, hJ, hAJ⟩ := exists_component_noncentral_of_Em h.A_N hAE
  have hOJ : pCore p ↥N ≤ centralizer (J : Set ↥N) := pCore_le_centralizer_component hp hJ
  have hJ' : IsComponent (J.map (QuotientGroup.mk' (pCore p ↥N))) :=
    isComponent_map_mk hp CFSG.pCore_normal hJ CFSG.pCore_isPGroup
  have hA₁ : A.subgroupOf N ≤ (A1 z M N p).subgroupOf N := fun x hx => A_le_A1 h hx
  have hnc : ¬ xBar p N (A1 z M N p) ≤
      centralizer ((J.map (QuotientGroup.mk' (pCore p ↥N)) : Subgroup _) : Set _) :=
    not_le_centralizer_map hp hJ hA₁ hAJ
  set Xb := xBar p N (A1 z M N p) with hXb
  set zb := zSec z N hzN (pCore p ↥N) with hzb
  have hKn : (ncl Xb).Normal := Subgroup.normalClosure_normal
  have hXK : Xb ≤ ncl Xb := Subgroup.subset_normalClosure
  have hJK : J.map (QuotientGroup.mk' (pCore p ↥N)) ≤ ncl Xb :=
    component_le_of_noncentral hKn hJ' hXK hnc
  obtain ⟨F, iF, fF, hFcard, ⟨ι⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  have hsimple : IsSimpleGroup (↥(ncl Xb) ⧸ center ↥(ncl Xb)) := by
    have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
      L46E.isSimpleGroup_P3
    exact ι.isSimpleGroup
  have hJeq : J.map (QuotientGroup.mk' (pCore p ↥N)) = ⁅ncl Xb, ncl Xb⁆ :=
    component_eq_commutator_of_le hKn hJ' hJK hsimple
  have hzK : zb ∈ ncl Xb := hXz (Subgroup.mem_sup_right (Subgroup.mem_zpowers zb))
  have hA₁comm : ⁅(A1 z M N p).subgroupOf N, zpowers (⟨z, hzN⟩ : ↥N)⁆ = (A1 z M N p).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (A1_le hC hzN |>.trans inf_le_right),
      MonoidHom.map_zpowers]
    exact A1_comm hC hzN
  have hXcomm : ⁅Xb, zpowers zb⁆ = Xb := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' (pCore p ↥N))) hA₁comm
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at h1
    exact h1
  have hXJ : Xb ≤ J.map (QuotientGroup.mk' (pCore p ↥N)) := by
    rw [hJeq]
    calc Xb = ⁅Xb, zpowers zb⁆ := hXcomm.symm
      _ ≤ ⁅ncl Xb, ncl Xb⁆ := Subgroup.commutator_mono hXK (Subgroup.zpowers_le.mpr hzK)
  have hJn' : (J.map (QuotientGroup.mk' (pCore p ↥N))).Normal := by
    rw [hJeq]
    infer_instance
  have hKJ : ncl Xb ≤ J.map (QuotientGroup.mk' (pCore p ↥N)) :=
    Subgroup.normalClosure_le_normal hXJ
  have hJK_eq : J.map (QuotientGroup.mk' (pCore p ↥N)) = ncl Xb := le_antisymm hJK hKJ
  have hJnorm : ∀ y : ↥N, y ∈ normalizer (J : Set ↥N) := by
    intro y
    refine mem_normalizer_of_image hp hJ ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr hJn']
    exact Subgroup.mem_top _
  have hlift : ∀ y : ↥N, QuotientGroup.mk' (pCore p ↥N) y ∈ ncl Xb →
      ∃ j ∈ J, ∃ o ∈ pCore p ↥N, y = j * o := by
    intro y hy
    rw [← hJK_eq] at hy
    obtain ⟨j, hjJ, hjy⟩ := hy
    refine ⟨j, hjJ, j⁻¹ * y, ?_, by group⟩
    have h1 : QuotientGroup.mk' (pCore p ↥N) (j⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hjy]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hOcomm : ∀ o ∈ pCore p ↥N, ∀ g ∈ J, g * o = o * g := fun o ho g hg =>
    Subgroup.mem_centralizer_iff.mp (hOJ ho) g hg
  have : Fact p.Prime := ⟨hp⟩
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hC.orderOf_z, pow_two] at h1
    exact h1
  have hzJ : (⟨z, hzN⟩ : ↥N) ∈ J := by
    obtain ⟨j, hjJ, o, ho, hjo⟩ := hlift ⟨z, hzN⟩ hzK
    have hjr : j * o = o * j := hOcomm o ho j hjJ
    have hodd : Odd (orderOf o) := by
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf (p := p)).mp (CFSG.pCore_isPGroup (G := ↥N) (p := p))
        ⟨o, ho⟩
      have h1 : orderOf o = p ^ m := by
        rw [← hm]
        exact Subgroup.orderOf_coe (⟨o, ho⟩ : ↥(pCore p ↥N))
      rw [h1]
      exact (hp.odd_of_ne_two hC.odd).pow
    have hz2' : (⟨z, hzN⟩ : ↥N) * ⟨z, hzN⟩ = 1 := Subtype.ext hz2
    have hoj : o ∈ zpowers j := mem_zpowers_of_involution_mul hjr hodd hz2' hjo
    rw [hjo]
    exact mul_mem hjJ (Subgroup.zpowers_le.mpr hjJ hoj)
  have hA₁J : (A1 z M N p).subgroupOf N ≤ J := by
    rw [← hA₁comm]
    refine Subgroup.commutator_le.mpr fun a ha g hg => ?_
    have haK : QuotientGroup.mk' (pCore p ↥N) a ∈ ncl Xb := hXK ⟨a, ha, rfl⟩
    obtain ⟨j, hjJ, o, ho, hjo⟩ := hlift a haK
    have hgJ : g ∈ J := Subgroup.zpowers_le.mpr hzJ hg
    have h1 : ⁅a, g⁆ = ⁅j, g⁆ := by
      rw [hjo, commutatorElement_def, commutatorElement_def]
      have := hOcomm o ho g hgJ
      calc j * o * g * (j * o)⁻¹ * g⁻¹ = j * (o * g) * o⁻¹ * j⁻¹ * g⁻¹ := by group
        _ = j * (g * o) * o⁻¹ * j⁻¹ * g⁻¹ := by rw [← this]
        _ = j * g * j⁻¹ * g⁻¹ := by group
    rw [h1, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hjJ hgJ) (J.inv_mem hjJ)) (J.inv_mem hgJ)
  have hker : ((QuotientGroup.mk' (pCore p ↥N)).subgroupMap J).ker ≤ center ↥J := by
    intro x hx
    have hx1 : QuotientGroup.mk' (pCore p ↥N) (x : ↥N) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa using this
    have hxO : (x : ↥N) ∈ pCore p ↥N := (QuotientGroup.eq_one_iff _).mp hx1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hOcomm _ hxO g g.2)
  let e : (↥J ⧸ center ↥J) ≃*
      (↥(J.map (QuotientGroup.mk' (pCore p ↥N))) ⧸
        center ↥(J.map (QuotientGroup.mk' (pCore p ↥N)))) :=
    quotientCenterEquiv hJ.1.1 ((QuotientGroup.mk' (pCore p ↥N)).subgroupMap J)
      ((QuotientGroup.mk' (pCore p ↥N)).subgroupMap_surjective J) hker
  have hLie' : LieModel (↥(J.map (QuotientGroup.mk' (pCore p ↥N))) ⧸
      center ↥(J.map (QuotientGroup.mk' (pCore p ↥N)))) .PSL 3 p n := by
    rw [hJK_eq]
    exact hLie
  exact ⟨J, n, hn, hJ, hJnorm, hOJ, hJK_eq, hzJ, hA₁J,
    Odd87.Transport.lieModel_of_mulEquiv e.symm hLie', hAJ, hel, hcard⟩

end CaseC

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
