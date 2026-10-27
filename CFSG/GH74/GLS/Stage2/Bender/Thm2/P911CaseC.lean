module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Comp
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C1
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C4
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Hyp
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915D1
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {X V N : Subgroup G}

theorem exists_caseC_J_X (hC : Ctx9 G z k S M p) (hzN : z ∈ N) (hXN : X ≤ N)
    (hXA : X ≤ L915.A1 z M N p) (hXE : ¬ X ≤ centralizer (Em N : Set G))
    (hcC : C43c (zSec z N hzN (pCore p ↥N)) p (xBar p N (L915.A1 z M N p))) :
    ∃ (J : Subgroup ↥N) (n : ℕ), 1 ≤ n ∧ IsComponent J ∧
      (∀ y : ↥N, y ∈ normalizer (J : Set ↥N)) ∧ pCore p ↥N ≤ centralizer (J : Set ↥N) ∧
      J.map (QuotientGroup.mk' (pCore p ↥N)) = ncl (xBar p N (L915.A1 z M N p)) ∧
      (⟨z, hzN⟩ : ↥N) ∈ J ∧ (L915.A1 z M N p).subgroupOf N ≤ J ∧
      LieModel (↥J ⧸ center ↥J) .PSL 3 p n ∧ ¬ X.subgroupOf N ≤ centralizer (J : Set ↥N) ∧
      IsElementaryAbelian p ↥(xBar p N (L915.A1 z M N p)) ∧
      Nat.card ↥(xBar p N (L915.A1 z M N p)) = p ^ (2 * n) := by
  have hp := hC.prime
  obtain ⟨n, hn, hLie, hXz, hmax, hOp, hel, hcard⟩ := hcC
  obtain ⟨J, hJ, hXJ'⟩ := L915.exists_component_noncentral_of_Em hXN hXE
  have hOJ : pCore p ↥N ≤ centralizer (J : Set ↥N) := L915.pCore_le_centralizer_component hp hJ
  have hJ' : IsComponent (J.map (QuotientGroup.mk' (pCore p ↥N))) :=
    L915.isComponent_map_mk hp CFSG.pCore_normal hJ CFSG.pCore_isPGroup
  have hA₁ : X.subgroupOf N ≤ (L915.A1 z M N p).subgroupOf N := fun x hx => hXA hx
  have hnc : ¬ xBar p N (L915.A1 z M N p) ≤
      centralizer ((J.map (QuotientGroup.mk' (pCore p ↥N)) : Subgroup _) : Set _) :=
    L915.not_le_centralizer_map hp hJ hA₁ hXJ'
  set Xb := xBar p N (L915.A1 z M N p) with hXb
  set zb := zSec z N hzN (pCore p ↥N) with hzb
  have hKn : (ncl Xb).Normal := Subgroup.normalClosure_normal
  have hXK : Xb ≤ ncl Xb := Subgroup.subset_normalClosure
  have hJK : J.map (QuotientGroup.mk' (pCore p ↥N)) ≤ ncl Xb :=
    L915.component_le_of_noncentral hKn hJ' hXK hnc
  obtain ⟨F, iF, fF, hFcard, ⟨ι⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  have hsimple : IsSimpleGroup (↥(ncl Xb) ⧸ center ↥(ncl Xb)) := by
    have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
      L46E.isSimpleGroup_P3
    exact ι.isSimpleGroup
  have hJeq : J.map (QuotientGroup.mk' (pCore p ↥N)) = ⁅ncl Xb, ncl Xb⁆ :=
    L915.component_eq_commutator_of_le hKn hJ' hJK hsimple
  have hzK : zb ∈ ncl Xb := hXz (Subgroup.mem_sup_right (Subgroup.mem_zpowers zb))
  have hA₁comm : ⁅(L915.A1 z M N p).subgroupOf N, zpowers (⟨z, hzN⟩ : ↥N)⁆ =
      (L915.A1 z M N p).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le (L915.A1_le hC hzN |>.trans inf_le_right),
      MonoidHom.map_zpowers]
    exact L915.A1_comm hC hzN
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
    refine L915.mem_normalizer_of_image hp hJ ?_
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
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf (p := p)).mp
        (CFSG.pCore_isPGroup (G := ↥N) (p := p)) ⟨o, ho⟩
      have h1 : orderOf o = p ^ m := by
        rw [← hm]
        exact Subgroup.orderOf_coe (⟨o, ho⟩ : ↥(pCore p ↥N))
      rw [h1]
      exact (hp.odd_of_ne_two hC.odd).pow
    have hz2' : (⟨z, hzN⟩ : ↥N) * ⟨z, hzN⟩ = 1 := Subtype.ext hz2
    have hoj : o ∈ zpowers j := L915.mem_zpowers_of_involution_mul hjr hodd hz2' hjo
    rw [hjo]
    exact mul_mem hjJ (Subgroup.zpowers_le.mpr hjJ hoj)
  have hA₁J : (L915.A1 z M N p).subgroupOf N ≤ J := by
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
    L915.quotientCenterEquiv hJ.1.1 ((QuotientGroup.mk' (pCore p ↥N)).subgroupMap J)
      ((QuotientGroup.mk' (pCore p ↥N)).subgroupMap_surjective J) hker
  have hLie' : LieModel (↥(J.map (QuotientGroup.mk' (pCore p ↥N))) ⧸
      center ↥(J.map (QuotientGroup.mk' (pCore p ↥N)))) .PSL 3 p n := by
    rw [hJK_eq]
    exact hLie
  exact ⟨J, n, hn, hJ, hJnorm, hOJ, hJK_eq, hzJ, hA₁J,
    Odd87.Transport.lieModel_of_mulEquiv e.symm hLie', hXJ', hel, hcard⟩

theorem V_le_centralizer_layer_of_caseC (h118 : IG_11_8) (H : Hyp911 z k S M p X V N)
    (hzN : z ∈ N) (hXA : X ≤ L915.A1 z M N p) (hXE : ¬ X ≤ centralizer (Em N : Set G))
    (hcC : C43c (zSec z N hzN (pCore p ↥N)) p (xBar p N (L915.A1 z M N p))) :
    V.subgroupOf N ≤ centralizer ((layer ↥N : Subgroup ↥N) : Set ↥N) := by
  have hC : Ctx9 G z k S M p := H.ctx
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have : Fact p.Prime := ⟨hp⟩
  have hXN : X ≤ N := le_trans Subgroup.le_normalizer H.hXN
  obtain ⟨J, n, hn, hJ, hJn, -, -, hzJ, -, hLie, -, -, -⟩ :=
    exists_caseC_J_X hC hzN hXN hXA hXE hcC
  have hO2 : Op 2 N = ⊥ := L915.lemma9_2a h118 hC H.hXP H.hzX H.hXN
  have hO2' : pCore 2 ↥N = ⊥ := by
    have := hO2
    rw [Op_eq_map, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at this
    exact le_bot_iff.mp this
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hC.orderOf_z, pow_two] at h1
    exact h1
  have hz1 : z ≠ 1 := by
    intro h1
    have := hC.orderOf_z
    rw [h1, orderOf_one] at this
    omega
  set z' : ↥N := ⟨z, hzN⟩ with hz'
  have hz2' : z' * z' = 1 := Subtype.ext hz2
  have hz1' : z' ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  set A₀ : Subgroup G := Op p M ⊓ N ⊓ Cen z with hA₀def
  have hA₀N : A₀ ≤ N := inf_le_left.trans inf_le_right
  have hA₀P : A₀ ≤ Op p M := inf_le_left.trans inf_le_left
  have hA₀p : IsPGroup p ↥A₀ := hC.P_pgroup.to_le hA₀P
  have hA₀'p : IsPGroup p ↥(A₀.subgroupOf N) :=
    hA₀p.of_injective (Subgroup.subgroupOfEquivOfLe hA₀N).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hA₀N).injective
  have hnormA₀ : ∀ c : G, c * z = z * c → c ∈ N → c ∈ normalizer (A₀ : Set G) := by
    intro c hcz hcN
    have hcC : c ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hcz
    have hcM : c ∈ M := hC.cen_le hcC
    exact Thm1.mem_normalizer_inf (Thm1.mem_normalizer_inf (le_normalizer_Op' p M hcM)
      (Subgroup.le_normalizer hcN))
      (L915.mem_normalizer_centralizer_of_comm (S := {z}) fun s hs => by
        rw [Set.mem_singleton_iff.mp hs]; exact hcz.symm)
  have hA₀'n : ∀ c : ↥N, c * z' = z' * c →
      c ∈ normalizer ((A₀.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    intro c hc
    have h1 := hnormA₀ (c : G) (congrArg Subtype.val hc) c.2
    rw [mem_normalizer_iff]
    intro x
    have h2 := (mem_normalizer_iff.mp h1) (x : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using h2
  have hA₀'z : ∀ a ∈ A₀.subgroupOf N, a * z' = z' * a := by
    intro a ha
    have : (a : G) ∈ Cen z := (Subgroup.mem_subgroupOf.mp ha).2
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp this)
  have hcent : A₀.subgroupOf N ≤ centralizer (J : Set ↥N) :=
    L915.centralizes_of_K1 L915.k1_statement hp hp2 hn hO2' hJ hJn hLie hzJ hz2' hz1' hA₀'p hA₀'z
      hA₀'n
  have hA₀odd : Odd (Nat.card ↥(A₀.subgroupOf N)) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p)).mp hA₀'p
    rw [hm]
    exact (hp.odd_of_ne_two hp2).pow
  have hcard : Nat.card (CFSG.LocalCores.ComponentIndex ↥N) ≤ 2 :=
    card_componentIndex_le_two (SectionalTwoRankLE.subgroup N H.ctx.ctx.std.gen4)
  have hA₀norm : ∀ K : Subgroup ↥N, IsComponent K →
      A₀.subgroupOf N ≤ normalizer (K : Set ↥N) := by
    intro K hK a ha
    exact mem_normalizer_of_odd_orderOf hcard
      (Odd.of_dvd_nat hA₀odd (Subgroup.orderOf_dvd_natCard _ ha)) hK
  have hcomp : ∀ K : Subgroup ↥N, IsComponent K →
      A₀.subgroupOf N ≤ centralizer (K : Set ↥N) := by
    intro K hK
    rcases CFSG.LocalCores.distinct_components_commute hK hJ with rfl | hKJ
    · exact hcent
    · have hKJc : K ≤ centralizer (J : Set ↥N) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKJ
      have hKz : ∀ c ∈ K, c * z' = z' * c := fun c hc =>
        (Subgroup.mem_centralizer_iff.mp (hKJc hc) z' hzJ).symm
      have hKA : K ≤ normalizer ((A₀.subgroupOf N : Subgroup ↥N) : Set ↥N) := fun c hc =>
        hA₀'n c (hKz c hc)
      exact L915.commute_of_normal_pgroup_of_normal_quasisimple hp
        (H := normalizer (K : Set ↥N) ⊓ normalizer ((A₀.subgroupOf N : Subgroup ↥N) : Set ↥N))
        (U := A₀.subgroupOf N) (I := K) hK.1 (le_inf Subgroup.le_normalizer hKA)
        (fun h hh => hh.1) (le_inf (hA₀norm K hK) Subgroup.le_normalizer) (fun h hh => hh.2) hA₀'p
  have hVA : V.subgroupOf N ≤ A₀.subgroupOf N := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (H.hV (Subgroup.mem_subgroupOf.mp hx))
  refine Subgroup.le_centralizer_iff.mpr (sSup_le fun K hK => Subgroup.le_centralizer_iff.mp ?_)
  exact hVA.trans (hcomp K hK)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
