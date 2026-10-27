module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Glue

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Eight2

namespace CtxA0

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

theorem exists_pComponent_l43 (hS : SchreierFor Blueprint.Catalog) (hQ : CFQPUJ6Three)
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)))
    (hq3 : c.s.p = 3 ∧ c.s.f = 1) :
    ∃ M : Subgroup X, M ≤ centralizer ({c.b} : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({c.b} : Set X))) ∧
      Seven.Lay c.s.h c.s.y ≤ M ∧ GSLit.fixedLayer c.s.h.J (zpowers c.b) ≤ M ∧
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃*
        ↥(Seven.Lay c.s.h c.s.y) ⧸ pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y)) ∧
      Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 4 3 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hMC, hMpc, hLM⟩ := c.exists_pComponent_le_sup hS
  have hLie : IsL4U4Mod4 (↥(Seven.Lay c.s.h c.s.y) ⧸ pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y))
      c.s.p c.s.f := c.lieModel_Lay hA
  set Y := centralizer ({c.b} : Set X) with hYdef
  have hKY : SectionRank.IsKGroupCat ↥Y := isKGroupCat_of_ne_top' c.s.kProper c.centralizer_b_ne_top
  have hbB0 : c.b ∈ c.s.h.secB0 c.s.y := c.hbB
  have hB0Y : c.s.h.secB0 c.s.y ≤ Y := c.secB0_le_centralizer_b
  have hCB0Y : centralizer (c.s.h.secB0 c.s.y : Set X) ≤ Y :=
    centralizer_le (Set.singleton_subset_iff.mpr hbB0)
  have hLY : Seven.Lay c.s.h c.s.y ≤ Y := c.s.Lay_le_centralizer.trans hCB0Y
  have haY : c.s.h.a ∈ Y := mem_centralizer_singleton_iff.mpr c.hba.symm
  have hbY : c.b ∈ Y := mem_centralizer_singleton_iff.mpr rfl
  have hzY : c.Z.z ∈ Y := mem_centralizer_singleton_iff.mpr c.hbz.symm
  set Jb := GSLit.fixedLayer c.s.h.J (zpowers c.b) with hJbdef
  have hJbC := c.Jb_le
  have hJbY : Jb ≤ Y := hJbC.trans inf_le_right
  obtain ⟨hJ0Jb, hJ0sup⟩ := c.J0_le_Jb
  have hJbty : IsSec8JType (↥Jb ⧸ pPrimeCore 2 ↥Jb) 3 1 := by
    obtain ⟨eJ⟩ := c.s.sec_J_equiv
    obtain ⟨eJb⟩ := QPUJ.nonempty_fixedLayer_quot_equiv (B5a.isQuasisimple_J c.s.h)
      c.zpowers_b_le_coreActionKernel c.isPGroup_zpowers_b
    have h1 := CatFactsL4U4.Cover82.isSec8JType_of_mulEquiv (eJ.trans eJb.symm) c.s.J_type
    rwa [hq3.1, hq3.2] at h1
  have hJbLie : Blueprint.LieModel (↥Jb ⧸ pPrimeCore 2 ↥Jb) .PSL 2 c.s.p (2 * c.s.f) := by
    rw [hq3.1, hq3.2]
    rcases hJbty with h1 | ⟨-, -, ⟨e6⟩⟩
    · exact h1
    · exact LieType.CurtisTits.lieModel_of_mulEquiv e6.symm
        Catalog82A10.lieModel_alternatingGroup_six
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
  set b' : Y := ⟨c.b, hbY⟩ with hb'
  set z' : Y := ⟨c.Z.z, hzY⟩ with hz'
  set g' : Y := ⟨c.s.t, hLY c.htL⟩ with hg'
  have hbZ : b' ∈ center Y := mem_center_iff.mpr fun w => Subtype.ext
    (mem_centralizer_singleton_iff.mp w.2)
  have hab2 : a' * b' * (a' * b') = 1 := Subtype.ext c.ab_mul_ab
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
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hCB0Y 2
      Nat.prime_two).mpr c.s.L_pc
  have htK : a' * b' ∈ K := c.ab_mem_Lay
  have hgK : g' ∈ K := c.htL
  have hgw : g'⁻¹ * z' * g' = a' * b' := Subtype.ext c.hzb
  have hz2 : z' * z' = 1 := Subtype.ext c.Z.hzz
  have htw : a' * b' * z' = z' * (a' * b') := Subtype.ext c.ab_comm_z
  have hwt : z' ≠ a' * b' := fun h1 => c.z_ne_ab (congrArg Subtype.val h1)
  set J : Subgroup Y := Jb.subgroupOf Y with hJdef
  have hCtY : (centralizer ({c.s.h.a} : Set X) ⊓ Y).subgroupOf Y =
      centralizer ({a' * b'} : Set Y) := by
    rw [QPUJ.centralizer_mul_of_mem_center hbZ]
    ext w
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, and_true,
      mem_centralizer_singleton_iff]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩
  have hJC : J ≤ centralizer ({a' * b'} : Set Y) := by
    rw [← hCtY]
    exact fun w hw => hJbC hw
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({a' * b'} : Set Y))) := by
    rw [← hCtY]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two).mpr c.isPComponent_Jb
  set JB : Subgroup Y := (c.s.h.secJ0 c.s.y).subgroupOf Y with hJBdef
  have hJ0L : c.s.h.secJ0 c.s.y ≤ Seven.Lay c.s.h c.s.y := Seven.J0_le_Lay c.s.h c.s.y
  have hJ0Y : c.s.h.secJ0 c.s.y ≤ Y := hJ0L.trans hLY
  have hJBK : JB ≤ K := fun w hw => hJ0L hw
  have hJBJ : JB ≤ J := fun w hw => hJ0Jb hw
  have hJBp : ⁅JB, JB⁆ = JB := by
    apply map_injective Y.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJ0Y, hJ0p]
  have hJB1 : JB ≠ ⊥ := by
    intro hbot
    apply hJ01
    have h1 : JB.map Y.subtype = c.s.h.secJ0 c.s.y := map_subgroupOf_eq_of_le hJ0Y
    rw [← h1, hbot, Subgroup.map_bot]
  have hJB : JB ⊔ (pPrimeCore 2 ↥J).map J.subtype = J := by
    apply map_injective Y.subtype_injective
    have hcomp : Y.subtype.comp J.subtype =
        Jb.subtype.comp (subgroupOfEquivOfLe hJbY).toMonoidHom := by
      ext x
      rfl
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hJ0Y, map_subgroupOf_eq_of_le hJbY, map_map,
      hcomp, ← map_map, pPrimeCore_map_iso]
    exact hJ0sup
  have hKM : K ≤ M.subgroupOf Y ⊔ pPrimeCore 2 ↥Y := by
    rw [← map_le_map_iff_of_injective Y.subtype_injective, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hLY, map_subgroupOf_eq_of_le hMC]
    exact hLM
  have hKLie : IsL4U4Mod4 (↥K ⧸ pPrimeCore 2 ↥K) c.s.p c.s.f :=
    IsL4U4Mod4.of_mulEquiv (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hLY).symm) hLie
  have hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 c.s.p (2 * c.s.f) :=
    OddQuot.lieModel_of_equiv (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hJbY)).symm hJbLie
  obtain ⟨hKM', hJM', hcase⟩ := QPUJ.le_and_equiv_or_config63 hMpc hP hKC hKpc hKM c.s.hp
    c.s.hp2 c.s.hf hq3 hKLie htK hab2 hgK hgw hz2 htw hwt hJC hJpc hJLie hJBK hJBJ hJBp hJB1 hJB
  have hLayM : Seven.Lay c.s.h c.s.y ≤ M := fun x hx => hKM' (show (⟨x, hLY hx⟩ : Y) ∈ K from hx)
  have hJbM : Jb ≤ M := fun x hx => hJM' (show (⟨x, hJbY hx⟩ : Y) ∈ J from hx)
  rcases hcase with heM | hconf
  ·
    obtain ⟨eM⟩ := heM
    let e : ↥M ⧸ pPrimeCore 2 ↥M ≃*
        ↥(Seven.Lay c.s.h c.s.y) ⧸ pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y) :=
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
        (subgroupOfEquivOfLe hMC).symm).trans (eM.trans
          (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
            (subgroupOfEquivOfLe hLY)))
    have hLieM : IsL4U4Mod4 (↥M ⧸ pPrimeCore 2 ↥M) c.s.p c.s.f :=
      IsL4U4Mod4.of_mulEquiv e.symm hLie
    have hLieM3 : Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 4 3 1 := by
      rcases hLieM with ⟨h1, -⟩ | ⟨-, h1⟩
      · rwa [hq3.1, hq3.2] at h1
      · rw [hq3.1, hq3.2] at h1
        norm_num at h1
    exact ⟨M, hMC, hMpc, hLayM, hJbM, ⟨e⟩, hLieM3⟩
  ·
    exfalso
    have hKYb : SectionRank.IsKGroupCat (↥Y ⧸ pPrimeCore 2 ↥Y) :=
      OddQuot.isKGroupCat_of_surjective hKY _ (QuotientGroup.mk'_surjective _)
    have := hconf.1.2.1
    exact hQ _ c.s.p c.s.f hconf (SectionRank.catalog_of_isKGroupCat_of_surjective hKYb
      ((M.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 ↥Y)))
      (QuotientGroup.mk' (center _)) (QuotientGroup.mk'_surjective _))

end CtxA0

end Eight2

end CFSG.ComponentClassification.GSThmB
