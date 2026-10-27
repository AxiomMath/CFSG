module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem primeResidual_eq_bot_of_coprime_card {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hcard : p.Coprime (Nat.card G)) : primeResidual p G = ⊥ := by
  apply le_antisymm _ bot_le
  apply sSup_le
  intro P hP
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcardOne : Nat.card P = 1 := by
    apply Nat.eq_one_of_dvd_coprimes (hcard.pow_left k)
    · rw [hk]
    · exact Subgroup.card_subgroup_dvd_card _
  exact (Subgroup.card_eq_one.mp hcardOne).le

theorem primeResidual_eq_top_of_corefree_quasisimple {G : Type*}
    [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hquasisimple : CFSG.IsQuasisimple G) (hcorefree : pPrimeCore p G = ⊥) :
    primeResidual p G = ⊤ := by
  let : (primeResidual p G).Characteristic := primeResidual_characteristic p G
  have hnative := CatalogueBAlternating.quasisimple_iff_native.mp hquasisimple
  rcases Quasisimple.normal_le_center_or_eq_top hnative (primeResidual p G) with
    hcentral | htop
  · let : Group.IsPerfect G := hquasisimple.1
    let : Nontrivial G := Quasisimple.nontrivial hnative
    let P : Sylow p G := Classical.choice inferInstance
    have hPCentral : (P : Subgroup G) ≤ Subgroup.center G :=
      (pSubgroup_le_residual p _ P.isPGroup').trans hcentral
    let : IsMulCommutative (P : Subgroup G) := isMulCommutative_iff.mpr
      fun x y => Subtype.ext ((Subgroup.mem_center_iff.mp (hPCentral x.property)) y).symm
    have hnormalizer : Subgroup.normalizer (P : Set G) ≤
        Subgroup.centralizer (P : Set G) := by
      intro x _
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      exact ((Subgroup.mem_center_iff.mp (hPCentral hy)) x).symm
    let transfer := MonoidHom.transferSylow P hnormalizer
    have htransfer : transfer = 1 := PerfectAutomorphisms.hom_eq_one_of_commutative transfer
    have hkernel : transfer.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr htransfer
    have hnotP : ¬ p ∣ Nat.card G := by
      have hnot := MonoidHom.not_dvd_card_ker_transferSylow P hnormalizer
      change ¬ p ∣ Nat.card transfer.ker at hnot
      simpa only [hkernel, Subgroup.card_top] using hnot
    have hcoprime : p.Coprime (Nat.card G) :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnotP
    have hcoreTop : (⊤ : Subgroup G) ≤ pPrimeCore p G :=
      le_sSup ⟨inferInstance, by simpa only [Subgroup.card_top] using hcoprime⟩
    rw [hcorefree] at hcoreTop
    exact (not_le_of_gt (bot_lt_top : (⊥ : Subgroup G) < ⊤) hcoreTop).elim
  · exact htop

theorem prime_dvd_card_center_quotient_of_corefree_quasisimple {G : Type*}
    [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hquasisimple : CFSG.IsQuasisimple G) (hcorefree : pPrimeCore p G = ⊥) :
    p ∣ Nat.card (G ⧸ Subgroup.center G) := by
  by_contra hnot
  have hcoprime := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnot
  have hmap := primeResidual_map_surjective p (QuotientGroup.mk' (Subgroup.center G))
    (QuotientGroup.mk'_surjective _)
  rw [primeResidual_eq_top_of_corefree_quasisimple p hquasisimple hcorefree,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    primeResidual_eq_bot_of_coprime_card p hcoprime] at hmap
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasisimple.2.1
  exact (not_le_of_gt (bot_lt_top : (⊥ : Subgroup (G ⧸ Subgroup.center G)) < ⊤)
    hmap.le).elim

theorem quotient_component_iff_core_quotient {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hL : L.IsSubnormal) :
    CFSG.IsComponent (L.map (QuotientGroup.mk' (pPrimeCore p G))) ↔
      CFSG.IsQuasisimple (L ⧸ pPrimeCore p L) := by
  let e := CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage p L hL
  constructor
  · intro hcomponent
    exact CatalogueBAlternating.quasisimple_iff_native.mpr
      (Components.quasisimple_of_equiv e
        (CatalogueBAlternating.quasisimple_iff_native.mp hcomponent.1))
  · intro hquasisimple
    refine ⟨CatalogueBAlternating.quasisimple_iff_native.mpr
      (Components.quasisimple_of_equiv e.symm
        (CatalogueBAlternating.quasisimple_iff_native.mp hquasisimple)), ?_⟩
    exact hL.map (QuotientGroup.mk'_surjective _)

theorem primeResidual_eq_top_of_pComponent {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hL : CFSG.IsPComponent p L) :
    primeResidual p L = ⊤ := by
  let core := pPrimeCore p L
  let q := QuotientGroup.mk' core
  have hquasisimple := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple p L hL
  have hgenerated : primeResidual p (L ⧸ core) = ⊤ :=
    primeResidual_eq_top_of_corefree_quasisimple p hquasisimple
      (pPrimeCore_quotient_pPrimeCore_eq_bot (G := L) (p := p))
  have hresidualMap : (primeResidual p L).map q = ⊤ := by
    rw [primeResidual_map_surjective p q (QuotientGroup.mk'_surjective core)]
    exact hgenerated
  let R := primeResidual p L
  let ambientR := R.map L.subtype
  let : R.Characteristic := primeResidual_characteristic p L
  have hR : R.IsSubnormal := (inferInstance : R.Normal).isSubnormal
  have hambient : ambientR.IsSubnormal := hR.trans' hL.choose_spec.2.1
  have hmap : ambientR.map (QuotientGroup.mk' (pPrimeCore p G)) =
      L.map (QuotientGroup.mk' (pPrimeCore p G)) := by
    apply le_antisymm (Subgroup.map_mono (Subgroup.map_subtype_le R))
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have htarget : q (⟨y, hy⟩ : L) ∈ R.map q := by
      rw [hresidualMap]
      exact Subgroup.mem_top _
    obtain ⟨z, hz, hvalue⟩ := Subgroup.mem_map.mp htarget
    have hkernel : z⁻¹ * (⟨y, hy⟩ : L) ∈ core := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (z⁻¹ * (⟨y, hy⟩ : L)) = 1
      rw [map_mul, map_inv, hvalue, inv_mul_cancel]
    have hambientKernel : z.val⁻¹ * y ∈ pPrimeCore p G := by
      change z⁻¹ * (⟨y, hy⟩ : L) ∈ (pPrimeCore p G).subgroupOf L
      rw [← CatalogueBHeldSmallCore.primeCore_subnormal_intersection p L hL.choose_spec.2.1]
      exact hkernel
    have hambientValue : (QuotientGroup.mk' (pPrimeCore p G)) z.val =
        (QuotientGroup.mk' (pPrimeCore p G)) y := by
      have hone := (QuotientGroup.eq_one_iff _).mpr hambientKernel
      change (QuotientGroup.mk' (pPrimeCore p G)) (z.val⁻¹ * y) = 1 at hone
      rw [map_mul, map_inv] at hone
      exact inv_mul_eq_one.mp hone
    exact ⟨z.val, ⟨z, hz, rfl⟩, hambientValue⟩
  have hminimal := (CatalogueBAlternating.pComponent_iff_minimal_image p L).mp hL |>.2.2
  have heq := hminimal ambientR (Subgroup.map_subtype_le R)
    (Components.chain_of_mathlib_subnormal hambient) hmap
  apply top_unique
  intro x _
  have hx : x.val ∈ ambientR := by
    rw [heq]
    exact x.property
  obtain ⟨y, hy, hvalue⟩ := Subgroup.mem_map.mp hx
  exact (Subtype.ext hvalue : y = x) ▸ hy

theorem pComponent_iff_subnormal_generated_quasisimple {G : Type*}
    [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    CFSG.IsPComponent p L ↔ L.IsSubnormal ∧ primeResidual p L = ⊤ ∧
      CFSG.IsQuasisimple (L ⧸ pPrimeCore p L) := by
  constructor
  · intro hL
    exact ⟨hL.choose_spec.2.1, primeResidual_eq_top_of_pComponent p L hL,
      CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple p L hL⟩
  · rintro ⟨hsubnormal, hgenerated, hquasisimple⟩
    apply (CatalogueBAlternating.pComponent_iff_minimal_image p L).mpr
    refine ⟨Components.chain_of_mathlib_subnormal hsubnormal,
      (CFSG.isComponent_iff_open _).mp
        ((quotient_component_iff_core_quotient p L hsubnormal).mpr hquasisimple), ?_⟩
    intro J hJL hJ hmap
    let q := QuotientGroup.mk' (pPrimeCore p G)
    let I := L.map q
    let restriction : L →* I := (q.domRestrict L).codRestrict I
      (fun x => Subgroup.mem_map_of_mem q x.property)
    have hsurjective : Function.Surjective restriction := by
      intro x
      obtain ⟨y, hy, hvalue⟩ := Subgroup.mem_map.mp x.property
      exact ⟨⟨y, hy⟩, Subtype.ext hvalue⟩
    have hkernel : restriction.ker = pPrimeCore p L := by
      ext x
      change restriction x = 1 ↔ x ∈ pPrimeCore p L
      rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection p L hsubnormal]
      change restriction x = 1 ↔ x.val ∈ pPrimeCore p G
      rw [← QuotientGroup.eq_one_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hcover : Function.Surjective (restriction.domRestrict (J.subgroupOf L)) := by
      intro x
      have hx : x.val ∈ J.map q := by
        rw [hmap]
        exact x.property
      obtain ⟨y, hy, hvalue⟩ := Subgroup.mem_map.mp hx
      exact ⟨⟨⟨y, hJL hy⟩, hy⟩, Subtype.ext hvalue⟩
    have hindex := coprime_index_of_surjective_restriction p restriction hsurjective
      (by rw [hkernel]; exact pPrimeCore_coprime_card) (J.subgroupOf L) hcover
    have hlocal := primeResidual_le_subnormal_of_coprime_index p (J.subgroupOf L)
      ((Components.mathlib_subnormal_of_chain hJ .top).subgroupOf) hindex
    rw [hgenerated] at hlocal
    exact le_antisymm hJL (Subgroup.subgroupOf_eq_top.mp (top_unique hlocal))

end CFSG.ComponentClassification.CatalogueBPrimeJoin
