module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBHeldSmallCore

theorem primeCore_normal_step_mem_iff {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] {lower upper : Subgroup G} (hle : lower ≤ upper)
    [(lower.subgroupOf upper).Normal] (element : lower) :
    element ∈ pPrimeCore p lower ↔
      Subgroup.inclusion hle element ∈ pPrimeCore p upper := by
  let equivalence := Subgroup.subgroupOfEquivOfLe hle
  have hintersection :
      (pPrimeCore p (lower.subgroupOf upper)).map (lower.subgroupOf upper).subtype =
        lower.subgroupOf upper ⊓ pPrimeCore p upper := by
    rw [← LBalance.primeCore_eq_map, LBalance.primeCore_normal_intersection]
  have hmem : ∀ member : lower.subgroupOf upper,
      member ∈ pPrimeCore p (lower.subgroupOf upper) ↔
        member.val ∈ pPrimeCore p upper := by
    intro member
    rw [← Subgroup.mem_map_iff_mem (lower.subgroupOf upper).subtype_injective,
      hintersection]
    change member.val ∈ lower.subgroupOf upper ∧ _ ↔ _
    exact and_iff_right member.property
  rw [← pPrimeCore_map_iso p equivalence, Subgroup.mem_map_equiv]
  exact hmem (equivalence.symm element)

theorem primeCore_subnormal_mem_iff {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] {lower upper : Subgroup G}
    (hsubnormal : Open.IsSubnormal lower upper) (element : G) (hmem : element ∈ lower) :
    (⟨element, hmem⟩ : lower) ∈ pPrimeCore p lower ↔
      ∃ hupper : element ∈ upper, (⟨element, hupper⟩ : upper) ∈ pPrimeCore p upper := by
  induction hsubnormal with
  | refl subgroup => exact ⟨fun hcore => ⟨hmem, hcore⟩, fun ⟨_, hcore⟩ => hcore⟩
  | @step lower middle upper hle hnormal hsubnormal hinduction =>
      let : (lower.subgroupOf middle).Normal := hnormal
      rw [primeCore_normal_step_mem_iff p hle]
      exact hinduction (hle hmem)

theorem primeCore_subnormal_intersection {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hsubnormal : L.IsSubnormal) :
    pPrimeCore p L = (pPrimeCore p G).subgroupOf L := by
  have hchain := Components.chain_of_mathlib_subnormal hsubnormal
  have htop : ∀ member : (⊤ : Subgroup G),
      member ∈ pPrimeCore p (⊤ : Subgroup G) ↔ member.val ∈ pPrimeCore p G := by
    intro member
    rw [← Subgroup.mem_map_iff_mem (⊤ : Subgroup G).subtype_injective,
      ← LBalance.primeCore_eq_map, LBalance.primeCore_top]
    rfl
  ext element
  change element ∈ pPrimeCore p L ↔ element.val ∈ pPrimeCore p G
  constructor
  · intro hcore
    obtain ⟨hmem, hmember⟩ :=
      (primeCore_subnormal_mem_iff p hchain element.val element.property).mp hcore
    exact (htop ⟨element.val, hmem⟩).mp hmember
  · intro hcore
    apply (primeCore_subnormal_mem_iff p hchain element.val element.property).mpr
    exact ⟨Subgroup.mem_top element.val,
      (htop ⟨element.val, Subgroup.mem_top element.val⟩).mpr hcore⟩

@[expose] def subnormalCoreQuotientEquivImage {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hsubnormal : L.IsSubnormal) :
    (L ⧸ pPrimeCore p L) ≃* L.map (QuotientGroup.mk' (pPrimeCore p G)) := by
  let q := QuotientGroup.mk' (pPrimeCore p G)
  let I := L.map q
  let f : L →* I := (q.comp L.subtype).codRestrict I
    (fun l => Subgroup.mem_map_of_mem q l.property)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp x.property
    exact ⟨⟨l, hl⟩, Subtype.ext hlx⟩
  have hker : pPrimeCore p L = f.ker := by
    ext l
    change l ∈ pPrimeCore p L ↔ f l = 1
    rw [primeCore_subnormal_intersection p L hsubnormal]
    change l.val ∈ pPrimeCore p G ↔ f l = 1
    rw [← QuotientGroup.eq_one_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  exact QuotientGroup.liftEquiv _ hsurj hker

theorem subnormalCoreQuotientEquivImage_mk {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hsubnormal : L.IsSubnormal) (l : L) :
    (subnormalCoreQuotientEquivImage p L hsubnormal
      ((QuotientGroup.mk' (pPrimeCore p L)) l)).val =
        (QuotientGroup.mk' (pPrimeCore p G)) l.val := by
  dsimp only [subnormalCoreQuotientEquivImage]
  erw [QuotientGroup.liftEquiv_mk]
  rfl

theorem pComponent_perfect {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hL : CFSG.IsPComponent p L) :
    Group.IsPerfect L :=
  LBalance.pComponent_perfect p ⊤ L
    ((CatalogueBAlternating.pComponent_iff_lBalance_top p L).mp hL)

theorem pComponent_coreQuotient_quasisimple {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple (L ⧸ pPrimeCore p L) := by
  obtain ⟨K, hK, hsubnormal, hmap, _⟩ := hL
  have himage : Open.IsQuasisimple (L.map (QuotientGroup.mk' (pPrimeCore p G))) := by
    rw [hmap]
    exact ((CFSG.isComponent_iff_open K).mp hK).2.2
  have hquasisimple := Components.quasisimple_of_equiv
    (subnormalCoreQuotientEquivImage p L hsubnormal) himage
  exact ⟨⟨hquasisimple.1⟩, hquasisimple.2,
    Helpers.quasisimple_central_quotient_nonabelian _ hquasisimple⟩

end CFSG.ComponentClassification.CatalogueBHeldSmallCore
