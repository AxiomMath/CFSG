module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblySections
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceCore
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient

public section

namespace CFSG.ComponentClassification.LBalance

open CFSG.Open Subgroup

namespace Asm

variable {G : Type*} [Group G] [Finite G]

theorem lBalancePLayer_top (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    lBalancePLayer p (⊤ : Subgroup G) = pLayer G p := by
  unfold lBalancePLayer pLayer
  congr 1
  ext L
  exact (CatalogueBAlternating.pComponent_iff_lBalance_top p L).symm

theorem lBalancePLayer_eq_map (p : ℕ) [Fact p.Prime] (Y : Subgroup G) :
    lBalancePLayer p Y = (pLayer Y p).map Y.subtype := by
  rw [← pLayer_nested_map p Y Y le_rfl, subgroupOf_self, lBalancePLayer_top]

theorem pComponent_normal_restriction (p : ℕ) [Fact p.Prime] (Y L : Subgroup G) [Y.Normal]
    (hL : lBalanceIsPComponent p ⊤ L) (hLY : L ≤ Y) : lBalanceIsPComponent p Y L := by
  obtain ⟨hchain, hC, hminimal⟩ := (pComponent_top_iff_minimal_image p L).mp hL
  refine (pComponent_iff_minimal_image p Y L hLY).mpr ⟨?_, ?_, ?_⟩
  · apply (subnormal_subgroupOf_iff hLY).mp
    simpa only [top_subgroupOf] using subnormal_subgroupOf hchain Y
  · let q := QuotientGroup.mk' (pPrimeCore p G)
    let I := Y.map q
    have hI : IsComponentOf ((L.map q).subgroupOf I) ⊤ :=
      LocalComponents.of_overgroup hC (map_mono hLY)
    have heq : (L.map q).subgroupOf I =
        (quotientImage p Y L).map (normalQuotientEquivImage p Y).toMonoidHom := by
      have h := congrArg (Subgroup.comap I.subtype) (quotientImage_normal_transport p Y L hLY)
      change (((quotientImage p Y L).map
        (normalQuotientEquivImage p Y).toMonoidHom).map I.subtype).comap I.subtype =
        (L.map q).subgroupOf I at h
      rw [comap_map_eq_self_of_injective I.subtype_injective] at h
      exact h.symm
    rw [heq] at hI
    exact (LocalComponents.equiv_iff (normalQuotientEquivImage p Y) (quotientImage p Y L)).mp hI
  · intro J hJL hJ hmap
    have hJtop : IsSubnormal J ⊤ := Components.chain_of_mathlib_subnormal
      (Components.mathlib_subnormal_of_chain hJ (inferInstance : Y.Normal).isSubnormal)
    exact hminimal J hJL hJtop
      ((normal_quotientImage_eq_iff p Y J L (hJL.trans hLY) hLY).mp hmap)

theorem pComponent_relative_normal_restriction (p : ℕ) [Fact p.Prime] (Y M L : Subgroup G)
    (hYM : Y ≤ M) [(Y.subgroupOf M).Normal] (hL : lBalanceIsPComponent p M L) (hLY : L ≤ Y) :
    lBalanceIsPComponent p Y L := by
  have htop : lBalanceIsPComponent p (⊤ : Subgroup M) (L.subgroupOf M) := by
    have h := (pComponent_nested_iff p M M L le_rfl (hLY.trans hYM)).mpr hL
    rwa [subgroupOf_self] at h
  exact (pComponent_nested_iff p Y M L hYM hLY).mp
    (pComponent_normal_restriction p (Y.subgroupOf M) (L.subgroupOf M) htop fun _ hx => hLY hx)

theorem pLayer_le_of_pComponents_le (p : ℕ) [Fact p.Prime] (Y M : Subgroup G) (hYM : Y ≤ M)
    [(Y.subgroupOf M).Normal] (h : ∀ L, lBalanceIsPComponent p M L → L ≤ Y) :
    lBalancePLayer p M ≤ lBalancePLayer p Y :=
  sSup_le fun L hL => le_sSup (pComponent_relative_normal_restriction p Y M L hYM hL (h L hL))

end Asm

theorem pLayer_centralizer_element_le {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hH : SchreierSections H) {x : H} (hx : ∃ n : ℕ, x ^ p ^ n = 1) :
    (pLayer (centralizer ({x} : Set H)) p).map (centralizer ({x} : Set H)).subtype ≤
      pLayer H p :=
  pLayer_centralizer_le_pLayer_of_quotient hx fun _ hLC hL =>
    pComponent_centralizer_le_layer (pPrimeCore_quotient_pPrimeCore_eq_bot p)
      (Quot.exists_mk_pow_eq_one hx) (hH.quotient (pPrimeCore p H)).outer_component hLC hL

theorem lBalancePLayer_centralizer_element_le {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hH : SchreierSections H) {x : H} (hx : ∃ n : ℕ, x ^ p ^ n = 1) :
    lBalancePLayer p (centralizer ({x} : Set H)) ≤ lBalancePLayer p ⊤ := by
  rw [Asm.lBalancePLayer_eq_map, Asm.lBalancePLayer_top]
  exact pLayer_centralizer_element_le hH hx

theorem lBalancePLayer_inf_centralizer_le {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hX : SchreierSections X) {M : Subgroup X} {x : X} (hxM : x ∈ M)
    (hx : ∃ n : ℕ, x ^ p ^ n = 1) :
    lBalancePLayer p (M ⊓ centralizer ({x} : Set X)) ≤ lBalancePLayer p M := by
  have hx' : ∃ n : ℕ, (⟨x, hxM⟩ : M) ^ p ^ n = 1 :=
    hx.imp fun n hn => Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hn)
  have hC : (M ⊓ centralizer ({x} : Set X)).subgroupOf M =
      centralizer ({(⟨x, hxM⟩ : M)} : Set M) := by
    ext y
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, true_and,
      mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [← pLayer_nested_map p (M ⊓ centralizer ({x} : Set X)) M inf_le_left, hC,
    ← pLayer_nested_map p M M le_rfl, subgroupOf_self]
  exact map_mono (lBalancePLayer_centralizer_element_le (hX.subgroup M) hx')

end CFSG.ComponentClassification.LBalance
