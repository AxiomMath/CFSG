module

public import CFSG.LargeExtraspecial.S4Res

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem resL_eq_one_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g)
    (x : S.Lbar g) : resL haQ ht x = 1 ↔ (x : S.O) ∈ Nbar S g t := by
  have := restrictHom_eq_one_iff (S.O.subtype.comp (S.Lbar g).subtype) (Vt S g t)
    (fun x _ hu => apply_mem_Vt_of_mem_Rbar haQ (Lbar_le_Rbar ht x.2) hu) x
  exact this.trans ⟨fun h => ⟨Lbar_le_Rbar ht x.2, h⟩, fun h => h.2⟩

theorem card_Lbar_eq (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g) :
    Nat.card (S.Lbar g) = Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      Nat.card (LmodN S g t) := by
  have hker : (resL haQ ht).ker = (Nbar S g t).subgroupOf (S.Lbar g) := by
    ext x
    rw [MonoidHom.mem_ker, resL_eq_one_iff haQ ht, mem_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (resL haQ ht).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (resL haQ ht)).toEquiv,
    range_resL haQ ht, hker] at h1
  rw [h1, mul_comm]
  congr 1
  have e : (Nbar S g t).subgroupOf (S.Lbar g) =
      (S.Lbar g ⊓ Nbar S g t).subgroupOf (S.Lbar g) := by
    ext x
    simp [mem_subgroupOf]
  rw [e]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv

end CFSG.LargeExtraspecial.S5
