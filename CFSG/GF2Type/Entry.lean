module

public import CFSG.LargeExtraspecial.BridgeSetting

public section

namespace CFSG.GF2Type

open CFSG CFSG.Open CFSG.LargeExtraspecial.Bridge

theorem timmesfeld_hypotheses {G : Type} [Group G] {z : G} {w : ℕ}
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
      2 ^ (1 + 2 * w)) :
    timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) ∧
      Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w) := by
  set M := Subgroup.centralizer ({z} : Set G) with hM
  let e : generalizedFitting ↥M ≃* inSubgroup generalizedFitting M :=
    (generalizedFitting ↥M).equivMapOfInjective M.subtype M.subtype_injective
  rw [← generalizedFitting_eq_timmesfeldFStar]
  exact ⟨(timmesfeldIsExtraspecial_congr e).mpr ((timmesfeldIsExtraspecial_iff _).mpr hext),
    (Nat.card_congr e).trans hcard⟩

theorem exists_quotient_generalizedFitting (H : Type) [Group H] :
    ∃ (Mbar : Type) (_ : Group Mbar), timmesfeldQuotientIso (generalizedFitting H) Mbar := by
  have : (generalizedFitting H).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  exact ⟨H ⧸ generalizedFitting H, inferInstance,
    ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩⟩

end CFSG.GF2Type
