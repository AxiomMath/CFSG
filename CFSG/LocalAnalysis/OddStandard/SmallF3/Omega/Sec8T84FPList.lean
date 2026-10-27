module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPSpan

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Certificates.Asc82NormA6
open Certificates.T84P (Elt mulE oneE commE M0l span4)

theorem sec8t84FPRaw_eq_oneE_iff (F : Facts) (x : Sec8T84FPM0 F) :
    sec8t84FPRaw F x = oneE ↔ x = 1 := by
  rw [← sec8t84FPRaw_one F]
  exact (sec8t84FPRaw_injective F).eq_iff

theorem sec8t84FPRaw_mul_self_iff (F : Facts) (x : Sec8T84FPM0 F) :
    mulE (sec8t84FPRaw F x) (sec8t84FPRaw F x) = oneE ↔ x * x = 1 := by
  rw [← sec8t84FPRaw_mul, sec8t84FPRaw_eq_oneE_iff]

theorem sec8t84FPRaw_commE_iff (F : Facts) (x y : Sec8T84FPM0 F) :
    commE (sec8t84FPRaw F x) (sec8t84FPRaw F y) ↔ x * y = y * x := by
  change mulE _ _ = mulE _ _ ↔ _
  rw [← sec8t84FPRaw_mul, ← sec8t84FPRaw_mul]
  exact (sec8t84FPRaw_injective F).eq_iff

theorem sec8t84FPRaw_mul_inv (F : Facts) (x : Sec8T84FPM0 F) :
    mulE (sec8t84FPRaw F x) (sec8t84FPRaw F x⁻¹) = oneE := by
  rw [← sec8t84FPRaw_mul, mul_inv_cancel, sec8t84FPRaw_one]

private lemma t84_mulE_oneE (x : Elt) : mulE x oneE = x := by
  simp [mulE, oneE]

theorem sec8t84FPRaw_prod4 (F : Facts) (a b c d : Sec8T84FPM0 F) :
    (sec8t84Prod4 a b c d).map (sec8t84FPRaw F) =
      span4 (sec8t84FPRaw F a) (sec8t84FPRaw F b) (sec8t84FPRaw F c) (sec8t84FPRaw F d) := by
  simp [sec8t84Prod4, span4, sec8t84FPRaw_mul, sec8t84FPRaw_one, t84_mulE_oneE]

theorem sec8t84FPV0_card (F : Facts) : Nat.card (Sec8T84FPV0 F) = 16 := by
  rw [Sec8T84FPV0, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective SemidirectProduct.inl_injective, Subgroup.card_top]
  simp [Nat.card_eq_fintype_card]

theorem sec8t84FPOfList_card_eq_length (F : Facts) {l : List Elt} (h1 : oneE ∈ l)
    (hmul : ∀ x ∈ l, ∀ y ∈ l, mulE x y ∈ l) (hl : ∀ z ∈ l, z ∈ M0l) (hnd : l.Nodup) :
    Nat.card (sec8t84FPOfList F l h1 hmul) = l.length := by
  rw [sec8t84FPOfList_card F h1 hmul hl, List.toFinset_card_of_nodup hnd]

theorem sec8t84FPOfList_le (F : Facts) {l l' : List Elt} (h1 : oneE ∈ l)
    (hmul : ∀ x ∈ l, ∀ y ∈ l, mulE x y ∈ l) (h1' : oneE ∈ l')
    (hmul' : ∀ x ∈ l', ∀ y ∈ l', mulE x y ∈ l') (h : ∀ z ∈ l, z ∈ l') :
    sec8t84FPOfList F l h1 hmul ≤ sec8t84FPOfList F l' h1' hmul' := fun x hx =>
  (sec8t84FPOfList_mem F h1' hmul' x).mpr (h _ ((sec8t84FPOfList_mem F h1 hmul x).mp hx))

end CFSG.OddStandard.SmallF3.Omega
