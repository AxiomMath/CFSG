module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoOn

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G Y : Type} [Group G] [Group Y] {K : Subgroup G}

@[expose] noncomputable def autOfIsoOn (e : Y ≃* ↥K) {η : G → G} (hη : IsIsoOn K K η) : Y ≃* Y :=
  e.trans (hη.toMulEquiv.trans e.symm)

theorem autOfIsoOn_apply (e : Y ≃* ↥K) {η : G → G} (hη : IsIsoOn K K η) (y : Y) :
    ((e (autOfIsoOn e hη y) : ↥K) : G) = η (e y : G) := by
  simp only [autOfIsoOn, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem eq_or_conj_of_xAutCent (e : Y ≃* ↥K) {T : Y} (hT : XAutCent Y T) {t : G}
    (het : ((e T : ↥K) : G) = t) {η : G → G} (hη : IsIsoOn K K η)
    (hfix : ∀ x ∈ K, x * t = t * x → η x = x) :
    (∀ x ∈ K, η x = x) ∨ ∀ x ∈ K, η x = t * x * t⁻¹ := by
  have hσ : ∀ y : Y, y * T = T * y → autOfIsoOn e hη y = y := by
    intro y hy
    refine e.injective (Subtype.ext ?_)
    have hy' : ((e y : ↥K) : G) * t = t * ((e y : ↥K) : G) := by
      rw [← het, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hy]
    rw [autOfIsoOn_apply]
    exact hfix _ (e y).2 hy'
  rcases hT _ hσ with hid | hconj
  · left
    intro x hx
    have h1 := congrArg (fun y => ((e y : ↥K) : G)) (hid (e.symm ⟨x, hx⟩))
    simpa only [autOfIsoOn_apply, MulEquiv.apply_symm_apply] using h1
  · right
    intro x hx
    have h1 := congrArg (fun y => ((e y : ↥K) : G)) (hconj (e.symm ⟨x, hx⟩))
    simpa only [autOfIsoOn_apply, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, het] using h1

end CFSG.EvenSporadicStandard.HNRecog.Section4
