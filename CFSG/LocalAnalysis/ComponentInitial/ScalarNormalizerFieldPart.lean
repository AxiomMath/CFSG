module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeOuterPrimeSupport

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification.CatalogueBSmallRee

variable {K : Type*} [Field K] [Finite K]

def scalarNormalizerFieldPart :
    Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) →* (K ≃+* K) where
  toFun := semilinearFieldAut
  map_one' := semilinearFieldAut_eq (c := 1) fun x => by
    rw [Units.val_one, one_mul]
    rfl
  map_mul' f g := by
    obtain ⟨c, hc⟩ := exists_apply_eq_mul_semilinearFieldAut f
    obtain ⟨d, hd⟩ := exists_apply_eq_mul_semilinearFieldAut g
    refine semilinearFieldAut_eq
      (c := c * Units.map (semilinearFieldAut f).toRingHom.toMonoidHom d) fun x => ?_
    change (f : Multiplicative (AddAut K)).toAdd ((g : Multiplicative (AddAut K)).toAdd x) = _
    rw [hd, hc, map_mul, Units.val_mul, Units.coe_map, RingAut.mul_apply, mul_assoc]
    rfl

theorem scalarNormalizerFieldPart_eq
    {f : Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))} {c : Kˣ}
    {σ : K ≃+* K} (h : ∀ x, (f : Multiplicative (AddAut K)).toAdd x = c * σ x) :
    scalarNormalizerFieldPart f = σ :=
  semilinearFieldAut_eq h

theorem scalarNormalizerFieldPart_eq_one_iff
    (f : Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))) :
    scalarNormalizerFieldPart f = 1 ↔ (f : Multiplicative (AddAut K)) ∈ scalarAddAut K :=
  semilinearFieldAut_eq_one_iff f

end CFSG.LocalAnalysis.ComponentInitial
