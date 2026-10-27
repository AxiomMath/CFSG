module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldProjection

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBUnitaryIsometry CFSG.LieType.Universal.Unitary

universe u

abbrev specialUnitaryScalars (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Subgroup (SUid sigma n) :=
  ((GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range).subgroupOf (SUid sigma n)

instance specialUnitaryScalarsNormal (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    (specialUnitaryScalars n K sigma).Normal := by
  change (((GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range).comap
    (SUid sigma n).subtype).Normal
  rw [← GeneralLinearGroup.center_eq_range_scalar]
  infer_instance

abbrev ProjectiveSpecialUnitary (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :=
  SUid sigma n ⧸ specialUnitaryScalars n K sigma

@[expose] def specialUnitaryProjection (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    SUid sigma n →* fixedPGL n K sigma :=
  (unitaryProjection n K sigma).comp (Subgroup.inclusion (SUid_le_Uid sigma n))

theorem specialUnitaryProjection_val (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : SUid sigma n) :
    (specialUnitaryProjection n K sigma g).val = ProjGenLinGroup.mk g.val := rfl

theorem specialUnitaryProjection_kernel (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    (specialUnitaryProjection n K sigma).ker = specialUnitaryScalars n K sigma := by
  ext g
  constructor
  · intro hg
    have hmk : ProjGenLinGroup.mk g.val = 1 := congrArg Subtype.val hg
    have hc := ProjGenLinGroup.mk_eq_one.mp hmk
    rwa [GeneralLinearGroup.center_eq_range_scalar] at hc
  · rintro ⟨c, hc⟩
    change GeneralLinearGroup.scalar (Fin n) c = g.val at hc
    apply Subtype.ext
    change ProjGenLinGroup.mk g.val = 1
    rw [← hc, ProjGenLinGroup.mk_scalar]

theorem specialUnitaryProjection_range (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    (specialUnitaryProjection n K sigma).range =
      (specialUnitary sigma n).map (unitaryProjection n K sigma) := by
  rw [specialUnitaryProjection, MonoidHom.range_comp, Subgroup.inclusion_range,
    specialUnitary_eq_subgroupOf]

@[expose] def projectiveSpecialUnitaryEquivImage (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    ProjectiveSpecialUnitary n K sigma ≃* (specialUnitaryProjection n K sigma).range :=
  (QuotientGroup.quotientMulEquivOfEq (specialUnitaryProjection_kernel n K sigma).symm).trans
    (QuotientGroup.quotientKerEquivRange (specialUnitaryProjection n K sigma))

theorem projectiveSpecialUnitaryEquivImage_mk (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : SUid sigma n) :
    (projectiveSpecialUnitaryEquivImage n K sigma (QuotientGroup.mk g)).val.val =
      ProjGenLinGroup.mk g.val := by
  rw [projectiveSpecialUnitaryEquivImage, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem projectiveSpecialUnitary_eq_stated (n : ℕ) (K : Type) [Field K]
    (sigma : K ≃+* K) :
    ProjectiveSpecialUnitary n K sigma = CFSG.Assembly.LowTwoRank.StatedProj (SUid sigma n) := rfl

end

end CFSG.ComponentClassification.CatalogueBGraphField
