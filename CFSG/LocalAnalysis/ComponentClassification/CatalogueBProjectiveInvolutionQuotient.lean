module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionCharacter

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

open Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] def ordinaryCentralizerScalar (A : GL ι K) :
    Kˣ →* Subgroup.centralizer {A} where
  toFun c := ⟨GeneralLinearGroup.scalar ι c,
    Subgroup.mem_centralizer_singleton_iff.mpr (GeneralLinearGroup.scalar_commute c A)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' c d := Subtype.ext (map_mul _ c d)

theorem ordinaryCentralizerScalar_apply (A : GL ι K) (c : Kˣ) :
    (ordinaryCentralizerScalar A c).val = GeneralLinearGroup.scalar ι c := rfl

theorem ordinaryCentralizerScalar_range_le_center (A : GL ι K) :
    (ordinaryCentralizerScalar A).range ≤ Subgroup.center (Subgroup.centralizer {A}) := by
  rintro B ⟨c, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro D
  exact Subtype.ext (GeneralLinearGroup.scalar_commute c D.val).symm

instance ordinaryCentralizerScalar_range_normal (A : GL ι K) :
    (ordinaryCentralizerScalar A).range.Normal :=
  Subgroup.normal_of_le_center (ordinaryCentralizerScalar_range_le_center A)

theorem ordinaryCentralizerProjection_kernel_eq_scalar (A : GL ι K) :
    (ordinaryCentralizerProjection A).ker = (ordinaryCentralizerScalar A).range := by
  ext B
  constructor
  · intro hB
    have hmk : ProjGenLinGroup.mk B.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hB)
    have hcentral := ProjGenLinGroup.mk_eq_one.mp hmk
    rw [GeneralLinearGroup.center_eq_range_scalar] at hcentral
    obtain ⟨c, hc⟩ := hcentral
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change ProjGenLinGroup.mk (GeneralLinearGroup.scalar ι c) = 1
    apply ProjGenLinGroup.mk_eq_one.mpr
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩

@[expose] def ordinaryCentralizerScalarQuotientEquiv (A : GL ι K) :
    (Subgroup.centralizer {A} ⧸ (ordinaryCentralizerScalar A).range) ≃*
      (ordinaryCentralizerProjection A).range :=
  (QuotientGroup.quotientMulEquivOfEq (ordinaryCentralizerProjection_kernel_eq_scalar A).symm).trans
    (QuotientGroup.quotientKerEquivRange (ordinaryCentralizerProjection A))

theorem scalarRange_map_of_compatible {H : Type*} [Group H] (A : GL ι K)
    (e : Subgroup.centralizer {A} ≃* H) (s : Kˣ →* H)
    (hscalar : ∀ c, e (ordinaryCentralizerScalar A c) = s c) :
    (ordinaryCentralizerScalar A).range.map e.toMonoidHom = s.range := by
  rw [MonoidHom.map_range]
  exact congrArg MonoidHom.range (MonoidHom.ext hscalar)

theorem scalarRange_normal_of_compatible {H : Type*} [Group H] (A : GL ι K)
    (e : Subgroup.centralizer {A} ≃* H) (s : Kˣ →* H)
    (hscalar : ∀ c, e (ordinaryCentralizerScalar A c) = s c) : s.range.Normal := by
  rw [← scalarRange_map_of_compatible A e s hscalar]
  exact Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective

@[expose] def ordinaryCentralizerCoordinateQuotientEquiv {H : Type*} [Group H]
    (A : GL ι K) (e : Subgroup.centralizer {A} ≃* H) (s : Kˣ →* H)
    (hscalar : ∀ c, e (ordinaryCentralizerScalar A c) = s c) :
    letI : s.range.Normal := scalarRange_normal_of_compatible A e s hscalar
    (ordinaryCentralizerProjection A).range ≃* (H ⧸ s.range) := by
  letI : s.range.Normal := scalarRange_normal_of_compatible A e s hscalar
  exact (ordinaryCentralizerScalarQuotientEquiv A).symm.trans
    (QuotientGroup.congr _ _ e (scalarRange_map_of_compatible A e s hscalar))

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
