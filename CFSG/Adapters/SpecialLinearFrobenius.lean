module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.FieldCoordinates
public import TauCeti.GroupTheory.FixedSubgroup

public section

noncomputable section

namespace CFSG.ClassicalModels

open Matrix TauCeti

theorem specialLinear_mem_range_galoisFieldEmbedding_iff
    (d : ValidLieTypeIndex) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SpecialLinearGroup ι d.Closure) :
    g ∈ (SpecialLinearGroup.map (n := ι) d.galoisFieldEmbedding).range ↔
      ∀ i j, (g i j) ^ d.fieldOrder = g i j := by
  constructor
  · rintro ⟨g₀, rfl⟩ i j
    exact d.mem_range_galoisFieldEmbedding_iff.mp
      ⟨g₀ i j, rfl⟩
  · intro hg
    obtain ⟨A, hA⟩ := (Matrix.exists_map_galoisFieldEmbedding_iff_frobenius
      (d := d) (g : Matrix ι ι d.Closure)).mpr hg
    have hdet : A.det = 1 := by
      apply d.galoisFieldEmbedding.injective
      calc
        d.galoisFieldEmbedding A.det = (A.map d.galoisFieldEmbedding).det :=
          d.galoisFieldEmbedding.map_det A
        _ = (g : Matrix ι ι d.Closure).det := congrArg Matrix.det hA
        _ = 1 := g.property
        _ = d.galoisFieldEmbedding 1 := (map_one _).symm
    refine ⟨⟨A, hdet⟩, ?_⟩
    apply Subtype.ext
    exact hA

theorem specialLinear_map_galoisFieldEmbedding_injective
    (d : ValidLieTypeIndex) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Function.Injective (SpecialLinearGroup.map (n := ι) d.galoisFieldEmbedding) := by
  intro A B hAB
  apply Subtype.ext
  ext i j
  apply d.galoisFieldEmbedding.injective
  exact congrArg (fun g : SpecialLinearGroup ι d.Closure => g i j) hAB

theorem specialLinear_mem_fixedSubgroup_frobenius_iff
    (d : ValidLieTypeIndex) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SpecialLinearGroup ι d.Closure) :
    g ∈ fixedSubgroup (SpecialLinearGroup.map (n := ι)
      (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) ↔
      ∀ i j, (g i j) ^ d.fieldOrder = g i j := by
  rw [mem_fixedSubgroup]
  constructor
  · intro hg i j
    have hentry := congrArg (fun A : SpecialLinearGroup ι d.Closure => A i j) hg
    change iterateFrobenius d.Closure d.characteristic d.fieldExponent (g i j) = g i j
      at hentry
    simpa only [iterateFrobenius_def, d.fieldOrder_eq_characteristic_pow] using hentry
  · intro hg
    apply Subtype.ext
    ext i j
    change iterateFrobenius d.Closure d.characteristic d.fieldExponent (g i j) = g i j
    simpa only [iterateFrobenius_def, d.fieldOrder_eq_characteristic_pow] using hg i j

theorem specialLinear_range_galoisFieldEmbedding_eq_fixedSubgroup
    (d : ValidLieTypeIndex) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (SpecialLinearGroup.map (n := ι) d.galoisFieldEmbedding).range =
      fixedSubgroup (SpecialLinearGroup.map (n := ι)
        (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) := by
  ext g
  rw [specialLinear_mem_range_galoisFieldEmbedding_iff,
    specialLinear_mem_fixedSubgroup_frobenius_iff]

@[expose] def specialLinearFrobeniusEmbedding
    (d : ValidLieTypeIndex) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SpecialLinearGroup ι (GaloisField d.characteristic d.fieldExponent) →*
      fixedSubgroup (SpecialLinearGroup.map (n := ι)
        (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) where
  toFun g := ⟨SpecialLinearGroup.map d.galoisFieldEmbedding g, by
    rw [← specialLinear_range_galoisFieldEmbedding_eq_fixedSubgroup]
    exact ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

theorem specialLinearFrobeniusEmbedding_bijective
    (d : ValidLieTypeIndex) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Function.Bijective (specialLinearFrobeniusEmbedding d ι) := by
  constructor
  · intro g h heq
    apply specialLinear_map_galoisFieldEmbedding_injective d
    exact congrArg Subtype.val heq
  · intro g
    have hg : (g : SpecialLinearGroup ι d.Closure) ∈
        (SpecialLinearGroup.map (n := ι) d.galoisFieldEmbedding).range :=
      (specialLinear_range_galoisFieldEmbedding_eq_fixedSubgroup d).symm.le g.property
    obtain ⟨h, hh⟩ := hg
    exact ⟨h, Subtype.ext hh⟩

@[expose] def specialLinearEquivFrobeniusFixedPoints
    (d : ValidLieTypeIndex) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SpecialLinearGroup ι (GaloisField d.characteristic d.fieldExponent) ≃*
      fixedSubgroup (SpecialLinearGroup.map (n := ι)
        (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) :=
  MulEquiv.ofBijective (specialLinearFrobeniusEmbedding d ι)
    (specialLinearFrobeniusEmbedding_bijective d ι)

theorem specialLinearEquivFrobeniusFixedPoints_coe
    (d : ValidLieTypeIndex) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (g : SpecialLinearGroup ι (GaloisField d.characteristic d.fieldExponent)) :
    ((specialLinearEquivFrobeniusFixedPoints d ι g : SpecialLinearGroup ι d.Closure) :
      Matrix ι ι d.Closure) = (g : Matrix ι ι _).map d.galoisFieldEmbedding := rfl

end CFSG.ClassicalModels
