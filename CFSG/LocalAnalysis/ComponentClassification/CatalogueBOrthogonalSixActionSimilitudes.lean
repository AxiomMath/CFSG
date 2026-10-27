module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModel

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

theorem six_multiplier_unique (delta : K) (g : GL (Fin 4) (extension delta)) (a b : Kˣ)
    (ha : (sixBar delta g.val).transpose * sixGram (extension delta) * g.val =
      (a : K) • sixGram (extension delta))
    (hb : (sixBar delta g.val).transpose * sixGram (extension delta) * g.val =
      (b : K) • sixGram (extension delta)) : a = b := by
  apply Units.ext
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (extension delta) => (M 0 2).re)
    (ha.symm.trans hb)
  simpa [sixGram, QuadraticAlgebra.re_smul, QuadraticAlgebra.re_one, smul_eq_mul] using h

theorem six_similitude_product (delta : K) (g h : GL (Fin 4) (extension delta)) (a b : Kˣ)
    (hg : (sixBar delta g.val).transpose * sixGram (extension delta) * g.val =
      (a : K) • sixGram (extension delta))
    (hh : (sixBar delta h.val).transpose * sixGram (extension delta) * h.val =
      (b : K) • sixGram (extension delta)) :
    (sixBar delta (g * h).val).transpose * sixGram (extension delta) * (g * h).val =
      ((a * b : Kˣ) : K) • sixGram (extension delta) := by
  change (sixBar delta (g.val * h.val)).transpose * _ * (g.val * h.val) = _
  rw [sixBar_mul, Matrix.transpose_mul]
  calc
    (sixBar delta h.val).transpose * (sixBar delta g.val).transpose *
        sixGram (extension delta) * (g.val * h.val) =
        (sixBar delta h.val).transpose *
          ((sixBar delta g.val).transpose * sixGram (extension delta) * g.val) * h.val := by
      simp only [Matrix.mul_assoc]
    _ = (a : K) • ((sixBar delta h.val).transpose * sixGram (extension delta) * h.val) := by
      rw [hg, Matrix.mul_smul, Matrix.smul_mul]
    _ = ((a * b : Kˣ) : K) • sixGram (extension delta) := by rw [hh, smul_smul]; rfl

theorem six_similitude_inverse (delta : K) (g : GL (Fin 4) (extension delta)) (a : Kˣ)
    (hg : (sixBar delta g.val).transpose * sixGram (extension delta) * g.val =
      (a : K) • sixGram (extension delta)) :
    (sixBar delta g⁻¹.val).transpose * sixGram (extension delta) * g⁻¹.val =
      ((a⁻¹ : Kˣ) : K) • sixGram (extension delta) := by
  have ht : (sixBar delta g⁻¹.val).transpose * (sixBar delta g.val).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← sixBar_mul, Units.mul_inv]
    apply Matrix.ext
    intro i j
    simp [sixBar, Matrix.one_apply, eq_comm]
  have hH : sixGram (extension delta) = (a : K) •
      ((sixBar delta g⁻¹.val).transpose * sixGram (extension delta) * g⁻¹.val) := by
    calc
      sixGram (extension delta) = (sixBar delta g⁻¹.val).transpose *
          ((sixBar delta g.val).transpose * sixGram (extension delta) * g.val) * g⁻¹.val := by
        calc
          sixGram (extension delta) =
              ((sixBar delta g⁻¹.val).transpose * (sixBar delta g.val).transpose) *
                sixGram (extension delta) * (g.val * g⁻¹.val) := by
            rw [ht, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  have hs := congrArg
    (fun M : Matrix (Fin 4) (Fin 4) (extension delta) => ((a⁻¹ : Kˣ) : K) • M) hH
  simpa [smul_smul] using hs.symm

@[expose] def sixSimilitudes (delta : K) : Subgroup (GL (Fin 4) (extension delta)) where
  carrier := {g | ∃ a : Kˣ,
    (sixBar delta g.val).transpose * sixGram (extension delta) * g.val =
      (a : K) • sixGram (extension delta) ∧
    g.val.det = algebraMap K (extension delta) ((a : K) ^ 2)}
  one_mem' := ⟨1, by simp [sixBar], by simp⟩
  mul_mem' := by
    rintro g h ⟨a, ha, hda⟩ ⟨b, hb, hdb⟩
    refine ⟨a * b, six_similitude_product delta g h a b ha hb, ?_⟩
    change (g.val * h.val).det = _
    rw [Matrix.det_mul, hda, hdb, ← map_mul, Units.val_mul, mul_pow]
  inv_mem' := by
    rintro g ⟨a, ha, hda⟩
    refine ⟨a⁻¹, six_similitude_inverse delta g a ha, ?_⟩
    have hu : GeneralLinearGroup.det g =
        Units.map (algebraMap K (extension delta)) (a ^ 2) := by
      apply Units.ext
      exact hda
    change ((GeneralLinearGroup.det g⁻¹ : (extension delta)ˣ) : extension delta) = _
    rw [map_inv, hu, ← map_inv]
    rfl

@[expose] def sixMultiplier (delta : K) : sixSimilitudes delta →* Kˣ where
  toFun g := Classical.choose g.property
  map_one' := six_multiplier_unique delta 1 _ 1
    (Classical.choose_spec (1 : sixSimilitudes delta).property).1 (by simp [sixBar])
  map_mul' g h := six_multiplier_unique delta (g.val * h.val) _ _
    (Classical.choose_spec (g * h).property).1
    (six_similitude_product delta g.val h.val _ _
      (Classical.choose_spec g.property).1 (Classical.choose_spec h.property).1)

theorem sixMultiplier_spec (delta : K) (g : sixSimilitudes delta) :
    (sixBar delta g.val.val).transpose * sixGram (extension delta) * g.val.val =
      (sixMultiplier delta g : K) • sixGram (extension delta) :=
  (Classical.choose_spec g.property).1

theorem sixMultiplier_det (delta : K) (g : sixSimilitudes delta) :
    g.val.val.det = algebraMap K (extension delta) ((sixMultiplier delta g : K) ^ 2) :=
  (Classical.choose_spec g.property).2

theorem sixMultiplier_eq_of_equation (delta : K) (g : sixSimilitudes delta) (a : Kˣ)
    (ha : (sixBar delta g.val.val).transpose * sixGram (extension delta) * g.val.val =
      (a : K) • sixGram (extension delta)) : sixMultiplier delta g = a :=
  six_multiplier_unique delta g.val _ _ (sixMultiplier_spec delta g) ha

@[expose] def sixSpecialUnitary (delta : K) : Subgroup (GL (Fin 4) (extension delta)) where
  carrier := {g | (sixBar delta g.val).transpose * sixGram (extension delta) * g.val =
    sixGram (extension delta) ∧ g.val.det = 1}
  one_mem' := by simp [sixBar]
  mul_mem' := by
    rintro g h ⟨hg, hdg⟩ ⟨hh, hdh⟩
    constructor
    · simpa using six_similitude_product delta g h 1 1 (by simpa using hg) (by simpa using hh)
    · change (g.val * h.val).det = 1
      rw [Matrix.det_mul, hdg, hdh, one_mul]
  inv_mem' := by
    rintro g ⟨hg, hdg⟩
    constructor
    · simpa using six_similitude_inverse delta g 1 (by simpa using hg)
    · have hu : GeneralLinearGroup.det g = 1 := Units.ext hdg
      change ((GeneralLinearGroup.det g⁻¹ : (extension delta)ˣ) : extension delta) = 1
      rw [map_inv, hu, inv_one, Units.val_one]

theorem sixSpecialUnitary_le_similitudes (delta : K) :
    sixSpecialUnitary delta ≤ sixSimilitudes delta := by
  intro g hg
  exact ⟨1, by simpa using hg.1, by simpa using hg.2⟩

@[expose] def sixSpecialInclusion (delta : K) : sixSpecialUnitary delta →* sixSimilitudes delta :=
  Subgroup.inclusion (sixSpecialUnitary_le_similitudes delta)

theorem sixMultiplier_kernel_iff (delta : K) (g : sixSimilitudes delta) :
    g ∈ (sixMultiplier delta).ker ↔ g.val ∈ sixSpecialUnitary delta := by
  constructor
  · intro hg
    have hmu := (sixMultiplier delta).mem_ker.mp hg
    constructor
    · rw [sixMultiplier_spec, hmu]
      simp
    · rw [sixMultiplier_det, hmu]
      simp
  · intro hg
    apply (sixMultiplier delta).mem_ker.mpr
    apply sixMultiplier_eq_of_equation
    simpa using hg.1

theorem sixSpecialInclusion_range (delta : K) :
    (sixSpecialInclusion delta).range = (sixMultiplier delta).ker := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨h, rfl⟩
    exact (sixMultiplier_kernel_iff delta _).mpr h.property
  · intro hg
    exact ⟨⟨g.val, (sixMultiplier_kernel_iff delta g).mp hg⟩, Subtype.ext rfl⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
