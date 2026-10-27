module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

namespace RootPair

section Plane

variable {r : ℕ} {K : Type} [Field K]

theorem spForm_antisymm (x y : Fin r ⊕ Fin r → K) : spForm r K y x = - spForm r K x y := by
  have h := spForm_isAlt (r := r) (K := K) (x + y)
  simp only [map_add, LinearMap.add_apply, spForm_isAlt x, spForm_isAlt y] at h
  linear_combination h

@[expose] noncomputable def planeProj (e f y : Fin r ⊕ Fin r → K) : Fin 2 → K :=
  ![spForm r K y f, - spForm r K y e]

@[expose] noncomputable def planeEmb (e f : Fin r ⊕ Fin r → K) (a : Fin 2 → K) :
    Fin r ⊕ Fin r → K :=
  a 0 • e + a 1 • f

@[expose] noncomputable def planeExt (e f : Fin r ⊕ Fin r → K) (g : Matrix (Fin 2) (Fin 2) K)
    (y : Fin r ⊕ Fin r → K) : Fin r ⊕ Fin r → K :=
  y + planeEmb e f ((g - 1) *ᵥ planeProj e f y)

theorem exists_spEnd_eq' {u v : Fin r ⊕ Fin r → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ s : StatedSp r K, spEnd s u = v := by
  obtain ⟨l, -, hl⟩ :=
    (CFSG.ClassicalGroups.Alternating.alternating_transvection_vector_transitivity
      (spForm_isAlt (r := r) (K := K)) spForm_nondegenerate).1 u v hu hv
  refine ⟨(l.map fun p => spTransvection p.1 p.2).prod, ?_⟩
  have hlin : spLin r K (l.map fun p => spTransvection p.1 p.2).prod =
      (l.map fun p => CFSG.ClassicalGroups.Alternating.symplecticTransvection (spForm r K)
        spForm_isAlt p.1 p.2).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    exact spLin_spTransvection p.1 p.2
  change ((spLin r K (l.map fun p => spTransvection p.1 p.2).prod :
    LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) u = v
  rw [hlin]
  exact hl

variable {e f : Fin r ⊕ Fin r → K}

theorem planeProj_add (y z : Fin r ⊕ Fin r → K) :
    planeProj e f (y + z) = planeProj e f y + planeProj e f z := by
  ext i
  fin_cases i
  · simp [planeProj, map_add, LinearMap.add_apply]
  · simp [planeProj, map_add, LinearMap.add_apply]
    ring

theorem planeProj_smul (c : K) (y : Fin r ⊕ Fin r → K) :
    planeProj e f (c • y) = c • planeProj e f y := by
  ext i
  fin_cases i <;> simp [planeProj, map_smul]

theorem planeEmb_add (a b : Fin 2 → K) :
    planeEmb e f (a + b) = planeEmb e f a + planeEmb e f b := by
  simp only [planeEmb, Pi.add_apply, add_smul]
  abel

theorem planeEmb_smul (c : K) (a : Fin 2 → K) :
    planeEmb e f (c • a) = c • planeEmb e f a := by
  simp only [planeEmb, Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]

theorem planeProj_emb (hef : spForm r K e f = 1) (a : Fin 2 → K) :
    planeProj e f (planeEmb e f a) = a := by
  have hfe : spForm r K f e = -1 := by rw [spForm_antisymm e f, hef]
  have hee : spForm r K e e = 0 := spForm_isAlt e
  have hff : spForm r K f f = 0 := spForm_isAlt f
  ext i
  fin_cases i <;> simp [planeProj, planeEmb, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, hef, hfe, hee, hff]

theorem planeProj_ext (hef : spForm r K e f = 1) (g : Matrix (Fin 2) (Fin 2) K)
    (y : Fin r ⊕ Fin r → K) : planeProj e f (planeExt e f g y) = g *ᵥ planeProj e f y := by
  rw [planeExt, planeProj_add, planeProj_emb hef, sub_mulVec, one_mulVec]
  abel

theorem planeExt_mul (hef : spForm r K e f = 1) (g g' : Matrix (Fin 2) (Fin 2) K)
    (y : Fin r ⊕ Fin r → K) :
    planeExt e f (g * g') y = planeExt e f g (planeExt e f g' y) := by
  have hz : planeProj e f (planeExt e f g' y) = g' *ᵥ planeProj e f y := planeProj_ext hef g' y
  have key : (g * g' - 1) *ᵥ planeProj e f y =
      (g' - 1) *ᵥ planeProj e f y + (g - 1) *ᵥ (g' *ᵥ planeProj e f y) := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have h1 : planeExt e f g (planeExt e f g' y) =
      planeExt e f g' y + planeEmb e f ((g - 1) *ᵥ planeProj e f (planeExt e f g' y)) := rfl
  have h2 : planeExt e f g' y = y + planeEmb e f ((g' - 1) *ᵥ planeProj e f y) := rfl
  rw [h1, hz, h2]
  show y + planeEmb e f ((g * g' - 1) *ᵥ planeProj e f y) = _
  rw [key, planeEmb_add]
  abel

theorem planeExt_one (y : Fin r ⊕ Fin r → K) : planeExt e f 1 y = y := by
  simp [planeExt, planeEmb]

theorem spForm_planeEmb_left (a : Fin 2 → K) (z : Fin r ⊕ Fin r → K) :
    spForm r K (planeEmb e f a) z = a 0 * planeProj e f z 1 - a 1 * planeProj e f z 0 := by
  have h1 := spForm_antisymm (r := r) (K := K) e z
  have h2 := spForm_antisymm (r := r) (K := K) f z
  simp only [planeEmb, planeProj, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, h1, h2]
  ring

theorem spForm_planeEmb_right (a : Fin 2 → K) (z : Fin r ⊕ Fin r → K) :
    spForm r K z (planeEmb e f a) = -(a 0 * planeProj e f z 1 - a 1 * planeProj e f z 0) := by
  rw [spForm_antisymm (r := r) (K := K) (planeEmb e f a) z, spForm_planeEmb_left]

theorem spForm_planeEmb_planeEmb (hef : spForm r K e f = 1) (a b : Fin 2 → K) :
    spForm r K (planeEmb e f a) (planeEmb e f b) = a 0 * b 1 - a 1 * b 0 := by
  rw [spForm_planeEmb_left, planeProj_emb hef]

theorem plane_alg {g : Matrix (Fin 2) (Fin 2) K} (hg : g.det = 1) (X Y : Fin 2 → K) :
    -(((g - 1) *ᵥ Y) 0 * X 1 - ((g - 1) *ᵥ Y) 1 * X 0) +
      (((g - 1) *ᵥ X) 0 * Y 1 - ((g - 1) *ᵥ X) 1 * Y 0) +
      (((g - 1) *ᵥ X) 0 * ((g - 1) *ᵥ Y) 1 - ((g - 1) *ᵥ X) 1 * ((g - 1) *ᵥ Y) 0) = 0 := by
  rw [Matrix.det_fin_two] at hg
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]
  simp
  linear_combination (X 0 * Y 1 - X 1 * Y 0) * hg

theorem spForm_planeExt (hef : spForm r K e f = 1) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g.det = 1) (y z : Fin r ⊕ Fin r → K) :
    spForm r K (planeExt e f g y) (planeExt e f g z) = spForm r K y z := by
  have h := plane_alg hg (planeProj e f y) (planeProj e f z)
  simp only [planeExt, map_add, LinearMap.add_apply, spForm_planeEmb_left,
    spForm_planeEmb_right, planeProj_emb hef]
  linear_combination h

@[expose] noncomputable def planeExtLin (e f : Fin r ⊕ Fin r → K) (g : Matrix (Fin 2) (Fin 2) K) :
    (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) where
  toFun := planeExt e f g
  map_add' y z := by
    simp only [planeExt, planeProj_add, Matrix.mulVec_add, planeEmb_add]
    abel
  map_smul' c y := by
    simp only [planeExt, planeProj_smul, Matrix.mulVec_smul, planeEmb_smul, smul_add,
      RingHom.id_apply]

@[expose] noncomputable def planeGL (hef : spForm r K e f = 1) (g : SpecialLinearGroup (Fin 2) K) :
    LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) where
  val := planeExtLin e f g
  inv := planeExtLin e f (g⁻¹ : SpecialLinearGroup (Fin 2) K)
  val_inv := LinearMap.ext fun y => by
    change planeExt e f (g : Matrix (Fin 2) (Fin 2) K)
      (planeExt e f ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) y) = y
    rw [← planeExt_mul hef, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, planeExt_one]
  inv_val := LinearMap.ext fun y => by
    change planeExt e f ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      (planeExt e f (g : Matrix (Fin 2) (Fin 2) K) y) = y
    rw [← planeExt_mul hef, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, planeExt_one]

theorem planeGL_apply (hef : spForm r K e f = 1) (g : SpecialLinearGroup (Fin 2) K)
    (y : Fin r ⊕ Fin r → K) :
    (planeGL hef g : Module.End K (Fin r ⊕ Fin r → K)) y =
      planeExt e f (g : Matrix (Fin 2) (Fin 2) K) y := rfl

@[expose] noncomputable def planeHom (hef : spForm r K e f = 1) :
    SpecialLinearGroup (Fin 2) K →* LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) where
  toFun := planeGL hef
  map_one' := Units.ext (LinearMap.ext fun y => by
    rw [planeGL_apply]
    simp [planeExt_one])
  map_mul' g g' := Units.ext (LinearMap.ext fun y => by
    change planeExt e f ((g * g' : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) y =
      planeExt e f (g : Matrix (Fin 2) (Fin 2) K)
        (planeExt e f (g' : Matrix (Fin 2) (Fin 2) K) y)
    rw [Matrix.SpecialLinearGroup.coe_mul, planeExt_mul hef])

theorem planeHom_mem (hef : spForm r K e f = 1) (g : SpecialLinearGroup (Fin 2) K) :
    planeHom hef g ∈ sesqUnitaryGroup (spForm r K) := by
  rw [mem_sesqUnitaryGroup]
  intro y z
  exact spForm_planeExt hef g.2 y z

@[expose] noncomputable def spSL2Hom (hef : spForm r K e f = 1) :
    SpecialLinearGroup (Fin 2) K →* StatedSp r K :=
  ((MonoidHom.ofInjective (spLin_injective (r := r) (K := K))).symm.toMonoidHom).comp
    ((planeHom hef).codRestrict (spLin r K).range fun g => by
      rw [range_spLin]; exact planeHom_mem hef g)

theorem spLin_spSL2Hom (hef : spForm r K e f = 1) (g : SpecialLinearGroup (Fin 2) K) :
    spLin r K (spSL2Hom hef g) = planeHom hef g := by
  change spLin r K ((MonoidHom.ofInjective (spLin_injective (r := r) (K := K))).symm
    ⟨planeHom hef g, _⟩) = _
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective (spLin_injective (r := r) (K := K))).apply_symm_apply
      ⟨planeHom hef g, _⟩)

theorem spEnd_spSL2Hom (hef : spForm r K e f = 1) (g : SpecialLinearGroup (Fin 2) K)
    (y : Fin r ⊕ Fin r → K) :
    spEnd (spSL2Hom hef g) y = planeExt e f (g : Matrix (Fin 2) (Fin 2) K) y := by
  change ((spLin r K (spSL2Hom hef g) : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K)) y = _
  rw [spLin_spSL2Hom]
  rfl

theorem spSL2Hom_u2 (hef : spForm r K e f = 1) (x : K) :
    spSL2Hom hef (u2 x) = spTransvection e (-x) := by
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spSL2Hom hef (u2 x)) y = spEnd (spTransvection e (-x)) y
  rw [spEnd_spSL2Hom, spEnd_spTransvection]
  simp [planeExt, planeEmb, planeProj, u2_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem spSL2Hom_l2 (hef : spForm r K e f = 1) (x : K) :
    spSL2Hom hef (l2 x) = spTransvection f x := by
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spSL2Hom hef (l2 x)) y = spEnd (spTransvection f x) y
  rw [spEnd_spSL2Hom, spEnd_spTransvection]
  simp [planeExt, planeEmb, planeProj, l2_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end Plane

end RootPair

end CFSG.LieType.SeitzGeneration
