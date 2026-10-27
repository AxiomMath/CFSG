module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicNine
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelAbelianization

open scoped Matrix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.DFour

open CFSG.Assembly.LowTwoRank (StatedQuadPlus StatedScalars)

@[expose] def blkMat (F : Type) [Field F] (p q : Fin 4) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F :=
  Matrix.of fun i j =>
    if i = .inl p then (if j = .inr q then 1 else 0)
    else if i = .inl q then (if j = .inr p then -1 else 0)
    else if i = .inr p then (if j = .inl q then 1 else 0) - (if j = .inr p then 1 else 0)
    else if i = .inr q then -(if j = .inr q then 1 else 0) - (if j = .inl p then 1 else 0)
    else (if i = j then 1 else 0)

def blkMatZ (p q : Fin 4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  Matrix.of fun i j =>
    if i = .inl p then (if j = .inr q then 1 else 0)
    else if i = .inl q then (if j = .inr p then -1 else 0)
    else if i = .inr p then (if j = .inl q then 1 else 0) - (if j = .inr p then 1 else 0)
    else if i = .inr q then -(if j = .inr q then 1 else 0) - (if j = .inl p then 1 else 0)
    else (if i = j then 1 else 0)

theorem blkMatZ_zero_one_cube :
    blkMatZ 0 1 * (blkMatZ 0 1 * blkMatZ 0 1) = 1 := by decide

theorem blkMatZ_two_three_cube :
    blkMatZ 2 3 * (blkMatZ 2 3 * blkMatZ 2 3) = 1 := by decide

theorem blkMatZ_comm : blkMatZ 0 1 * blkMatZ 2 3 = blkMatZ 2 3 * blkMatZ 0 1 := by decide

variable {F : Type} [Field F]

theorem blkMat_eq_mapMatrix (p q : Fin 4) :
    blkMat F p q = (Int.castRingHom F).mapMatrix (blkMatZ p q) := by
  ext i j
  simp [blkMat, blkMatZ, Int.cast_ite]

theorem blkMat_zero_one_cube : blkMat F 0 1 * (blkMat F 0 1 * blkMat F 0 1) = 1 := by
  rw [blkMat_eq_mapMatrix, ← map_mul, ← map_mul, blkMatZ_zero_one_cube, map_one]

theorem blkMat_two_three_cube : blkMat F 2 3 * (blkMat F 2 3 * blkMat F 2 3) = 1 := by
  rw [blkMat_eq_mapMatrix, ← map_mul, ← map_mul, blkMatZ_two_three_cube, map_one]

theorem blkMat_comm : blkMat F 0 1 * blkMat F 2 3 = blkMat F 2 3 * blkMat F 0 1 := by
  rw [blkMat_eq_mapMatrix, blkMat_eq_mapMatrix, ← map_mul, ← map_mul, blkMatZ_comm]

@[expose] def lmGL (F : Type) [Field F] : GL (Fin 4 ⊕ Fin 4) F :=
  ⟨blkMat F 0 1, blkMat F 0 1 * blkMat F 0 1, blkMat_zero_one_cube,
    (mul_assoc _ _ _).trans blkMat_zero_one_cube⟩

@[expose] def lpGL (F : Type) [Field F] : GL (Fin 4 ⊕ Fin 4) F :=
  ⟨blkMat F 2 3, blkMat F 2 3 * blkMat F 2 3, blkMat_two_three_cube,
    (mul_assoc _ _ _).trans blkMat_two_three_cube⟩

theorem coe_lmGL : ((lmGL F : GL (Fin 4 ⊕ Fin 4) F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) =
    blkMat F 0 1 := rfl

theorem coe_lpGL : ((lpGL F : GL (Fin 4 ⊕ Fin 4) F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) =
    blkMat F 2 3 := rfl

theorem lmGL_quad (v : Fin 4 ⊕ Fin 4 → F) :
    StatedQuadPlus 4 F ((lmGL F : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ v) =
      StatedQuadPlus 4 F v := by
  simp only [StatedQuadPlus, coe_lmGL, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_four, blkMat, Matrix.of_apply]
  simp
  ring

theorem lpGL_quad (v : Fin 4 ⊕ Fin 4 → F) :
    StatedQuadPlus 4 F ((lpGL F : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ v) =
      StatedQuadPlus 4 F v := by
  simp only [StatedQuadPlus, coe_lpGL, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_four, blkMat, Matrix.of_apply]
  simp
  ring

theorem lmGL_pow_three : (lmGL F) ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, coe_lmGL, pow_succ, pow_two, mul_assoc]
  exact blkMat_zero_one_cube

theorem lpGL_pow_three : (lpGL F) ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, coe_lpGL, pow_succ, pow_two, mul_assoc]
  exact blkMat_two_three_cube

theorem lmGL_lpGL_comm : lmGL F * lpGL F = lpGL F * lmGL F := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_lmGL, coe_lpGL]
  exact blkMat_comm

theorem lmGL_lpGL_independent (a b : ℕ)
    (h : (lmGL F) ^ a * (lpGL F) ^ b ∈ StatedScalars (Fin 4 ⊕ Fin 4) F) :
    3 ∣ a ∧ 3 ∣ b := by
  rw [pow_eq_pow_mod a lmGL_pow_three, pow_eq_pow_mod b lpGL_pow_three] at h
  obtain ⟨c, hc⟩ := h
  have h01 := congrArg (fun g : GL (Fin 4 ⊕ Fin 4) F =>
    (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) (.inl 0) (.inr 1)) hc
  have h23 := congrArg (fun g : GL (Fin 4 ⊕ Fin 4) F =>
    (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) (.inl 2) (.inr 3)) hc
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb] at h01 h23 <;>
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      coe_lmGL, coe_lpGL, pow_succ, blkMat, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_four] at h01 h23
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.DFour

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedOmega StatedQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open DFour

theorem mem_commutator_of_pow_three {G : Type*} [Group G] (O : Subgroup G)
    (hab : CFSG.IsElementaryAbelian 2 (Abelianization O)) {x : G} (hx : x ∈ O) (h3 : x ^ 3 = 1) :
    x ∈ ⁅O, O⁆ := by
  have h2 : ∀ a : Abelianization O, a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p 2 _)
  set y : O := ⟨x, hx⟩ with hy
  have hy3 : (Abelianization.of y) ^ 3 = 1 := by
    rw [← map_pow]
    have : y ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this, map_one]
  have hy1 : Abelianization.of y = 1 := by
    have h := h2 (Abelianization.of y)
    calc Abelianization.of y = (Abelianization.of y) ^ 3 * ((Abelianization.of y) ^ 2)⁻¹ := by
          group
      _ = 1 := by rw [hy3, h]; simp
  have hker : y ∈ commutator O := by
    rw [← Abelianization.ker_of]
    exact hy1
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨y, hker, rfl⟩

theorem exists_nine_of_POmegaPlus_four {X : Type} [Group X] {ℓ f : ℕ}
    (h : StatedClassicalModel X .POmegaPlus 4 ℓ f) :
    ∃ A : Subgroup X, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 ℓ f h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hmem : ∀ g : GL (Fin 4 ⊕ Fin 4) K,
      (∀ v, StatedQuadPlus 4 K ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) =
        StatedQuadPlus 4 K v) → g ^ 3 = 1 → g ∈ StatedOmega (StatedQuadPlus 4 K) := by
    intro g hg hg3
    rw [statedOmega_eq_comap (coe_quadPlus 4 K), Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    refine mem_commutator_of_pow_three _ hab.1 ?_ ?_
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      rw [toLinEquiv_apply, coe_quadPlus]
      exact hg v
    · rw [← map_pow, hg3, map_one]
  refine exists_isElemAbelian_of_mulEquiv e.symm
    (exists_nine_statedProj _ (lmGL K) (lpGL K) (hmem _ lmGL_quad lmGL_pow_three)
      (hmem _ lpGL_quad lpGL_pow_three) lmGL_pow_three lpGL_pow_three ?_ lmGL_lpGL_independent)
  rw [mul_assoc, lmGL_lpGL_comm]
  simp [mul_assoc]

end CFSG.LocalAnalysis.RankThreeTheoremC
