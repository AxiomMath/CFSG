module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LTheta
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LBlocks
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix

theorem Theta_one (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))] :
    Theta (1 : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) = 1 := by
  ext a b
  have h : ∀ p q : Fin 2 × Fin 2,
      ThetaP (1 : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) p q =
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) p q := by
    intro p q
    by_cases h1 : p.1 = q.1
    · simp [ThetaP, h1, Matrix.one_apply, Prod.ext_iff]
    · simp [ThetaP, h1, Matrix.one_apply, Prod.ext_iff]
  simp only [Theta, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [h]
  simp [Matrix.one_apply, eps.apply_eq_iff_eq]

@[expose] noncomputable def ThetaMon (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))] :
    Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)) →* Matrix (Fin 4) (Fin 4) K where
  toFun := Theta
  map_one' := Theta_one K
  map_mul' := fun X Y => Theta_mul X Y

@[expose] noncomputable def dT (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))] :
    Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)) →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp
    ((Units.map (ThetaMon K)).comp Matrix.SpecialLinearGroup.toGL)

theorem dT_val (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (X : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) :
    ((dT K X : Kˣ) : K) = (Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))).det := by
  simp [dT, ThetaMon, Matrix.GeneralLinearGroup.det, Matrix.SpecialLinearGroup.toGL]

theorem root_quad (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))] :
    AdjoinRoot.root (KA7.quad K) ^ 2 + AdjoinRoot.root (KA7.quad K) + 1 = 0 :=
  KA7.zetaQ_quad K

theorem L4 (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) :
    ∃ s : Finset (AdjoinRoot (KA7.quad K)), s.card = 4 := by
  set w := AdjoinRoot.root (KA7.quad K) with hwdef
  have hw : w ^ 2 + w + 1 = 0 := root_quad K
  have h3K : (3 : K) ≠ 0 := by
    intro h
    apply hnr 1
    linear_combination h
  have h3 : (3 : AdjoinRoot (KA7.quad K)) ≠ 0 := by
    intro h
    apply h3K
    exact (algebraMap K (AdjoinRoot (KA7.quad K))).injective
      ((map_ofNat _ 3).trans (h.trans (map_zero _).symm))
  have n01 : (0 : AdjoinRoot (KA7.quad K)) ≠ 1 := zero_ne_one
  have n0w : (0 : AdjoinRoot (KA7.quad K)) ≠ w := by
    intro h
    rw [← h] at hw
    norm_num at hw
  have n0w1 : (0 : AdjoinRoot (KA7.quad K)) ≠ w + 1 := by
    intro h
    have : w = -1 := by linear_combination -h
    rw [this] at hw
    apply (one_ne_zero : (1 : AdjoinRoot (KA7.quad K)) ≠ 0)
    linear_combination hw
  have n1w : (1 : AdjoinRoot (KA7.quad K)) ≠ w := by
    intro h
    rw [← h] at hw
    apply h3
    linear_combination hw
  have n1w1 : (1 : AdjoinRoot (KA7.quad K)) ≠ w + 1 := by
    intro h
    apply n0w
    linear_combination h
  have nww1 : w ≠ w + 1 := by
    intro h
    have h1 : (1 : AdjoinRoot (KA7.quad K)) = 0 := by linear_combination -h
    exact (one_ne_zero : (1 : AdjoinRoot (KA7.quad K)) ≠ 0) h1
  refine ⟨{0, 1, w, w + 1}, ?_⟩
  rw [Finset.card_insert_of_notMem (by simp [n01, n0w, n0w1]),
    Finset.card_insert_of_notMem (by simp [n1w, n1w1]),
    Finset.card_pair nww1]

theorem isQuasisimple_SL2 (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) :
    CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) := by
  obtain ⟨s, hs⟩ := L4 K hnr
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := AdjoinRoot (KA7.quad K)) (n := 2) le_rfl
      (Or.inr ⟨s, hs⟩)
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := AdjoinRoot (KA7.quad K)) (n := 2) le_rfl
      (Or.inr ⟨s, hs⟩)
  exact ⟨Group.isPerfect_def.mp hperf, hsimple⟩

theorem dT_eq_one (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) : dT K X = 1 := by
  obtain ⟨s, hs⟩ := L4 K hnr
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := AdjoinRoot (KA7.quad K)) (n := 2) le_rfl
      (Or.inr ⟨s, hs⟩)
  have hle : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)))),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))))⁆ ≤
      (dT K).ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have htop := Group.isPerfect_def.mp hperf
  have hX : X ∈ (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)))) :=
    Subgroup.mem_top X
  rw [← htop] at hX
  exact (MonoidHom.mem_ker).mp (hle hX)

theorem det_Theta_SL (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) :
    (Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))).det = 1 := by
  rw [← dT_val, dT_eq_one K hnr X, Units.val_one]

@[expose] noncomputable def Psi (K : Type) [Field K] [Fact (Irreducible (KA7.quad K))]
    (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K)) →*
      Matrix.SpecialLinearGroup (Fin 6) K where
  toFun X := ⟨blk6 (Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))) 1, by
    unfold blk6
    rw [Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one, det_Theta_SL K hnr X]⟩
  map_one' := by
    apply Subtype.ext
    simp [Matrix.SpecialLinearGroup.coe_one, Theta_one, blk6_one]
  map_mul' X Y := by
    apply Subtype.ext
    show blk6 (Theta ((X * Y : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (KA7.quad K))) :
        Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))) 1 =
      blk6 (Theta (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))) 1 *
        blk6 (Theta (Y : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)))) 1
    rw [Matrix.SpecialLinearGroup.coe_mul, Theta_mul, ← blk6_mul, Matrix.mul_one]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
