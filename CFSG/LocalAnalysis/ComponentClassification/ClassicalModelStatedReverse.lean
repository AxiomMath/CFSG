module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public noncomputable section

namespace CFSG.ComponentClassification.ClassicalModelStatedBridge

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv glFieldEquiv_scalar)

section Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K L : Type} [Field K] [Field L]

theorem coe_glFieldEquiv (e : K ≃+* L) (A : GL ι K) :
    ((glFieldEquiv ι e A : GL ι L) : Matrix ι ι L) = e.mapMatrix (A : Matrix ι ι K) :=
  rfl

theorem map_statedScalars (e : K ≃+* L) :
    (StatedScalars ι K).map (glFieldEquiv ι e : GL ι K →* GL ι L) = StatedScalars ι L := by
  ext A
  constructor
  · rintro ⟨B, ⟨c, rfl⟩, rfl⟩
    exact ⟨Units.map e.toMonoidHom c, (glFieldEquiv_scalar ι e c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨GeneralLinearGroup.scalar ι (Units.map e.symm.toMonoidHom c), ⟨_, rfl⟩, ?_⟩
    change glFieldEquiv ι e (GeneralLinearGroup.scalar ι _) = _
    rw [glFieldEquiv_scalar]
    congr 1
    ext
    simp

@[expose] def statedProjCongr {ι' : Type} [Fintype ι'] [DecidableEq ι']
    (e : GL ι K ≃* GL ι' L) {H : Subgroup (GL ι K)} {H' : Subgroup (GL ι' L)}
    (hH : H.map (e : GL ι K →* GL ι' L) = H')
    (hZ : (StatedScalars ι K).map (e : GL ι K →* GL ι' L) = StatedScalars ι' L) :
    StatedProj H ≃* StatedProj H' :=
  QuotientGroup.congr _ _ ((e.subgroupMap H).trans (MulEquiv.subgroupCongr hH)) (by
    set φ := (e.subgroupMap H).trans (MulEquiv.subgroupCongr hH)
    have hφ : ∀ y : H, ((φ y : H') : GL ι' L) = e y := fun y => rfl
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf, ← hZ]
      exact ⟨y, hy, (hφ y).symm⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf, ← hZ] at hx
      obtain ⟨a, ha, hax⟩ := hx
      refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have hsymm : e ((φ.symm x : H) : GL ι K) = x := by
        rw [← hφ]
        exact congrArg Subtype.val (φ.apply_symm_apply x)
      have : ((φ.symm x : H) : GL ι K) = a := e.injective (hsymm.trans hax.symm)
      rw [this]
      exact ha)

theorem map_closure_of_iff {ι' : Type} [Fintype ι'] [DecidableEq ι'] (e : GL ι K ≃* GL ι' L)
    {s : Set (GL ι K)} {t : Set (GL ι' L)} (h : ∀ A, e A ∈ t ↔ A ∈ s) :
    (Subgroup.closure s).map (e : GL ι K →* GL ι' L) = Subgroup.closure t := by
  rw [MonoidHom.map_closure]
  congr 1
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (h A).mpr hA
  · intro hB
    refine ⟨e.symm B, (h _).mp ?_, e.apply_symm_apply B⟩
    rw [MulEquiv.apply_symm_apply]
    exact hB

theorem det_mapMatrix (e : K ≃+* L) (M : Matrix ι ι K) : (e.mapMatrix M).det = e M.det :=
  (RingHom.map_det e.toRingHom M).symm

theorem transpose_mapMatrix (e : K ≃+* L) (M : Matrix ι ι K) :
    (e.mapMatrix M)ᵀ = e.mapMatrix Mᵀ :=
  rfl

theorem mapMatrix_eq_one_iff (e : K ≃+* L) (M : Matrix ι ι K) : e.mapMatrix M = 1 ↔ M = 1 := by
  rw [← map_one e.mapMatrix, e.mapMatrix.injective.eq_iff]

theorem map_statedSL (n : ℕ) (e : K ≃+* L) :
    (StatedSL n K).map (glFieldEquiv (Fin n) e : GL (Fin n) K →* GL (Fin n) L) =
      StatedSL n L := by
  refine map_closure_of_iff _ fun A => ?_
  change (e.mapMatrix (A : Matrix (Fin n) (Fin n) K)).det = 1 ↔
    (A : Matrix (Fin n) (Fin n) K).det = 1
  rw [det_mapMatrix, ← map_one e, e.injective.eq_iff]

theorem mapMatrix_map_pow (e : K ≃+* L) (q : ℕ) (M : Matrix ι ι K) :
    (e.mapMatrix M).map (· ^ q) = e.mapMatrix (M.map (· ^ q)) := by
  ext i j
  simp

theorem map_statedSU (n q : ℕ) (e : K ≃+* L) :
    (StatedSU n q K).map (glFieldEquiv (Fin n) e : GL (Fin n) K →* GL (Fin n) L) =
      StatedSU n q L := by
  refine map_closure_of_iff _ fun A => ?_
  change (e.mapMatrix (A : Matrix (Fin n) (Fin n) K)).det = 1 ∧
      ((e.mapMatrix (A : Matrix (Fin n) (Fin n) K)).map (· ^ q))ᵀ *
        e.mapMatrix (A : Matrix (Fin n) (Fin n) K) = 1 ↔
    (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1
  rw [mapMatrix_map_pow, transpose_mapMatrix, ← map_mul, mapMatrix_eq_one_iff, det_mapMatrix,
    ← map_one e, e.injective.eq_iff]

theorem map_symplecticJ (n : ℕ) (e : K ≃+* L) :
    e.mapMatrix (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem map_statedSp (n : ℕ) (e : K ≃+* L) :
    (StatedSp n K).map
        (glFieldEquiv (Fin n ⊕ Fin n) e : GL (Fin n ⊕ Fin n) K →* GL (Fin n ⊕ Fin n) L) =
      StatedSp n L := by
  refine map_closure_of_iff _ fun A => ?_
  change (e.mapMatrix (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))ᵀ *
      Matrix.fromBlocks 0 1 (-1) 0 * e.mapMatrix (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Matrix.fromBlocks 0 1 (-1) 0 ↔
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.fromBlocks 0 1 (-1) 0
  rw [← map_symplecticJ n e, transpose_mapMatrix, ← map_mul, ← map_mul,
    e.mapMatrix.injective.eq_iff]

end Transport

section Models

variable {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]

theorem classicalModel_psl_of_stated (h : StatedClassicalModel G .PSL n p f) :
    Assembly.ComponentType.ClassicalModel G .PSL n p f := by
  obtain ⟨⟨hp, hf, hn, h2, h3⟩, K, _, _, hK, ⟨θ⟩⟩ := h
  let e := CFSG.ClassicalModels.finiteFieldEquivGaloisField K p f (by omega) hK
  refine ⟨⟨hp, hf, hn, ?_⟩, ⟨θ.trans ((statedProjCongr (glFieldEquiv (Fin n) e)
    (map_statedSL n e) (map_statedScalars e)).trans (pslModelEquiv n p f).symm)⟩⟩
  rintro ⟨rfl, h | h⟩
  · exact h2 (by rw [h])
  · exact h3 (by rw [h])

theorem classicalModel_psu_of_stated (h : StatedClassicalModel G .PSU n p f) :
    Assembly.ComponentType.ClassicalModel G .PSU n p f := by
  obtain ⟨⟨hp, hf, hn, h3⟩, K, _, _, hK, ⟨θ⟩⟩ := h
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e := CFSG.ClassicalModels.finiteFieldEquivGaloisField K p (2 * f) (by omega) hK'
  refine ⟨⟨hp, hf, hn, ?_⟩, ⟨θ.trans ((statedProjCongr (glFieldEquiv (Fin n) e)
    (map_statedSU n (p ^ f) e) (map_statedScalars e)).trans (psuModelEquiv n p f).symm)⟩⟩
  rintro ⟨rfl, h⟩
  exact h3 (by rw [h])

theorem classicalModel_psp_of_stated (h : StatedClassicalModel G .PSp n p f) :
    Assembly.ComponentType.ClassicalModel G .PSp n p f := by
  obtain ⟨⟨hp, hf, hn, h2⟩, K, _, _, hK, ⟨θ⟩⟩ := h
  let e := CFSG.ClassicalModels.finiteFieldEquivGaloisField K p f (by omega) hK
  refine ⟨⟨hp, hf, hn, ?_⟩, ⟨θ.trans ((statedProjCongr (glFieldEquiv (Fin n ⊕ Fin n) e)
    (map_statedSp n e) (map_statedScalars e)).trans (pspModelEquiv n p f).symm)⟩⟩
  rintro ⟨rfl, h⟩
  exact h2 (by rw [h])

end Models

end CFSG.ComponentClassification.ClassicalModelStatedBridge
