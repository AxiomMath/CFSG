module

public import CFSG.HardMathSupport.GuralnickMalle.AdjointHeart
public import CFSG.LieType.SpecialLinear.ExteriorModel.Minor
public import CFSG.HardMathSupport.GuralnickMalle.BasicGeneral

public section

open Matrix CFSG.HardMathSupport.GuralnickMalle CFSG.LieType.SpecialLinear.ExteriorModel
open Module

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem conj_sub_one_mul_sub_one {R : Type*} [Ring R] (P Q a b : R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (h : (a - 1) * (b - 1) = 0) :
    (P * a * Q - 1) * (P * b * Q - 1) = 0 := by
  have hPaQ : P * a * Q - 1 = P * (a - 1) * Q := by
    rw [mul_sub, mul_one, sub_mul, hPQ]
  have hPbQ : P * b * Q - 1 = P * (b - 1) * Q := by
    rw [mul_sub, mul_one, sub_mul, hPQ]
  rw [hPaQ, hPbQ]
  calc P * (a - 1) * Q * (P * (b - 1) * Q)
      = P * (a - 1) * (Q * P) * (b - 1) * Q := by noncomm_ring
    _ = P * (a - 1) * (b - 1) * Q := by rw [hQP, mul_one]
    _ = P * ((a - 1) * (b - 1)) * Q := by noncomm_ring
    _ = 0 := by rw [h, mul_zero, zero_mul]

theorem exists_smul_one_eq_of_map_eq_smul_one {K k : Type*} [CommRing K] [CommRing k]
    (φ : K →+* k) (hφ : Function.Injective φ) {m : ℕ} (Y : Matrix (Fin m) (Fin m) K)
    {c : k} (hY : Y.map φ = c • 1) : ∃ c₀ : K, Y = c₀ • 1 := by
  classical
  rcases isEmpty_or_nonempty (Fin m) with h | hne
  · exact ⟨0, Subsingleton.elim _ _⟩
  · let i₀ : Fin m := Classical.choice hne
    refine ⟨Y i₀ i₀, ?_⟩
    ext i j
    have hij := congrFun (congrFun hY i) j
    by_cases h : i = j
    · subst h
      have hii : Y i i = Y i₀ i₀ := by
        apply hφ
        have h1 : φ (Y i i) = c := by simpa using hij
        have h0 : φ (Y i₀ i₀) = c := by
          have := congrFun (congrFun hY i₀) i₀
          simpa using this
        rw [h1, h0]
      simp [hii]
    · have h0 : Y i j = 0 := by
        apply hφ
        have h1 : φ (Y i j) = 0 := by
          simpa [Matrix.one_apply, h] using hij
        rw [h1, map_zero]
      simp [h, h0]

theorem sub_one_mul_sub_one_conj {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (g a b : G)
    (h : (ρ a - 1) * (ρ b - 1) = 0) :
    (ρ (g * a * g⁻¹) - 1) * (ρ (g * b * g⁻¹) - 1) = 0 := by
  have hga : ρ (g * a * g⁻¹) = ρ g * ρ a * ρ (g⁻¹) := by rw [map_mul, map_mul]
  have hgb : ρ (g * b * g⁻¹) = ρ g * ρ b * ρ (g⁻¹) := by rw [map_mul, map_mul]
  rw [hga, hgb]
  exact conj_sub_one_mul_sub_one (ρ g) (ρ (g⁻¹)) (ρ a) (ρ b)
    (by ext v; simp) (by ext v; simp) h

theorem adjointHeartRep_sub_one_mul_sub_one_of_map {K k : Type} [Field K] [Field k]
    (φ : K →+* k) {m : ℕ} (a b : GL (Fin m) K)
    (h : (adjointHeartRep m k (Matrix.GeneralLinearGroup.map φ a) - 1) *
      (adjointHeartRep m k (Matrix.GeneralLinearGroup.map φ b) - 1) = 0) :
    (adjointHeartRep m K a - 1) * (adjointHeartRep m K b - 1) = 0 := by
  rw [adjointHeartRep_quadratic_iff]
  intro X hX
  have hXtr : Matrix.trace X = 0 := by
    simpa [slMatrices, Matrix.traceLinearMap_apply] using hX
  have hXk : X.map φ ∈ slMatrices m k := by
    rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply,
      ← AddMonoidHom.map_trace φ X, hXtr, map_zero]
  obtain ⟨c, hc⟩ := (adjointHeartRep_quadratic_iff (Matrix.GeneralLinearGroup.map φ a)
    (Matrix.GeneralLinearGroup.map φ b)).mp h (X.map φ) hXk
  have hA : ((Matrix.GeneralLinearGroup.map φ a : GL (Fin m) k) :
      Matrix (Fin m) (Fin m) k) = (a : Matrix (Fin m) (Fin m) K).map φ := rfl
  have hB : ((Matrix.GeneralLinearGroup.map φ b : GL (Fin m) k) :
      Matrix (Fin m) (Fin m) k) = (b : Matrix (Fin m) (Fin m) K).map φ := rfl
  have hAinv : (((Matrix.GeneralLinearGroup.map φ a)⁻¹ : GL (Fin m) k) :
      Matrix (Fin m) (Fin m) k) =
      (((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)).map φ := by
    rw [← Matrix.GeneralLinearGroup.map_inv]
    rfl
  have hBinv : (((Matrix.GeneralLinearGroup.map φ b)⁻¹ : GL (Fin m) k) :
      Matrix (Fin m) (Fin m) k) =
      (((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)).map φ := by
    rw [← Matrix.GeneralLinearGroup.map_inv]
    rfl
  have hmap : RingHom.mapMatrix φ
      ((a : Matrix (Fin m) (Fin m) K) *
          ((b : Matrix (Fin m) (Fin m) K) * X *
            ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) *
          ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) -
        (b : Matrix (Fin m) (Fin m) K) * X *
          ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) -
        (a : Matrix (Fin m) (Fin m) K) * X *
          ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) + X) =
      ((Matrix.GeneralLinearGroup.map φ a : GL (Fin m) k) :
          Matrix (Fin m) (Fin m) k) *
          (((Matrix.GeneralLinearGroup.map φ b : GL (Fin m) k) :
              Matrix (Fin m) (Fin m) k) * X.map φ *
            (((Matrix.GeneralLinearGroup.map φ b)⁻¹ : GL (Fin m) k) :
              Matrix (Fin m) (Fin m) k)) *
          (((Matrix.GeneralLinearGroup.map φ a)⁻¹ : GL (Fin m) k) :
            Matrix (Fin m) (Fin m) k) -
        ((Matrix.GeneralLinearGroup.map φ b : GL (Fin m) k) :
            Matrix (Fin m) (Fin m) k) * X.map φ *
          (((Matrix.GeneralLinearGroup.map φ b)⁻¹ : GL (Fin m) k) :
            Matrix (Fin m) (Fin m) k) -
        ((Matrix.GeneralLinearGroup.map φ a : GL (Fin m) k) :
            Matrix (Fin m) (Fin m) k) * X.map φ *
          (((Matrix.GeneralLinearGroup.map φ a)⁻¹ : GL (Fin m) k) :
            Matrix (Fin m) (Fin m) k) + X.map φ := by
    simp only [map_add, map_sub, map_mul, RingHom.mapMatrix_apply,
      hA.symm, hB.symm, hAinv.symm, hBinv.symm]
  have hY : (RingHom.mapMatrix φ
      ((a : Matrix (Fin m) (Fin m) K) *
          ((b : Matrix (Fin m) (Fin m) K) * X *
            ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) *
          ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) -
        (b : Matrix (Fin m) (Fin m) K) * X *
          ((b⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) -
        (a : Matrix (Fin m) (Fin m) K) * X *
          ((a⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) + X)) = c • 1 := by
    rw [hmap, hc]
  obtain ⟨c₀, hc₀⟩ := exists_smul_one_eq_of_map_eq_smul_one φ (RingHom.injective φ) _
    (by simpa only [RingHom.mapMatrix_apply] using hY)
  exact ⟨c₀, hc₀⟩

@[expose] noncomputable def minorMatrix {R : Type*} [CommRing R] {m : ℕ} (j : ℕ)
    (g : Matrix (Fin m) (Fin m) R) :
    Matrix (Set.powersetCard (Fin m) j) (Set.powersetCard (Fin m) j) R :=
  Matrix.of fun s t => minor g s t

theorem minorMatrix_mul {R : Type*} [CommRing R] {m : ℕ} (j : ℕ)
    (g h : Matrix (Fin m) (Fin m) R) :
    minorMatrix j (g * h) = minorMatrix j g * minorMatrix j h := by
  ext s t
  simp [minorMatrix, minor_mul, Matrix.mul_apply]

theorem minorMatrix_one {R : Type*} [CommRing R] {m : ℕ} (j : ℕ) :
    minorMatrix j (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext s t
  simp [minorMatrix, minor_one, Matrix.one_apply]

theorem minorMatrix_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (j : ℕ) (g : Matrix (Fin m) (Fin m) R) :
    minorMatrix j (g.map φ) = (minorMatrix j g).map φ := by
  ext s t
  simp [minorMatrix, minor_map]

theorem toMatrix_exteriorPower_map {R : Type*} [CommRing R] {m : ℕ} (j : ℕ)
    (g : Matrix (Fin m) (Fin m) R) :
    LinearMap.toMatrix ((Pi.basisFun R (Fin m)).exteriorPower j)
        ((Pi.basisFun R (Fin m)).exteriorPower j)
      (exteriorPower.map j (Matrix.toLin' g)) = minorMatrix j g := by
  ext s t
  rw [LinearMap.toMatrix_apply, minorMatrix, Matrix.of_apply,
    repr_exteriorPower_map_eq_minor]

theorem exteriorPower_map_sub_one_mul_sub_one_iff {R : Type*} [CommRing R] {m : ℕ} (j : ℕ)
    (a b : Matrix (Fin m) (Fin m) R) :
    (exteriorPower.map j (Matrix.toLin' a) - 1) * (exteriorPower.map j (Matrix.toLin' b) - 1) = 0 ↔
      (minorMatrix j a - 1) * (minorMatrix j b - 1) = 0 := by
  let B : Basis (Set.powersetCard (Fin m) j) R (⋀[R]^j (Fin m → R)) :=
    (Pi.basisFun R (Fin m)).exteriorPower j
  let e := LinearMap.toMatrixAlgEquiv B
  have hA : e (exteriorPower.map j (Matrix.toLin' a)) = minorMatrix j a :=
    toMatrix_exteriorPower_map j a
  have hB : e (exteriorPower.map j (Matrix.toLin' b)) = minorMatrix j b :=
    toMatrix_exteriorPower_map j b
  have hsubA : e (exteriorPower.map j (Matrix.toLin' a) - 1) =
      e (exteriorPower.map j (Matrix.toLin' a)) - 1 := by
    calc e (exteriorPower.map j (Matrix.toLin' a) - 1)
        = e (exteriorPower.map j (Matrix.toLin' a)) - e 1 :=
          e.toRingEquiv.map_sub (exteriorPower.map j (Matrix.toLin' a)) 1
      _ = e (exteriorPower.map j (Matrix.toLin' a)) - 1 := by
          rw [show e 1 = 1 from e.toRingEquiv.map_one]
  have hsubB : e (exteriorPower.map j (Matrix.toLin' b) - 1) =
      e (exteriorPower.map j (Matrix.toLin' b)) - 1 := by
    calc e (exteriorPower.map j (Matrix.toLin' b) - 1)
        = e (exteriorPower.map j (Matrix.toLin' b)) - e 1 :=
          e.toRingEquiv.map_sub (exteriorPower.map j (Matrix.toLin' b)) 1
      _ = e (exteriorPower.map j (Matrix.toLin' b)) - 1 := by
          rw [show e 1 = 1 from e.toRingEquiv.map_one]
  have key : e ((exteriorPower.map j (Matrix.toLin' a) - 1) *
      (exteriorPower.map j (Matrix.toLin' b) - 1)) =
      (minorMatrix j a - 1) * (minorMatrix j b - 1) := by
    rw [map_mul, hsubA, hsubB, hA, hB]
  constructor
  · intro h
    rw [← key, h, map_zero]
  · intro h
    exact e.injective (by rw [key, h, map_zero])

theorem minorMatrix_sub_one_mul_sub_one_of_map {K k : Type*} [Field K] [Field k]
    (φ : K →+* k) {m : ℕ} (j : ℕ) (a b : Matrix (Fin m) (Fin m) K)
    (h : (minorMatrix j (a.map φ) - 1) * (minorMatrix j (b.map φ) - 1) = 0) :
    (minorMatrix j a - 1) * (minorMatrix j b - 1) = 0 := by
  rw [minorMatrix_map φ j a, minorMatrix_map φ j b] at h
  have h' : RingHom.mapMatrix φ ((minorMatrix j a - 1) * (minorMatrix j b - 1)) = 0 := by
    rw [map_mul, map_sub, map_one, map_sub, map_one]
    simpa only [RingHom.mapMatrix_apply] using h
  have h'' : ((minorMatrix j a - 1) * (minorMatrix j b - 1)).map φ = 0 := by
    simpa only [RingHom.mapMatrix_apply] using h'
  exact Matrix.map_injective (RingHom.injective φ) (by simpa using h'')

theorem minorMatrix_sub_one_mul_sub_one_conj {R : Type*} [CommRing R] {m : ℕ} (j : ℕ)
    (P Q a b : Matrix (Fin m) (Fin m) R) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h : (minorMatrix j a - 1) * (minorMatrix j b - 1) = 0) :
    (minorMatrix j (P * a * Q) - 1) * (minorMatrix j (P * b * Q) - 1) = 0 := by
  have hUV : minorMatrix j P * minorMatrix j Q = 1 := by
    rw [← minorMatrix_mul, hPQ, minorMatrix_one]
  have hVU : minorMatrix j Q * minorMatrix j P = 1 := by
    rw [← minorMatrix_mul, hQP, minorMatrix_one]
  have hPaQ : minorMatrix j (P * a * Q) =
      minorMatrix j P * minorMatrix j a * minorMatrix j Q := by
    rw [minorMatrix_mul, minorMatrix_mul]
  have hPbQ : minorMatrix j (P * b * Q) =
      minorMatrix j P * minorMatrix j b * minorMatrix j Q := by
    rw [minorMatrix_mul, minorMatrix_mul]
  rw [hPaQ, hPbQ]
  exact conj_sub_one_mul_sub_one (minorMatrix j P) (minorMatrix j Q)
    (minorMatrix j a) (minorMatrix j b) hUV hVU h

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
