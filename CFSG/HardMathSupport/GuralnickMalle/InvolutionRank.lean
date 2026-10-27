module

public import CFSG.HardMathSupport.GuralnickMalle.CyclicTwoBounds
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module

open scoped TensorProduct

lemma mul_add_mul_le_add_two_mul {a b d e z w k r : ℕ} (hd : a + z = d) (he : b + w = e)
    (hk : k ≤ a * b + z * w) (hr : r + k = d * e) :
    a * e + b * d ≤ r + 2 * a * b := by
  have hd' : d = a + z := hd.symm
  have he' : e = b + w := he.symm
  rw [hd', he'] at hr ⊢
  have hid : a * (b + w) + b * (a + z) + (a * b + z * w) =
      (a + z) * (b + w) + 2 * a * b := by
    ring
  have h1 : a * (b + w) + b * (a + z) + k ≤ (a + z) * (b + w) + 2 * a * b :=
    calc a * (b + w) + b * (a + z) + k
        ≤ a * (b + w) + b * (a + z) + (a * b + z * w) := Nat.add_le_add_left hk _
      _ = (a + z) * (b + w) + 2 * a * b := hid
  omega

theorem finrank_range_tensor_sub_one_add_ge {K V W : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : V →ₗ[K] V) (hT : T.comp T = 1) (S : W →ₗ[K] W) (hS : S.comp S = 1) :
    finrank K (LinearMap.range (T - 1)) * finrank K W +
        finrank K (LinearMap.range (S - 1)) * finrank K V ≤
      finrank K (LinearMap.range (TensorProduct.map T S - 1)) +
        2 * finrank K (LinearMap.range (T - 1)) * finrank K (LinearMap.range (S - 1)) := by
  classical
  refine mul_add_mul_le_add_two_mul
    (a := finrank K (LinearMap.range (T - 1)))
    (b := finrank K (LinearMap.range (S - 1)))
    (d := finrank K V) (e := finrank K W)
    (z := finrank K (LinearMap.ker (T - 1)))
    (w := finrank K (LinearMap.ker (S - 1)))
    (k := finrank K (LinearMap.ker (TensorProduct.map T S - 1)))
    (r := finrank K (LinearMap.range (TensorProduct.map T S - 1)))
    ?_ ?_ ?_ ?_
  · exact LinearMap.finrank_range_add_finrank_ker (T - 1)
  · exact LinearMap.finrank_range_add_finrank_ker (S - 1)
  · have h := (finrank_fixed_tensor_le T hT S hS).2
    have hdz : finrank K V - finrank K (LinearMap.ker (T - 1)) =
        finrank K (LinearMap.range (T - 1)) := by
      have := LinearMap.finrank_range_add_finrank_ker (T - 1)
      omega
    have hew : finrank K W - finrank K (LinearMap.ker (S - 1)) =
        finrank K (LinearMap.range (S - 1)) := by
      have := LinearMap.finrank_range_add_finrank_ker (S - 1)
      omega
    rwa [hdz, hew] at h
  · have h := LinearMap.finrank_range_add_finrank_ker (TensorProduct.map T S - 1)
    rw [Module.finrank_tensorProduct] at h
    exact h

lemma two_mul_mul_sub_le {j m A : ℕ} (hjm : j ≤ m) (h : 2 * j * m ≤ A + 2 * j * j) :
    2 * j * (m - j) ≤ A := by
  have h1 : 2 * j * (m - j) + 2 * j * j = 2 * j * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hjm]
  omega

lemma finrank_range_sub_one_eq_of_intertwines {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (e : M ≃ₗ[K] N) (f : M →ₗ[K] M) (g : N →ₗ[K] N)
    (h : ∀ x, e (f x) = g (e x)) :
    finrank K (LinearMap.range (g - 1)) = finrank K (LinearMap.range (f - 1)) := by
  have h' : (e : M →ₗ[K] N).comp (f - 1) = (g - 1).comp (e : M →ₗ[K] N) := by
    ext x
    simp [h x]
  have h1 : finrank K (LinearMap.range ((g - 1).comp (e : M →ₗ[K] N))) =
      finrank K (LinearMap.range (g - 1)) := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have h2 : finrank K (LinearMap.range ((e : M →ₗ[K] N).comp (f - 1))) =
      finrank K (LinearMap.range (f - 1)) := by
    rw [LinearMap.range_comp, LinearEquiv.finrank_map_eq]
  rw [← h1, ← h2, h']

lemma matrix_rank_eq_finrank_range_toLin' {K : Type} [Field K] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) K) :
    A.rank = finrank K (LinearMap.range (Matrix.toLin' A)) := by
  rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun K (Fin m)) (Pi.basisFun K (Fin m)),
    Matrix.toLin_eq_toLin']

theorem two_mul_mul_le_finrank_range_conj_sub_one {K : Type} [Field K] [CharP K 2] {m : ℕ}
    (x : GL (Fin m) K) (hx : x * x = 1) :
    2 * ((x : Matrix (Fin m) (Fin m) K) - 1).rank * (m - ((x : Matrix (Fin m) (Fin m) K) - 1).rank) ≤
      finrank K (LinearMap.range ((LinearMap.mulLeft K (x : Matrix (Fin m) (Fin m) K)) ∘ₗ
        (LinearMap.mulRight K ((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) - LinearMap.id)) := by
  classical
  have hxinv : x⁻¹ = x := by
    simpa using (mul_eq_one_iff_inv_eq (a := x) (b := x)).mp hx
  rw [hxinv]
  let A : Matrix (Fin m) (Fin m) K := (x : Matrix (Fin m) (Fin m) K)
  have hAA : A * A = 1 := by
    have h : ((x * x : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
      rw [hx]
      rfl
    simpa [A] using h
  let eMat : Matrix (Fin m) (Fin m) K ≃ₗ[K] ((Fin m → K) →ₗ[K] (Fin m → K)) := Matrix.toLin'
  let T : (Fin m → K) →ₗ[K] (Fin m → K) := Matrix.toLin' A
  let Cm : Matrix (Fin m) (Fin m) K →ₗ[K] Matrix (Fin m) (Fin m) K :=
    (LinearMap.mulLeft K A).comp (LinearMap.mulRight K A)
  let Ce : ((Fin m → K) →ₗ[K] (Fin m → K)) →ₗ[K] ((Fin m → K) →ₗ[K] (Fin m → K)) :=
    (T.compRight K).comp (T.lcomp K (Fin m → K))
  have hA : ∀ X : Matrix (Fin m) (Fin m) K, eMat (Cm X) = Ce (eMat X) := by
    intro X
    simp [Cm, Ce, T, eMat, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      Matrix.toLin'_mul, LinearMap.compRight_apply, LinearMap.lcomp_apply']
  have hmat := (finrank_range_sub_one_eq_of_intertwines eMat Cm Ce hA).symm
  let φ : (Fin m → K) ≃ₗ[K] Module.Dual K (Fin m → K) :=
    (Pi.basisFun K (Fin m)).toDualEquiv
  let Td : Module.Dual K (Fin m → K) →ₗ[K] Module.Dual K (Fin m → K) := T.dualMap
  let Tt : (Fin m → K) →ₗ[K] (Fin m → K) :=
    φ.symm.toLinearMap.comp (Td.comp φ.toLinearMap)
  let E : (Fin m → K) ⊗[K] (Fin m → K) ≃ₗ[K]
      ((Fin m → K) →ₗ[K] (Fin m → K)) :=
    (TensorProduct.congr φ (LinearEquiv.refl K (Fin m → K))).trans
      (dualTensorHomEquiv K (Fin m → K) (Fin m → K))
  let G : (Fin m → K) ⊗[K] (Fin m → K) →ₗ[K] (Fin m → K) ⊗[K] (Fin m → K) :=
    TensorProduct.map Tt T
  have hT2 : T.comp T = 1 := by
    change T * T = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hAA, Matrix.toLin'_one]
    rfl
  have hTdual : Td.comp Td = 1 := by
    change T.dualMap.comp T.dualMap = 1
    rw [LinearMap.dualMap_comp_dualMap (f := T) (g := T), hT2]
    exact LinearMap.dualMap_id
  have hTt : Tt.comp Tt = 1 := by
    apply LinearMap.ext
    intro y
    have hy : Td (Td (φ y)) = φ y := by
      simpa using LinearMap.congr_fun hTdual (φ y)
    calc Tt (Tt y) = φ.symm (Td (Td (φ y))) := by simp [Tt]
      _ = φ.symm (φ y) := by rw [hy]
      _ = y := φ.symm_apply_apply y
  have hTtφ : ∀ y, φ (Tt y) = Td (φ y) := by
    intro y
    simp [Tt]
  have hdualrank : finrank K (LinearMap.range (Td - 1)) =
      finrank K (LinearMap.range (T - 1)) := by
    have hsub : Td - 1 = (T - 1).dualMap := by
      ext f y
      simp [Td]
    rw [hsub, LinearMap.finrank_range_dualMap_eq_finrank_range]
  let j := (A - 1).rank
  have hTsub : Matrix.toLin' (A - 1) = T - 1 := by
    change Matrix.toLin' (A - 1) = Matrix.toLin' A - 1
    rw [map_sub, Matrix.toLin'_one]
    rfl
  have hjT : j = finrank K (LinearMap.range (T - 1)) := by
    change (A - 1).rank = finrank K (LinearMap.range (T - 1))
    rw [matrix_rank_eq_finrank_range_toLin' (A - 1), hTsub]
  have hTtRank : finrank K (LinearMap.range (Tt - 1)) = j := by
    have h1 := finrank_range_sub_one_eq_of_intertwines φ Tt Td hTtφ
    rw [← h1, hdualrank]
    exact hjT.symm
  have hElin : E.toLinearMap.comp G = Ce.comp E.toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    ext y
    simp [E, G, Ce, T, Tt, Td, TensorProduct.congr_tmul, TensorProduct.map_tmul,
      LinearMap.compRight_apply, LinearMap.lcomp_apply',
      LinearMap.dualMap_apply, LinearEquiv.apply_symm_apply]
  have hE : ∀ z, E (G z) = Ce (E z) := fun z => LinearMap.congr_fun hElin z
  have hCeG := finrank_range_sub_one_eq_of_intertwines E G Ce hE
  have hfinY : finrank K (Fin m → K) = m := Module.finrank_fin_fun K
  have htensor := finrank_range_tensor_sub_one_add_ge
    (V := Fin m → K) (W := Fin m → K) Tt hTt T hT2
  have htensor' : 2 * j * m ≤
      finrank K (LinearMap.range (TensorProduct.map Tt T - 1)) + 2 * j * j := by
    have h := htensor
    have hTtRank' : finrank K ↥(Tt - 1).range = j := by simpa using hTtRank
    have hTrank' : finrank K ↥(T - 1).range = j := by simpa using hjT.symm
    rw [hfinY, hTtRank', hTrank'] at h
    rw [show 2 * j * m = j * m + j * m by ring]
    exact h
  have hjm : j ≤ m := by
    change (A - 1).rank ≤ m
    rw [matrix_rank_eq_finrank_range_toLin' (A - 1), hTsub]
    calc finrank K (LinearMap.range (T - 1)) ≤ finrank K (Fin m → K) :=
          LinearMap.finrank_range_le _
      _ = m := Module.finrank_fin_fun K
  have hgoal := two_mul_mul_sub_le hjm htensor'
  change 2 * j * (m - j) ≤ finrank K (LinearMap.range (Cm - 1))
  rw [hmat, hCeG]
  exact hgoal

lemma two_mul_sub_two_le {j m A : ℕ} (hj : 1 ≤ j) (h2j : 2 * j ≤ m)
    (h : 2 * j * (m - j) ≤ A) : 2 * m - 2 ≤ A := by
  obtain ⟨i, rfl⟩ : ∃ i, j = 1 + i := ⟨j - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, m = (1 + i) + (1 + k) := by
    refine ⟨m - (1 + i) - 1, by omega⟩
  rw [hk] at h ⊢
  have hsub : ((1 + i) + (1 + k)) - (1 + i) = 1 + k := by omega
  rw [hsub] at h
  have hstep : 2 * ((1 + i) + (1 + k)) - 2 ≤ 2 * (1 + i) * (1 + k) := by
    have h2 : 2 * ((1 + i) + (1 + k)) - 2 = 2 + 2 * i + 2 * k := by omega
    rw [h2]
    nlinarith
  exact hstep.trans h

theorem two_mul_sub_two_le_finrank_range_conj_sub_one {K : Type} [Field K] [CharP K 2] {m : ℕ}
    (x : GL (Fin m) K) (hx : x * x = 1) (hx1 : x ≠ 1) :
    2 * m - 2 ≤
      finrank K (LinearMap.range ((LinearMap.mulLeft K (x : Matrix (Fin m) (Fin m) K)) ∘ₗ
        (LinearMap.mulRight K ((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) - LinearMap.id)) := by
  classical
  have hbound := two_mul_mul_le_finrank_range_conj_sub_one x hx
  have hxinv : x⁻¹ = x := by
    simpa using (mul_eq_one_iff_inv_eq (a := x) (b := x)).mp hx
  rw [hxinv]
  let A : Matrix (Fin m) (Fin m) K := (x : Matrix (Fin m) (Fin m) K)
  let Mmat : Matrix (Fin m) (Fin m) K →ₗ[K] Matrix (Fin m) (Fin m) K :=
    (LinearMap.mulLeft K A).comp (LinearMap.mulRight K A) - LinearMap.id
  have hAA : A * A = 1 := by
    have h : ((x * x : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
      rw [hx]
      rfl
    simpa [A] using h
  let T : (Fin m → K) →ₗ[K] (Fin m → K) := Matrix.toLin' A
  let j := (A - 1).rank
  have hT2 : T.comp T = 1 := by
    change T * T = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hAA, Matrix.toLin'_one]
    rfl
  have hTsub : Matrix.toLin' (A - 1) = T - 1 := by
    change Matrix.toLin' (A - 1) = Matrix.toLin' A - 1
    rw [map_sub, Matrix.toLin'_one]
    rfl
  have hjT : j = finrank K (LinearMap.range (T - 1)) := by
    change (A - 1).rank = finrank K (LinearMap.range (T - 1))
    rw [matrix_rank_eq_finrank_range_toLin' (A - 1), hTsub]
  have hjpos : 1 ≤ j := by
    by_contra hlt
    have hj0 : j = 0 := by omega
    have hrange0 : finrank K (LinearMap.range (T - 1)) = 0 := by
      rw [← hjT, hj0]
    have hbot : LinearMap.range (T - 1) = ⊥ := Submodule.finrank_eq_zero.mp hrange0
    have hT1 : T - 1 = 0 := LinearMap.range_eq_bot.mp hbot
    have hTeq : T = 1 := sub_eq_zero.mp hT1
    have hA1 : A = 1 := by
      apply Matrix.toLin'.injective
      change Matrix.toLin' A = Matrix.toLin' 1
      rw [Matrix.toLin'_one]
      exact hTeq
    have hx1' : x = 1 := by
      apply Units.ext
      simpa [A] using hA1
    exact hx1 hx1'
  have h2j : 2 * j ≤ m := by
    have hsq : (T - 1).comp (T - 1) = 0 := sub_one_comp_sub_one_eq_zero T hT2
    have hle : LinearMap.range (T - 1) ≤ LinearMap.ker (T - 1) := by
      rintro _ ⟨y, rfl⟩
      simpa [LinearMap.mem_ker, LinearMap.comp_apply] using congrArg (fun f => f y) hsq
    have hjk : j ≤ finrank K (LinearMap.ker (T - 1)) := by
      rw [hjT]
      exact Submodule.finrank_mono hle
    have hnull : j + finrank K (LinearMap.ker (T - 1)) = m := by
      have h := LinearMap.finrank_range_add_finrank_ker (T - 1)
      rw [← hjT, Module.finrank_fin_fun K] at h
      exact h
    omega
  have hbound' : 2 * j * (m - j) ≤ finrank K (LinearMap.range Mmat) := by
    rw [hxinv] at hbound
    simpa [j, Mmat, A] using hbound
  have hmain := two_mul_sub_two_le hjpos h2j hbound'
  change 2 * m - 2 ≤ finrank K (LinearMap.range Mmat)
  exact hmain

end CFSG.HardMathSupport.GuralnickMalle
