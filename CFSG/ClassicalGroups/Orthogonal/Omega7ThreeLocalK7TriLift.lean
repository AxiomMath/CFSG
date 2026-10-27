module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalK7TriForm
public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRoot

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K]

@[expose] def triIdx : Fin 3 → Idx
  | 0 => .inl 2
  | 1 => .inr (.inl 2)
  | 2 => .inr (.inr ())

theorem triIdx_injective : Function.Injective triIdx := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [triIdx] at h ⊢

@[expose] def triIn (K : Type) [Field K] : Matrix Idx (Fin 3) K :=
  Matrix.of fun a j => if a = triIdx j then 1 else 0

@[expose] def triOut (K : Type) [Field K] : Matrix (Fin 3) Idx K :=
  Matrix.of fun j a => if a = triIdx j then 1 else 0

theorem triOut_mul_triIn : triOut K * triIn K = 1 := by
  ext i j
  simp only [Matrix.mul_apply, triOut, triIn, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (triIdx i)]
  · simp [triIdx_injective.eq_iff]
  · intro a _ ha
    simp [ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem triOut_mulVec (w : Idx → K) (j : Fin 3) : (triOut K *ᵥ w) j = w (triIdx j) := by
  simp [Matrix.mulVec, dotProduct, triOut]

@[expose] def triMat (M : Matrix (Fin 3) (Fin 3) K) : Matrix Idx Idx K :=
  1 + triIn K * (M - 1) * triOut K

theorem triOut_mul_triMat (M : Matrix (Fin 3) (Fin 3) K) :
    triOut K * triMat M = M * triOut K := by
  unfold triMat
  have h := triOut_mul_triIn (K := K)
  rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul,
    Matrix.sub_mul, Matrix.one_mul]
  abel

theorem triMat_mul (M N : Matrix (Fin 3) (Fin 3) K) :
    triMat (M * N) = triMat M * triMat N := by
  unfold triMat
  have h := triOut_mul_triIn (K := K)
  have key : triIn K * (M - 1) * triOut K * (triIn K * (N - 1) * triOut K) =
      triIn K * ((M - 1) * (N - 1)) * triOut K := by
    calc triIn K * (M - 1) * triOut K * (triIn K * (N - 1) * triOut K)
        = triIn K * (M - 1) * (triOut K * triIn K) * (N - 1) * triOut K := by
          simp only [Matrix.mul_assoc]
      _ = triIn K * ((M - 1) * (N - 1)) * triOut K := by
          rw [h, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have e : (1 + triIn K * (M - 1) * triOut K) * (1 + triIn K * (N - 1) * triOut K) =
      1 + triIn K * (M - 1) * triOut K + triIn K * (N - 1) * triOut K +
        triIn K * (M - 1) * triOut K * (triIn K * (N - 1) * triOut K) := by noncomm_ring
  rw [e, key]
  have hMN : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  rw [hMN]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

theorem triMat_one : triMat (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  simp [triMat]

theorem triMat_injective :
    Function.Injective (triMat : Matrix (Fin 3) (Fin 3) K → Matrix Idx Idx K) := by
  intro M N h
  have hM : M = triOut K * triMat M * triIn K := by
    rw [triOut_mul_triMat, Matrix.mul_assoc, triOut_mul_triIn, Matrix.mul_one]
  have hN : N = triOut K * triMat N * triIn K := by
    rw [triOut_mul_triMat, Matrix.mul_assoc, triOut_mul_triIn, Matrix.mul_one]
  rw [hM, hN, h]

@[expose] def triHom : Matrix (Fin 3) (Fin 3) K →* Matrix Idx Idx K where
  toFun := triMat
  map_one' := triMat_one
  map_mul' := triMat_mul

@[expose] def triGL : GL (Fin 3) K →* GL Idx K := Units.map triHom

theorem coe_triGL (A : GL (Fin 3) K) :
    ((triGL A : GL Idx K) : Matrix Idx Idx K) = triMat (A : Matrix (Fin 3) (Fin 3) K) := rfl

theorem triGL_injective : Function.Injective (triGL : GL (Fin 3) K →* GL Idx K) := by
  intro A B h
  apply Units.ext
  exact triMat_injective (congrArg (fun g : GL Idx K => (g : Matrix Idx Idx K)) h)

theorem orderOf_triGL (A : GL (Fin 3) K) : orderOf (triGL A) = orderOf A :=
  orderOf_injective triGL triGL_injective A

theorem triIn_mulVec_of_ne (t : Fin 3 → K) {a : Idx} (h : ∀ j, a ≠ triIdx j) :
    (triIn K *ᵥ t) a = 0 := by
  simp [Matrix.mulVec, dotProduct, triIn, h]

theorem triMat_mulVec (M : Matrix (Fin 3) (Fin 3) K) (w : Idx → K) :
    triMat M *ᵥ w = w + triIn K *ᵥ ((M - 1) *ᵥ (triOut K *ᵥ w)) := by
  unfold triMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem triMat_mulVec_of_ne (M : Matrix (Fin 3) (Fin 3) K) (w : Idx → K) {a : Idx}
    (h : ∀ j, a ≠ triIdx j) : (triMat M *ᵥ w) a = w a := by
  rw [triMat_mulVec, Pi.add_apply, triIn_mulVec_of_ne _ h, add_zero]

theorem modelQuad_eq_add_quadTri (a : K) (w : Idx → K) :
    modelQuad K a w =
      (w (.inl 0) ^ 2 - w (.inl 0) * w (.inr (.inl 0)) + w (.inr (.inl 0)) ^ 2) +
        (w (.inl 1) ^ 2 - w (.inl 1) * w (.inr (.inl 1)) + w (.inr (.inl 1)) ^ 2) +
          quadTri K a (triOut K *ᵥ w) := by
  rw [quadTri_apply]
  simp only [modelQuad, Fin.sum_univ_three, triOut_mulVec, triIdx]
  ring

theorem modelQuad_triMat_mulVec {M : Matrix (Fin 3) (Fin 3) K} {a : K}
    (hM : ∀ x : Fin 3 → K, quadTri K a (M *ᵥ x) = quadTri K a x) (w : Idx → K) :
    modelQuad K a (triMat M *ᵥ w) = modelQuad K a w := by
  have h1 : triOut K *ᵥ (triMat M *ᵥ w) = M *ᵥ (triOut K *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, triOut_mul_triMat, ← Matrix.mulVec_mulVec]
  have e0 : ∀ j, (Sum.inl (0 : Fin 3) : Idx) ≠ triIdx j := by
    intro j; fin_cases j <;> simp [triIdx]
  have e1 : ∀ j, (Sum.inl (1 : Fin 3) : Idx) ≠ triIdx j := by
    intro j; fin_cases j <;> simp [triIdx]
  have f0 : ∀ j, (Sum.inr (Sum.inl (0 : Fin 3)) : Idx) ≠ triIdx j := by
    intro j; fin_cases j <;> simp [triIdx]
  have f1 : ∀ j, (Sum.inr (Sum.inl (1 : Fin 3)) : Idx) ≠ triIdx j := by
    intro j; fin_cases j <;> simp [triIdx]
  rw [modelQuad_eq_add_quadTri a (triMat M *ᵥ w), modelQuad_eq_add_quadTri a w, h1, hM,
    triMat_mulVec_of_ne M w e0, triMat_mulVec_of_ne M w e1, triMat_mulVec_of_ne M w f0,
    triMat_mulVec_of_ne M w f1]

theorem modelQuad_triGL_mulVec {A : GL (Fin 3) K} {a : K}
    (hA : ∀ x : Fin 3 → K, quadTri K a ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = quadTri K a x)
    (w : Idx → K) :
    modelQuad K a (((triGL A : GL Idx K) : Matrix Idx Idx K) *ᵥ w) = modelQuad K a w :=
  modelQuad_triMat_mulVec hA w

theorem rotMat_triIdx_right {v : Fin 3 → ZMod 3} (hv : v 2 = 0) (a : Idx) (j : Fin 3) :
    rotMat K v a (triIdx j) = if a = triIdx j then 1 else 0 := by
  rcases a with i | i | u
  · fin_cases j <;> fin_cases i <;> simp [rotMat, triIdx, hv, planeRot_zero]
  · fin_cases j <;> fin_cases i <;> simp [rotMat, triIdx, hv, planeRot_zero]
  · fin_cases j <;> simp [rotMat, triIdx, hv, planeRot_zero]

theorem rotMat_triIdx_left {v : Fin 3 → ZMod 3} (hv : v 2 = 0) (j : Fin 3) (b : Idx) :
    rotMat K v (triIdx j) b = if b = triIdx j then 1 else 0 := by
  rcases b with i | i | u
  · fin_cases j <;> fin_cases i <;> simp [rotMat, triIdx, hv, planeRot_zero]
  · fin_cases j <;> fin_cases i <;> simp [rotMat, triIdx, hv, planeRot_zero]
  · fin_cases j <;> simp [rotMat, triIdx, hv, planeRot_zero]

theorem rotMat_mul_triIn {v : Fin 3 → ZMod 3} (hv : v 2 = 0) :
    rotMat K v * triIn K = triIn K := by
  ext a j
  simp only [Matrix.mul_apply, triIn, Matrix.of_apply]
  rw [Finset.sum_eq_single (triIdx j)]
  · simp [rotMat_triIdx_right hv]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem triOut_mul_rotMat {v : Fin 3 → ZMod 3} (hv : v 2 = 0) :
    triOut K * rotMat K v = triOut K := by
  ext j b
  simp only [Matrix.mul_apply, triOut, Matrix.of_apply]
  rw [Finset.sum_eq_single (triIdx j)]
  · simp [rotMat_triIdx_left hv]
  · intro a _ ha
    simp [ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem triMat_mul_rotMat (M : Matrix (Fin 3) (Fin 3) K) {v : Fin 3 → ZMod 3} (hv : v 2 = 0) :
    triMat M * rotMat K v = rotMat K v * triMat M := by
  unfold triMat
  have h1 : triIn K * (M - 1) * triOut K * rotMat K v = triIn K * (M - 1) * triOut K := by
    rw [Matrix.mul_assoc, triOut_mul_rotMat hv]
  have h2 : rotMat K v * (triIn K * (M - 1) * triOut K) = triIn K * (M - 1) * triOut K := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rotMat_mul_triIn hv]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2]

theorem mem_Omega7_conj_triGL [Finite K] (F : Frame K) {A : GL (Fin 3) K}
    (hA : ∀ x : Fin 3 → K, quadTri K F.a ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = quadTri K F.a x)
    (hodd : Odd (orderOf A)) : F.P * triGL A * F.P⁻¹ ∈ Omega7 K :=
  F.mem_Omega7_conj_of_odd (fun w => modelQuad_triGL_mulVec hA w) (by rwa [orderOf_triGL])

@[expose] noncomputable def triElt [Finite K] (F : Frame K) {A : GL (Fin 3) K}
    (hA : ∀ x : Fin 3 → K, quadTri K F.a ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = quadTri K F.a x)
    (hodd : Odd (orderOf A)) : ↥(Omega7 K) :=
  ⟨F.P * triGL A * F.P⁻¹, mem_Omega7_conj_triGL F hA hodd⟩

theorem orderOf_triElt [Finite K] (F : Frame K) {A : GL (Fin 3) K}
    (hA : ∀ x : Fin 3 → K, quadTri K F.a ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = quadTri K F.a x)
    (hodd : Odd (orderOf A)) : orderOf (triElt F hA hodd) = orderOf A := by
  rw [triElt, orderOf_modelElt F (mem_Omega7_conj_triGL F hA hodd), orderOf_triGL]

theorem commute_c₀_triElt [Finite K] (F : Frame K) {A : GL (Fin 3) K}
    (hA : ∀ x : Fin 3 → K, quadTri K F.a ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = quadTri K F.a x)
    (hodd : Odd (orderOf A)) (v : F3Cube) (hv : Multiplicative.toAdd v 2 = 0) :
    Commute (c₀ F v) (triElt F hA hodd) := by
  have h := mem_centralizer_c₀_of_model F v (m := triGL A) (mem_Omega7_conj_triGL F hA hodd)
    (by simpa [coe_triGL] using triMat_mul_rotMat (A : Matrix (Fin 3) (Fin 3) K) hv)
  exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

theorem exists_orderOf_eq_commute_c₀_of_two_eq_zero [Finite K] (F : Frame K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card K * (Nat.card K ^ 2 - 1)) :
    ∃ g : ↥(Omega7 K), orderOf g = p ∧
      ∀ v : F3Cube, Multiplicative.toAdd v 2 = 0 → Commute (c₀ F v) g := by
  obtain ⟨A, hA, hord⟩ :=
    exists_isometry_orderOf_eq_quadTri F.hK F.h3 F.a_ne_zero hp hdvd
  have hodd : Odd (orderOf A) := by
    rw [hord]
    exact hp.eq_two_or_odd'.resolve_left hp2
  exact ⟨triElt F hA hodd, by rw [orderOf_triElt, hord],
    fun v hv => commute_c₀_triElt F hA hodd v hv⟩

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
