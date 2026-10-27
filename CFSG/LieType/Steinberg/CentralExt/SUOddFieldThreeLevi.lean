module

public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeRadical
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast

public section

namespace CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.Steinberg (IsBlkOn)

variable {F : Type*} [Field F] {σ : F ≃+* F} {m : ℕ}

section Block

variable {r n : ℕ} {e : Fin r → Fin n}

theorem isBlkOn_mul {M N : Matrix (Fin n) (Fin n) F} (hM : IsBlkOn e M) (hN : IsBlkOn e N) :
    IsBlkOn e (M * N) := by
  intro a b hab
  rcases hab with ha | hb
  · have h1 : (M * N) a b = ((1 : Matrix (Fin n) (Fin n) F) * N) a b := by
      simp only [mul_apply]
      exact Finset.sum_congr rfl fun t _ => by rw [hM a t (Or.inl ha)]
    rw [h1, Matrix.one_mul, hN a b (Or.inl ha)]
  · have h1 : (M * N) a b = (M * (1 : Matrix (Fin n) (Fin n) F)) a b := by
      simp only [mul_apply]
      exact Finset.sum_congr rfl fun t _ => by rw [hN t b (Or.inr hb)]
    rw [h1, Matrix.mul_one, hM a b (Or.inr hb)]

theorem isBlkOn_ext {M N : Matrix (Fin n) (Fin n) F} (hM : IsBlkOn e M) (hN : IsBlkOn e N)
    (h : M.submatrix e e = N.submatrix e e) : M = N := by
  ext a b
  by_cases hab : a ∈ Set.range e ∧ b ∈ Set.range e
  · obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hab
    exact congrFun (congrFun h i) j
  · rw [not_and_or] at hab
    rw [hM a b hab, hN a b hab]

end Block

section Iota

@[expose] def iotaMat (A : Matrix (Fin m) (Fin m) F) : Matrix (Fin (m + 2)) (Fin (m + 2)) F :=
  Matrix.of fun i j =>
    if h : (0 < (i : ℕ) ∧ (i : ℕ) < m + 1) ∧ (0 < (j : ℕ) ∧ (j : ℕ) < m + 1) then
      A ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    else (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) F) i j

theorem iotaMat_isBlkOn (A : Matrix (Fin m) (Fin m) F) : IsBlkOn mid (iotaMat A) := by
  intro a b hab
  rw [iotaMat, of_apply, dite_eq_right]
  rintro ⟨ha, hb⟩
  rcases hab with h | h
  · exact h (mem_range_mid.2 ha)
  · exact h (mem_range_mid.2 hb)

theorem iotaMat_mid (A : Matrix (Fin m) (Fin m) F) (i j : Fin m) :
    iotaMat A (mid i) (mid j) = A i j := by
  have h : (0 < (mid i : ℕ) ∧ (mid i : ℕ) < m + 1) ∧ (0 < (mid j : ℕ) ∧ (mid j : ℕ) < m + 1) := by
    simp only [val_mid]
    omega
  rw [iotaMat, of_apply, dite_eq_left h]
  congr 1

theorem submatrix_iotaMat (A : Matrix (Fin m) (Fin m) F) : (iotaMat A).submatrix mid mid = A := by
  ext i j
  exact iotaMat_mid A i j

theorem iotaMat_mul (A B : Matrix (Fin m) (Fin m) F) :
    iotaMat (A * B) = iotaMat A * iotaMat B :=
  isBlkOn_ext (iotaMat_isBlkOn _) (isBlkOn_mul (iotaMat_isBlkOn A) (iotaMat_isBlkOn B)) (by
    rw [submatrix_iotaMat, CFSG.LieType.Steinberg.submatrix_mul_of_isBlkOn mid_injective
      (iotaMat_isBlkOn A), submatrix_iotaMat, submatrix_iotaMat])

theorem iotaMat_one : iotaMat (1 : Matrix (Fin m) (Fin m) F) = 1 :=
  isBlkOn_ext (iotaMat_isBlkOn _) (fun _ _ _ => rfl) (by
    rw [submatrix_iotaMat, submatrix_one _ mid_injective])

theorem det_iotaMat (A : Matrix (Fin m) (Fin m) F) : (iotaMat A).det = A.det := by
  rw [← CFSG.LieType.Steinberg.det_submatrix_of_isBlkOn mid_injective (iotaMat_isBlkOn A),
    submatrix_iotaMat]

theorem rev_mem_range_mid_iff {a : Fin (m + 2)} :
    Fin.rev a ∈ Set.range (mid (m := m)) ↔ a ∈ Set.range (mid (m := m)) := by
  rw [mem_range_mid, mem_range_mid, Fin.val_rev]
  omega

variable (σ) in
theorem iotaMat_isometry {A : Matrix (Fin m) (Fin m) F}
    (hA : conjTr σ A * antidiag m * A = antidiag m) :
    conjTr σ (iotaMat A) * antidiag (m + 2) * iotaMat A = antidiag (m + 2) := by
  have hB := iotaMat_isBlkOn A
  ext a b
  rw [CFSG.LieType.Steinberg.conjTr_mul_antidiag_mul_apply]
  by_cases ha : a ∈ Set.range (mid (m := m))
  · by_cases hb : b ∈ Set.range (mid (m := m))
    · obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      have h := congrFun (congrFun hA i) j
      rw [CFSG.LieType.Steinberg.conjTr_mul_antidiag_mul_apply] at h
      rw [← Fintype.sum_of_injective mid mid_injective (fun s => σ (A s i) * A (Fin.rev s) j)
        _ (fun t ht => by rw [hB t (mid i) (Or.inl ht), one_apply_ne (fun h' => ht ⟨i, h'.symm⟩),
          map_zero, zero_mul]) (fun s => by rw [iotaMat_mid, rev_mid, iotaMat_mid]), h]
      simp only [antidiag, of_apply, rev_mid, mid_injective.eq_iff]
    · rw [Finset.sum_eq_single (Fin.rev b)]
      · rw [Fin.rev_rev, hB (Fin.rev b) a (Or.inl (fun h => hb (rev_mem_range_mid_iff.1 h))),
          hB b b (Or.inl hb), one_apply_eq, mul_one, one_apply_ne, map_zero]
        · simp only [antidiag, of_apply]
          rw [ite_eq_right]
          intro h
          exact hb (by rw [h]; exact rev_mem_range_mid_iff.2 ha)
        · intro h
          exact hb (rev_mem_range_mid_iff.1 (by rw [h]; exact ha))
      · intro t _ ht
        rw [hB (Fin.rev t) b (Or.inr hb), one_apply_ne (fun h => ht (by rw [← h, Fin.rev_rev])),
          mul_zero]
      · simp
  · rw [Finset.sum_eq_single a]
    · rw [hB a a (Or.inr ha), one_apply_eq, map_one, one_mul,
        hB (Fin.rev a) b (Or.inl (fun h => ha (rev_mem_range_mid_iff.1 h)))]
      simp only [antidiag, of_apply, one_apply]
      by_cases h : b = Fin.rev a
      · subst h
        simp
      · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
    · intro t _ ht
      rw [hB t a (Or.inr ha), one_apply_ne ht, map_zero, zero_mul]
    · simp

@[expose] noncomputable def iotaHom : SU σ m →* SU σ (m + 2) where
  toFun A := ⟨⟨iotaMat (mat σ m A), iotaMat (mat σ m A⁻¹),
      by rw [← iotaMat_mul, ← map_mul, mul_inv_cancel, map_one, iotaMat_one],
      by rw [← iotaMat_mul, ← map_mul, inv_mul_cancel, map_one, iotaMat_one]⟩,
    mem_SU.2 ⟨by rw [Units.val_mk, det_iotaMat]; exact A.2.1, iotaMat_isometry σ A.2.2⟩⟩
  map_one' := Subtype.ext (Units.ext (by
    change iotaMat (mat σ m 1) = 1
    rw [map_one, iotaMat_one]))
  map_mul' A B := Subtype.ext (Units.ext (by
    change iotaMat (mat σ m (A * B)) = iotaMat (mat σ m A) * iotaMat (mat σ m B)
    rw [map_mul, iotaMat_mul]))

theorem mat_iotaHom (A : SU σ m) : mat σ (m + 2) (iotaHom A) = iotaMat (mat σ m A) :=
  rfl

theorem iotaHom_injective : Function.Injective (iotaHom (σ := σ) (m := m)) := by
  intro A B h
  have h' := congrArg (fun g => (mat σ (m + 2) g).submatrix mid mid) h
  simp only [mat_iotaHom, submatrix_iotaMat] at h'
  exact mat_injective h'

theorem iotaMat_mulVec_e0 (A : Matrix (Fin m) (Fin m) F) : iotaMat A *ᵥ e0 = e0 := by
  funext i
  rw [mulVec_single_one, col_apply, iotaMat_isBlkOn A i 0 (Or.inr (fun h => by
    rw [mem_range_mid] at h
    exact absurd h.1 (by simp))), one_apply]
  simp only [e0, Pi.single_apply]

theorem iotaMat_mulVec_eL (A : Matrix (Fin m) (Fin m) F) : iotaMat A *ᵥ eL = eL := by
  funext i
  rw [mulVec_single_one, col_apply, iotaMat_isBlkOn A i (Fin.last (m + 1)) (Or.inr (fun h => by
    rw [mem_range_mid] at h
    exact absurd h.2 (by simp))), one_apply]
  simp only [eL, Pi.single_apply]

theorem iotaHom_mem_levi (A : SU σ m) : iotaHom A ∈ levi σ :=
  ⟨⟨1, by rw [mat_iotaHom, iotaMat_mulVec_e0, one_smul]⟩,
    ⟨1, by rw [mat_iotaHom, iotaMat_mulVec_eL, one_smul]⟩⟩

theorem range_iotaHom_le_levi : (iotaHom (σ := σ) (m := m)).range ≤ levi σ := by
  rintro _ ⟨A, rfl⟩
  exact iotaHom_mem_levi A

theorem eq_one_of_mem_radical_of_mem_range {hσ : ∀ c, σ (σ c) = c} {x : SU σ (m + 2)}
    (hx : x ∈ radical σ hσ) (hι : x ∈ (iotaHom (σ := σ) (m := m)).range) : x = 1 := by
  obtain ⟨A, rfl⟩ := hι
  exact eq_one_of_mem_radical_of_mulVec_eL hx (by rw [mat_iotaHom, iotaMat_mulVec_eL])

end Iota

section Torus

variable (σ) in
@[expose] def IsUnitaryDiag {n : ℕ} (u : Fin n → Fˣ) : Prop :=
  (∀ s, σ (u s : F) * u (Fin.rev s) = 1) ∧ ∏ s, (u s : F) = 1

@[expose] noncomputable def diagSU {n : ℕ} {u : Fin n → Fˣ} (hu : IsUnitaryDiag σ u) :
    SU σ n :=
  ⟨⟨diagonal fun s => (u s : F), diagonal fun s => ((u s)⁻¹ : Fˣ),
      by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩,
    mem_SU.2 ⟨by rw [Units.val_mk, det_diagonal, hu.2], by
      have hc : conjTr σ (diagonal fun s => (u s : F)) = diagonal fun s => σ (u s : F) := by
        ext a b
        by_cases h : a = b
        · subst h
          simp [conjTr]
        · simp [conjTr, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]
      rw [Units.val_mk, hc]
      ext a b
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [antidiag, Matrix.of_apply]
      split_ifs with hb
      · subst hb
        rw [mul_one, hu.1 a]
      · simp⟩⟩

theorem mat_diagSU {n : ℕ} {u : Fin n → Fˣ} (hu : IsUnitaryDiag σ u) :
    mat σ n (diagSU hu) = diagonal fun s => (u s : F) :=
  rfl

@[expose] noncomputable def torusDiag (σ : F ≃+* F) (a l : Fˣ) : Fin (m + 2) → Fˣ := fun s =>
  if s = 0 then a else if s = Fin.last (m + 1) then (Units.map σ.toRingHom.toMonoidHom a)⁻¹
  else l

theorem torusDiag_zero (a l : Fˣ) : torusDiag (m := m) σ a l 0 = a := by
  simp [torusDiag]

theorem torusDiag_last (a l : Fˣ) :
    (torusDiag (m := m) σ a l (Fin.last (m + 1)) : F) = (σ a)⁻¹ := by
  simp [torusDiag, (zero_ne_last (m := m)).symm]

theorem torusDiag_mid (a l : Fˣ) (j : Fin m) : torusDiag σ a l (mid j) = l := by
  simp [torusDiag, mid_ne_zero, mid_ne_last]

theorem torusDiag_of_mem {a l : Fˣ} {s : Fin (m + 2)} (hs : s ∈ Set.range (mid (m := m))) :
    torusDiag σ a l s = l := by
  obtain ⟨j, rfl⟩ := hs
  exact torusDiag_mid a l j

theorem isUnitaryDiag_torusDiag (hσ : ∀ c, σ (σ c) = c) {a l : Fˣ} (hl : σ (l : F) * l = 1)
    (hdet : (a : F) * (l : F) ^ m * (σ a)⁻¹ = 1) : IsUnitaryDiag σ (torusDiag (m := m) σ a l) := by
  have ha : (σ a : F) ≠ 0 := fun h => a.ne_zero (σ.injective (by rw [h, map_zero]))
  refine ⟨fun s => ?_, ?_⟩
  · by_cases h0 : s = 0
    · subst h0
      rw [Fin.rev_zero, torusDiag_last, torusDiag_zero, mul_inv_cancel₀ ha]
    · by_cases hl' : s = Fin.last (m + 1)
      · subst hl'
        rw [Fin.rev_last, torusDiag_last, torusDiag_zero, map_inv₀, hσ, inv_mul_cancel₀ a.ne_zero]
      · have hs : s ∈ Set.range (mid (m := m)) := mem_range_mid.2 ⟨by
          rcases Nat.eq_zero_or_pos (s : ℕ) with h | h
          · exact absurd (Fin.ext (by simpa using h)) h0
          · exact h, by
          have := s.isLt
          have h' : (s : ℕ) ≠ m + 1 := fun h => hl' (Fin.ext (by simpa using h))
          omega⟩
        rw [torusDiag_of_mem hs, torusDiag_of_mem (rev_mem_range_mid_iff.2 hs), hl]
  · rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    have hmid : ∀ i : Fin m, (torusDiag σ a l i.castSucc.succ : F) = l := fun i => by
      rw [show i.castSucc.succ = mid i from Fin.ext rfl, torusDiag_mid]
    simp only [hmid, Finset.prod_const, Finset.card_univ, Fintype.card_fin, torusDiag_zero]
    rw [show (Fin.last m).succ = Fin.last (m + 1) from rfl, torusDiag_last, ← mul_assoc, hdet]

@[expose] noncomputable def torusElt (hσ : ∀ c, σ (σ c) = c) {a l : Fˣ}
    (hl : σ (l : F) * l = 1) (hdet : (a : F) * (l : F) ^ m * (σ a)⁻¹ = 1) : SU σ (m + 2) :=
  diagSU (isUnitaryDiag_torusDiag hσ hl hdet)

variable {hσ : ∀ c, σ (σ c) = c} {a l : Fˣ} {hl : σ (l : F) * l = 1}
  {hdet : (a : F) * (l : F) ^ m * (σ a)⁻¹ = 1}

theorem mat_torusElt :
    mat σ (m + 2) (torusElt hσ hl hdet) = diagonal fun s => (torusDiag σ a l s : F) :=
  rfl

theorem torusElt_mulVec_e0 :
    mat σ (m + 2) (torusElt hσ hl hdet) *ᵥ e0 = (a : F) • e0 := by
  funext i
  rw [mat_torusElt, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : i = 0
  · subst h
    simp [torusDiag_zero]
  · simp [Pi.single_eq_of_ne h]

theorem torusElt_mulVec_eL :
    mat σ (m + 2) (torusElt hσ hl hdet) *ᵥ eL = (σ a)⁻¹ • eL := by
  funext i
  rw [mat_torusElt, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : i = Fin.last (m + 1)
  · subst h
    simp [torusDiag_last]
  · simp [Pi.single_eq_of_ne h]

theorem torusElt_mem_levi : torusElt hσ hl hdet ∈ levi σ :=
  ⟨⟨a, torusElt_mulVec_e0⟩, ⟨(σ a)⁻¹, torusElt_mulVec_eL⟩⟩

theorem torusElt_commute_iotaHom (A : SU σ m) :
    torusElt hσ hl hdet * iotaHom A = iotaHom A * torusElt hσ hl hdet := by
  refine mat_injective ?_
  rw [map_mul, map_mul, mat_torusElt, mat_iotaHom]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i ∈ Set.range (mid (m := m)) ∧ j ∈ Set.range (mid (m := m))
  · rw [torusDiag_of_mem hij.1, torusDiag_of_mem hij.2, mul_comm]
  · rw [not_and_or] at hij
    rw [iotaMat_isBlkOn _ i j hij]
    by_cases h : i = j
    · subst h
      exact mul_comm _ _
    · rw [one_apply_ne h, mul_zero, zero_mul]

theorem qθ_torusElt_conj {x : SU σ (m + 2)} (hx : x ∈ radical σ hσ) :
    qθ σ (torusElt hσ hl hdet * x * (torusElt hσ hl hdet)⁻¹) = (σ a * l : F) • qθ σ x := by
  rw [qθ_conj torusElt_mem_levi torusElt_mulVec_e0 hx]
  funext j
  rw [mat_torusElt, mulVec_diagonal, torusDiag_mid, midExt_mid, Pi.smul_apply, smul_eq_mul,
    mul_assoc]

theorem qc_torusElt_conj {x : SU σ (m + 2)} (hx : x ∈ radical σ hσ) :
    qc σ (torusElt hσ hl hdet * x * (torusElt hσ hl hdet)⁻¹) = σ a * a * qc σ x :=
  qc_conj torusElt_mem_levi torusElt_mulVec_e0 hx

end Torus

end CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
