module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutAmbient
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.ClassicalInvolution.WeakCT.AutExtend

public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Entries

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem coe_coe_blockEmb2_torusTwo (m : ℕ) (a : Fin m) (u : normOne (unitaryInvolution K p f)) :
    (((blockEmb2 K p f m a (torusTwo (unitaryInvolution K p f) u) : Su K p f (m + 1)) :
      GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      Matrix.diagonal fun i : Fin (m + 1) =>
        if i.val = a.val then ((u : Kˣ) : K)
        else if i.val = a.val + 1 then (((u : Kˣ)⁻¹ : Kˣ) : K) else 1 := by
  rw [← coe_torusEquiv_mulSingle, coe_torusEquiv]
  change Matrix.diagonal _ = _
  congr 1
  funext i
  show ((ratio (Pi.mulSingle a u) i : normOne (unitaryInvolution K p f)) : Kˣ).val = _
  rw [ratio_mulSingle]
  by_cases h1 : i.val = a.val
  · simp [h1]
  · by_cases h2 : i.val = a.val + 1
    · simp [h2]
    · simp [h1, h2]

theorem coe_coe_blockEmb2_weylElt_row (m : ℕ) (a : Fin m) (i j : Fin (m + 1))
    (hi : i.val = a.val) :
    (((blockEmb2 K p f m a (weylElt K p f) : Su K p f (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j = if j.val = a.val + 1 then 1 else 0 := by
  change blockMat (m + 1) a.val
    (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = _
  rw [blockMat_apply]
  by_cases hj : a.val ≤ j.val ∧ j.val < a.val + 2
  · rw [dite_eq_left ⟨⟨by omega, by omega⟩, hj⟩]
    have e1 : (⟨i.val - a.val, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp [hi])
    rw [e1]
    by_cases hj1 : j.val = a.val
    · have e2 : (⟨j.val - a.val, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp [hj1])
      rw [e2, ite_eq_right (by omega)]
      simp [CFSG.ClassicalInvolution.Phan.weylElt]
    · have hj2 : j.val = a.val + 1 := by omega
      have e2 : (⟨j.val - a.val, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
      rw [e2, ite_eq_left hj2]
      simp [CFSG.ClassicalInvolution.Phan.weylElt]
  · rw [dite_eq_right (fun h => hj h.2), ite_eq_right (by omega), Matrix.one_apply_ne]
    intro h
    apply hj
    rw [← h]
    omega

theorem coe_coe_blockEmb2_weylElt_col (m : ℕ) (a : Fin m) (i j : Fin (m + 1))
    (hj : j.val = a.val) :
    (((blockEmb2 K p f m a (weylElt K p f) : Su K p f (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j = if i.val = a.val + 1 then -1 else 0 := by
  change blockMat (m + 1) a.val
    (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = _
  rw [blockMat_apply]
  by_cases hi : a.val ≤ i.val ∧ i.val < a.val + 2
  · rw [dite_eq_left ⟨hi, ⟨by omega, by omega⟩⟩]
    have e1 : (⟨j.val - a.val, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp [hj])
    rw [e1]
    by_cases hi1 : i.val = a.val
    · have e2 : (⟨i.val - a.val, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp [hi1])
      rw [e2, ite_eq_right (by omega)]
      simp [CFSG.ClassicalInvolution.Phan.weylElt]
    · have hi2 : i.val = a.val + 1 := by omega
      have e2 : (⟨i.val - a.val, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
      rw [e2, ite_eq_left hi2]
      simp [CFSG.ClassicalInvolution.Phan.weylElt]
  · rw [dite_eq_right (fun h => hi h.1), ite_eq_right (by omega), Matrix.one_apply_ne]
    intro h
    apply hi
    rw [h]
    omega

end Entries

section Relations

variable {K : Type} [Field K]

theorem diagonal_relation {ι : Type} [Fintype ι] [DecidableEq ι] (bar : K ≃+* K)
    (G Gi : Matrix ι ι K) (hGiG : Gi * G = 1) (e : ι → K)
    (hrel : G * bar.mapMatrix (diagonal e) * Gi = diagonal e) (i j : ι) :
    e i * G i j = G i j * bar (e j) := by
  have h1 : G * bar.mapMatrix (diagonal e) = diagonal e * G := by
    have := congrArg (· * G) hrel
    simpa [Matrix.mul_assoc, hGiG] using this
  have h2 := congrFun (congrFun h1 i) j
  simpa [RingEquiv.mapMatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] using
    h2.symm

theorem torus_entry_cases (bar : K ≃+* K) {m : ℕ} (a : Fin m) (u : K) (hu1 : u ≠ 1)
    (hu2 : u⁻¹ ≠ u) (hbar : bar u = u⁻¹) (i j : Fin (m + 1)) (x : K) (hx : x ≠ 0)
    (h : (if i.val = a.val then u else if i.val = a.val + 1 then u⁻¹ else 1) * x =
      x * bar (if j.val = a.val then u else if j.val = a.val + 1 then u⁻¹ else 1)) :
    (i.val = a.val ∧ j.val = a.val + 1) ∨ (i.val = a.val + 1 ∧ j.val = a.val) ∨
      (i.val ≠ a.val ∧ i.val ≠ a.val + 1 ∧ j.val ≠ a.val ∧ j.val ≠ a.val + 1) := by
  have hbar' : bar u⁻¹ = u := by rw [map_inv₀, hbar, inv_inv]
  have h' : (if i.val = a.val then u else if i.val = a.val + 1 then u⁻¹ else 1) =
      bar (if j.val = a.val then u else if j.val = a.val + 1 then u⁻¹ else 1) := by
    apply mul_right_cancel₀ hx
    rw [h, mul_comm]
  have hi : i.val = a.val ∨ i.val = a.val + 1 ∨ (i.val ≠ a.val ∧ i.val ≠ a.val + 1) := by omega
  have hj : j.val = a.val ∨ j.val = a.val + 1 ∨ (j.val ≠ a.val ∧ j.val ≠ a.val + 1) := by omega
  have hu1' : u⁻¹ ≠ 1 := fun h0 => hu1 (by simpa using h0)
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj
  · simp [hi, hj, hbar] at h'
    exact absurd h'.symm hu2
  · exact Or.inl ⟨hi, hj⟩
  · simp [hi, hj.1, hj.2, hu1] at h'
  · exact Or.inr (Or.inl ⟨hi, hj⟩)
  · simp [hi, hj, hbar'] at h'
    exact absurd h' hu2
  · simp [hi, hj.1, hj.2, hu1'] at h'
  · simp [hi.1, hi.2, hj, hbar] at h'
    exact absurd h' hu1
  · simp [hi.1, hi.2, hj, hbar'] at h'
    exact absurd h'.symm hu1
  · exact Or.inr (Or.inr ⟨hi.1, hi.2, hj.1, hj.2⟩)

theorem commute_of_double_conj {ι : Type} [Fintype ι] [DecidableEq ι] (bar : K ≃+* K)
    (hbb : ∀ c, bar (bar c) = c) (G Gi Y : Matrix ι ι K) (hGiG : Gi * G = 1)
    (hY : Y = G * bar.mapMatrix (G * bar.mapMatrix Y * Gi) * Gi) :
    (G * bar.mapMatrix G) * Y = Y * (G * bar.mapMatrix G) := by
  have h1 : bar.mapMatrix (bar.mapMatrix Y) = Y := by
    ext i j
    simp [RingEquiv.mapMatrix_apply, hbb]
  have h2 : bar.mapMatrix Gi * bar.mapMatrix G = 1 := by
    rw [← map_mul, hGiG, map_one]
  rw [map_mul, map_mul, h1] at hY
  have e : Y * (G * bar.mapMatrix G) = G * bar.mapMatrix G * Y := by
    calc Y * (G * bar.mapMatrix G)
        = (G * (bar.mapMatrix G * Y * bar.mapMatrix Gi) * Gi) * (G * bar.mapMatrix G) := by
          rw [← hY]
      _ = G * bar.mapMatrix G * Y * bar.mapMatrix Gi * (Gi * G) * bar.mapMatrix G := by
          simp only [Matrix.mul_assoc]
      _ = G * bar.mapMatrix G * Y * (bar.mapMatrix Gi * bar.mapMatrix G) := by
          rw [hGiG, Matrix.mul_one, Matrix.mul_assoc _ (bar.mapMatrix Gi) (bar.mapMatrix G)]
      _ = G * bar.mapMatrix G * Y := by rw [h2, Matrix.mul_one]
  exact e.symm

end Relations

section Graph

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem not_fixed_blocks_of_graph (h : UnitaryFieldData p f K) (hK : Nat.card K = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) {m : ℕ} (hm : 4 ≤ m) (α : Su K p f (m + 1) →* Su K p f (m + 1))
    (g : GL (Fin (m + 1)) K)
    (hmat : ∀ x : Su K p f (m + 1),
      ((α x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          (unitaryInvolution K p f).mapMatrix
            ((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
            ((g⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
    (hiso : ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).map (unitaryInvolution K p f))ᵀ *
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1)
    (hsq : α.comp α = MonoidHom.id _)
    (hfix : ∀ a : Fin m, (a.val + 1 = m ∨ (1 ≤ a.val ∧ a.val + 3 ≤ m)) → ∀ A : Su K p f 2,
      α (blockEmb2 K p f m a A) = blockEmb2 K p f m a A) : False := by
  set σ₀ : K ≃+* K := unitaryInvolution K p f with hσ₀
  set G : Matrix (Fin (m + 1)) (Fin (m + 1)) K := (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    with hG
  set Gi : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((g⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : G.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det G).mp g.isUnit).ne_zero
  obtain ⟨c, hcN, hck⟩ := exists_norm_one_not_fixed h hp2
  have hbar : ∀ x, h.bar x = σ₀ x := fun x => by
    rw [UnitaryFieldData.bar_apply, hσ₀, unitaryInvolution_apply]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcN
    exact zero_ne_one hcN
  have hcσ : σ₀ c * c = 1 := by rw [← hbar]; exact hcN
  have hcσ' : σ₀ c = c⁻¹ := eq_inv_of_mul_eq_one_left hcσ
  have hu1 : c ≠ 1 := fun h1 => hck (by rw [h1]; exact one_mem _)
  have hu2 : c⁻¹ ≠ c := fun h1 => hck (by
    have h3 : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel₀ hc0
    rcases mul_self_eq_one_iff.mp h3 with h4 | h4
    · rw [h4]; exact one_mem _
    · rw [h4]; exact neg_mem (one_mem _))
  let u : normOne σ₀ := ⟨Units.mk0 c hc0, (mem_normOne _).2 (by simpa using hcσ)⟩
  have hrel : ∀ a : Fin m, (a.val + 1 = m ∨ (1 ≤ a.val ∧ a.val + 3 ≤ m)) →
      ∀ i j : Fin (m + 1), G i j ≠ 0 →
        (i.val = a.val ∧ j.val = a.val + 1) ∨ (i.val = a.val + 1 ∧ j.val = a.val) ∨
          (i.val ≠ a.val ∧ i.val ≠ a.val + 1 ∧ j.val ≠ a.val ∧ j.val ≠ a.val + 1) := by
    intro a ha i j hij
    have h1 := hmat (blockEmb2 K p f m a (torusTwo σ₀ u))
    rw [hfix a ha (torusTwo σ₀ u), coe_coe_blockEmb2_torusTwo] at h1
    have h2 := diagonal_relation σ₀ G Gi hGiG _ h1.symm i j
    exact torus_entry_cases σ₀ a c hu1 hu2 hcσ' i j (G i j) hij (by simpa [u] using h2)
  by_cases hm5 : 5 ≤ m
  ·
    have h1 := hrel ⟨1, by omega⟩ (Or.inr ⟨le_refl _, by simp only; omega⟩)
    have h2 := hrel ⟨2, by omega⟩ (Or.inr ⟨by simp only; omega, by simp only; omega⟩)
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero (⟨2, by omega⟩ : Fin (m + 1)) fun j => ?_
    by_contra hj
    rcases h1 ⟨2, by omega⟩ j hj with ⟨h3, -⟩ | ⟨-, h3⟩ | ⟨-, h3, -⟩
    · simp only at h3
      omega
    · rcases h2 ⟨2, by omega⟩ j hj with ⟨-, h4⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
      · simp only at h3 h4
        omega
      · simp only at h4
        omega
      · simp only at h4
        omega
    · simp only at h3
      omega
  ·
    obtain rfl : m = 4 := by omega
    have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
    have hA1 := hrel ⟨1, by omega⟩ (Or.inr ⟨le_refl _, by simp only; omega⟩)
    have hA3 := hrel ⟨3, by omega⟩ (Or.inl (by simp only))
    have row0 : ∀ j : Fin (4 + 1), G ⟨0, by omega⟩ j ≠ 0 → j.val = 0 := by
      intro j hj
      have h3 : j.val ≠ 1 ∧ j.val ≠ 2 := by
        rcases hA1 ⟨0, by omega⟩ j hj with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, -, h3, h4⟩
        · simp only at h3
          omega
        · simp only at h3
          omega
        · simp only at h3 h4
          exact ⟨h3, h4⟩
      have h4 : j.val ≠ 3 ∧ j.val ≠ 4 := by
        rcases hA3 ⟨0, by omega⟩ j hj with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, -, h3, h4⟩
        · simp only at h3
          omega
        · simp only at h3
          omega
        · simp only at h3 h4
          exact ⟨h3, h4⟩
      have := j.isLt
      omega
    have row1 : ∀ j : Fin (4 + 1), G ⟨1, by omega⟩ j ≠ 0 → j.val = 2 := by
      intro j hj
      rcases hA1 ⟨1, by omega⟩ j hj with ⟨-, h3⟩ | ⟨h3, -⟩ | ⟨h3, -⟩
      · simp only at h3
        omega
      · simp only at h3
        omega
      · simp only at h3
        omega
    have hW : G ⟨2, by omega⟩ ⟨1, by omega⟩ = -G ⟨1, by omega⟩ ⟨2, by omega⟩ := by
      obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin (4 + 1)) (Fin (4 + 1)) K,
          X = (((blockEmb2 K p f 4 ⟨1, by omega⟩ (weylElt K p f) : Su K p f (4 + 1)) :
            GL (Fin (4 + 1)) K) : Matrix (Fin (4 + 1)) (Fin (4 + 1)) K) := ⟨_, rfl⟩
      have h1 := hmat (blockEmb2 K p f 4 ⟨1, by omega⟩ (weylElt K p f))
      rw [hfix ⟨1, by omega⟩ (Or.inr ⟨le_refl _, by simp only; omega⟩) (weylElt K p f), ← hX]
        at h1
      have hXbar : σ₀.mapMatrix X = X := by
        have hW0 : (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K).map σ₀ =
            (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [CFSG.ClassicalInvolution.Phan.weylElt]
        rw [RingEquiv.mapMatrix_apply, hX]
        change (blockMat (4 + 1) 1 (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)).map σ₀ = blockMat (4 + 1) 1 (((weylElt K p f : Su K p f 2) :
            GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        refine (CFSG.ClassicalInvolution.WeakCT.map_blockMat (σ₀ : K →+* K) _).trans ?_
        exact congrArg (blockMat (4 + 1) 1) hW0
      rw [hXbar] at h1
      have h2 : X * G = G * X := by
        have : G * X = X * G := by
          simpa [Matrix.mul_assoc, hGiG] using congrArg (· * G) h1.symm
        exact this.symm
      have h3 := congrFun (congrFun h2 ⟨1, by omega⟩) ⟨1, by omega⟩
      have e1 : (X * G) ⟨1, by omega⟩ ⟨1, by omega⟩ = G ⟨2, by omega⟩ ⟨1, by omega⟩ := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (⟨2, by omega⟩ : Fin (4 + 1))]
        · rw [hX, coe_coe_blockEmb2_weylElt_row 4 ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ rfl,
            ite_eq_left rfl, one_mul]
        · intro k _ hk
          rw [hX, coe_coe_blockEmb2_weylElt_row 4 ⟨1, by omega⟩ ⟨1, by omega⟩ k rfl,
            ite_eq_right (fun h => hk (Fin.ext (by simpa using h))), zero_mul]
        · simp
      have e2 : (G * X) ⟨1, by omega⟩ ⟨1, by omega⟩ = -G ⟨1, by omega⟩ ⟨2, by omega⟩ := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (⟨2, by omega⟩ : Fin (4 + 1))]
        · rw [hX, coe_coe_blockEmb2_weylElt_col 4 ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ rfl,
            ite_eq_left rfl, mul_neg_one]
        · intro k _ hk
          rw [hX, coe_coe_blockEmb2_weylElt_col 4 ⟨1, by omega⟩ k ⟨1, by omega⟩ rfl,
            ite_eq_right (fun h => hk (Fin.ext (by simpa using h))), mul_zero]
        · simp
      rw [← e1, h3, e2]
    obtain ⟨c', hc'⟩ : ∃ c' : K,
        G * σ₀.mapMatrix G = c' • (1 : Matrix (Fin (4 + 1)) (Fin (4 + 1)) K) := by
      refine eq_smul_one_of_commute h hp2 (by omega) (G * σ₀.mapMatrix G) fun y hy => ?_
      have hy' : y ∈ SUid σ₀ (4 + 1) := by rw [SUid_eq_statedSU hK]; exact hy
      have h1 := DFunLike.congr_fun hsq ⟨y, hy'⟩
      have h2 := congrArg (fun x : Su K p f (4 + 1) =>
        ((x : GL (Fin (4 + 1)) K) : Matrix (Fin (4 + 1)) (Fin (4 + 1)) K)) h1
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h2
      rw [hmat (α ⟨y, hy'⟩), hmat ⟨y, hy'⟩] at h2
      exact commute_of_double_conj σ₀ (unitaryInvolution_involutive hK) G Gi
        (y : Matrix (Fin (4 + 1)) (Fin (4 + 1)) K) hGiG h2.symm
    have hGbi : σ₀.mapMatrix G * σ₀.mapMatrix Gi = 1 := by rw [← map_mul, hGGi, map_one]
    have h4 : Gᵀ * σ₀.mapMatrix G = 1 := by
      have := congrArg Matrix.transpose hiso
      rw [transpose_mul, transpose_transpose, transpose_one] at this
      exact this
    have hGT : G = c' • Gᵀ := by
      have h5 : (G - c' • Gᵀ) * σ₀.mapMatrix G = 0 := by
        rw [Matrix.sub_mul, hc', Matrix.smul_mul, h4, sub_self]
      have h6 := congrArg (· * σ₀.mapMatrix Gi) h5
      simp only [Matrix.mul_assoc, hGbi, Matrix.mul_one, Matrix.zero_mul] at h6
      exact sub_eq_zero.mp h6
    have hGT' : ∀ i j, G i j = c' * G j i := fun i j => by
      have := congrFun (congrFun hGT i) j
      simpa using this
    have hne12 : G ⟨1, by omega⟩ ⟨2, by omega⟩ ≠ 0 := by
      intro h0
      apply hdet
      refine Matrix.det_eq_zero_of_row_eq_zero (⟨1, by omega⟩ : Fin (4 + 1)) fun j => ?_
      by_contra hj
      have hj2 : j = ⟨2, by omega⟩ := Fin.ext (row1 j hj)
      rw [hj2] at hj
      exact hj h0
    have hc1 : c' = -1 := by
      have h5 := hGT' ⟨1, by omega⟩ ⟨2, by omega⟩
      rw [hW] at h5
      have h6 : G ⟨1, by omega⟩ ⟨2, by omega⟩ * (1 + c') = 0 := by linear_combination h5
      have h7 := (mul_eq_zero.mp h6).resolve_left hne12
      linear_combination h7
    have h00 : G ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
      have h5 := hGT' ⟨0, by omega⟩ ⟨0, by omega⟩
      rw [hc1] at h5
      have h6 : (2 : K) * G ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by linear_combination h5
      exact (mul_eq_zero.mp h6).resolve_left h2
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero (⟨0, by omega⟩ : Fin (4 + 1)) fun j => ?_
    by_contra hj
    have hj0 : j = ⟨0, by omega⟩ := Fin.ext (row0 j hj)
    rw [hj0] at hj
    exact hj h00

end Graph

section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem isPerfect_suTwo_of_card (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    Group.IsPerfect (Su K p f 2) := by
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two
    (K := K) (p := p) (f := f) hK
  refine CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 ?_ e.symm
  rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
  omega

theorem innerDiag_of_partner_blocks_unitary (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 4 ≤ m) {Y : Type} [Group Y] (θ : Su K p f (m + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (m + 1))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ a : Fin m, (a.val + 1 = m ∨ (1 ≤ a.val ∧ a.val + 3 ≤ m)) → ∀ A : Su K p f 2,
      σ (θ (blockEmb2 K p f m a A)) = θ (blockEmb2 K p f m a A)) :
    ∃ (g : GL (Fin (m + 1)) K)
      (hg : ∀ x : Su K p f (m + 1), g * (x : GL (Fin (m + 1)) K) * g⁻¹ ∈
        SUid (unitaryInvolution K p f) (m + 1)),
      ∀ x, σ (θ x) = θ ⟨g * (x : GL (Fin (m + 1)) K) * g⁻¹, hg x⟩ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have := isPerfect_suTwo_of_card hK hq
  obtain ⟨α, g, φ, hlift, hmat, hiso, hφ, hsq⟩ :=
    unitaryAutClassification_ambient hK hp2 hq (by omega) θ hker σ hσ hstab
  have hαfix : ∀ a : Fin m, (a.val + 1 = m ∨ (1 ≤ a.val ∧ a.val + 3 ≤ m)) → ∀ A : Su K p f 2,
      α (blockEmb2 K p f m a A) = blockEmb2 K p f m a A := fun a ha A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb2 K p f m a) (hfix a ha)) A
  rcases hφ with rfl | rfl
  · have hα : ∀ x : Su K p f (m + 1), g * (x : GL (Fin (m + 1)) K) * g⁻¹ =
        ((α x : Su K p f (m + 1)) : GL (Fin (m + 1)) K) := fun x =>
      Units.ext (by rw [hmat x, Units.val_mul, Units.val_mul]; simp)
    refine ⟨g, fun x => by rw [hα x]; exact (α x).2, fun x => ?_⟩
    rw [← hlift x]
    exact congrArg θ (Subtype.ext (hα x)).symm
  · exact (not_fixed_blocks_of_graph h hK hp2 hm α g hmat hiso hsq hαfix).elim

end Main

end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
