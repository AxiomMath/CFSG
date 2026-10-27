module

public import CFSG.Open.StatedAPI
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor

open Matrix Multiplicative CFSG.Open CFSG.Open.StatedAPI

variable {K : Type} [Field K]

@[expose] def diagUnit (x y z : Kˣ) : GL (Fin 3) K :=
  ⟨diagonal ![(x : K), (y : K), (z : K)],
    diagonal ![((x⁻¹ : Kˣ) : K), ((y⁻¹ : Kˣ) : K), ((z⁻¹ : Kˣ) : K)],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp⟩

theorem diagUnit_val (x y z : Kˣ) :
    ((diagUnit x y z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(x : K), (y : K), (z : K)] := rfl

theorem diagUnit_inv_val (x y z : Kˣ) :
    (((diagUnit x y z)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![((x⁻¹ : Kˣ) : K), ((y⁻¹ : Kˣ) : K), ((z⁻¹ : Kˣ) : K)] := rfl

theorem diagUnit_mul (x y z x' y' z' : Kˣ) :
    diagUnit x y z * diagUnit x' y' z' = diagUnit (x * x') (y * y') (z * z') := by
  apply Units.ext
  rw [Units.val_mul, diagUnit_val, diagUnit_val, diagUnit_val, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagUnit_one : diagUnit (1 : Kˣ) 1 1 = 1 := by
  apply Units.ext
  simp only [diagUnit_val, Units.val_one]
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem det_diagUnit (x y z : Kˣ) :
    (diagUnit x y z : GL (Fin 3) K).val.det = (x : K) * (y : K) * (z : K) := by
  rw [diagUnit_val, det_diagonal, Fin.prod_univ_three]
  simp

theorem diagUnit_eq_one {x y z : Kˣ} (h : diagUnit x y z = 1) : x = 1 ∧ y = 1 ∧ z = 1 := by
  have h0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) h
  have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) h
  simp only [diagUnit_val, Units.val_one, diagonal_apply_eq] at h0 h1 h2
  exact ⟨Units.ext (by simpa using h0), Units.ext (by simpa using h1),
    Units.ext (by simpa using h2)⟩

@[expose] def zetaU (ω : Kˣ) (a : ZMod 3) : Kˣ := ω ^ a.val

theorem pow_mod_three {ω : Kˣ} (hω : ω ^ 3 = 1) (n : ℕ) : ω ^ (n % 3) = ω ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hω, one_pow, mul_one]

theorem zetaU_add {ω : Kˣ} (hω : ω ^ 3 = 1) (a b : ZMod 3) :
    zetaU ω (a + b) = zetaU ω a * zetaU ω b := by
  unfold zetaU
  rw [ZMod.val_add, pow_mod_three hω, pow_add]

theorem zetaU_zero (ω : Kˣ) : zetaU ω 0 = 1 := by
  simp [zetaU]

theorem zetaU_eq_one {ω : Kˣ} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (a : ZMod 3) :
    zetaU ω a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hlt := ZMod.val_lt a
    rcases (show a.val = 0 ∨ a.val = 1 ∨ a.val = 2 by omega) with h0 | h1 | h2
    · exact (ZMod.val_eq_zero a).mp h0
    · exfalso
      apply hω1
      simpa [zetaU, h1] using h
    · exfalso
      have h2' : ω ^ 2 = 1 := by simpa [zetaU, h2] using h
      apply hω1
      calc ω = ω ^ 3 := by
            rw [show ω ^ 3 = ω ^ 2 * ω by rw [← pow_succ], h2', one_mul]
        _ = 1 := hω
  · rintro rfl
    exact zetaU_zero ω

@[expose] def E0hom (ω : Kˣ) (hω : ω ^ 3 = 1) :
    Multiplicative (ZMod 3 × ZMod 3) →* GL (Fin 3) K :=
  MonoidHom.mk'
    (fun x => diagUnit (zetaU ω (toAdd x).1) (zetaU ω ((toAdd x).2 - (toAdd x).1))
      (zetaU ω (-(toAdd x).2)))
    (by
      intro x y
      have e1 : (toAdd (x * y)).2 - (toAdd (x * y)).1 =
          ((toAdd x).2 - (toAdd x).1) + ((toAdd y).2 - (toAdd y).1) := by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
        ring
      have e2 : -(toAdd (x * y)).2 = -(toAdd x).2 + -(toAdd y).2 := by
        simp only [toAdd_mul, Prod.snd_add]
        abel
      have e3 : (toAdd (x * y)).1 = (toAdd x).1 + (toAdd y).1 := by
        simp only [toAdd_mul, Prod.fst_add]
      show diagUnit (zetaU ω (toAdd (x * y)).1) (zetaU ω ((toAdd (x * y)).2 - (toAdd (x * y)).1))
          (zetaU ω (-(toAdd (x * y)).2)) = diagUnit (zetaU ω (toAdd x).1)
          (zetaU ω ((toAdd x).2 - (toAdd x).1)) (zetaU ω (-(toAdd x).2)) *
          diagUnit (zetaU ω (toAdd y).1) (zetaU ω ((toAdd y).2 - (toAdd y).1))
          (zetaU ω (-(toAdd y).2))
      rw [e1, e2, e3, zetaU_add hω, zetaU_add hω, zetaU_add hω, diagUnit_mul])

theorem E0hom_apply (ω : Kˣ) (hω : ω ^ 3 = 1) (x : Multiplicative (ZMod 3 × ZMod 3)) :
    E0hom (K := K) ω hω x = diagUnit (zetaU ω (toAdd x).1)
      (zetaU ω ((toAdd x).2 - (toAdd x).1)) (zetaU ω (-(toAdd x).2)) := rfl

theorem E0hom_injective {ω : Kˣ} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    Function.Injective (E0hom (K := K) ω hω) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [E0hom_apply] at hx
  obtain ⟨h1, h2, h3⟩ := diagUnit_eq_one hx
  have ha : (toAdd x).1 = 0 := (zetaU_eq_one hω hω1 _).1 h1
  have hb : (toAdd x).2 - (toAdd x).1 = 0 := (zetaU_eq_one hω hω1 _).1 h2
  have hb' : (toAdd x).2 = 0 := by
    have : (toAdd x).2 = ((toAdd x).2 - (toAdd x).1) + (toAdd x).1 := by ring
    rw [this, hb, ha, zero_add]
  apply toAdd.injective
  exact Prod.ext ha (by simpa using hb')

@[expose] def E0G (ω : Kˣ) (hω : ω ^ 3 = 1) : Subgroup (GL (Fin 3) K) := (E0hom (K := K) ω hω).range

theorem card_E0G [Finite K] {ω : Kˣ} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    Nat.card (E0G (K := K) ω hω) = 9 := by
  unfold E0G
  rw [Nat.card_congr (MonoidHom.ofInjective (E0hom_injective hω hω1)).toEquiv.symm]
  simp [Nat.card_prod, ZMod.card]

theorem E0G_le_statedSL {ω : Kˣ} (hω : ω ^ 3 = 1) :
    E0G (K := K) ω hω ≤ StatedSL 3 K := by
  rintro g ⟨x, rfl⟩
  apply mem_statedSL_of_det
  rw [E0hom_apply, det_diagUnit]
  have hu : zetaU ω (toAdd x).1 * zetaU ω ((toAdd x).2 - (toAdd x).1) *
      zetaU ω (-(toAdd x).2) = 1 := by
    rw [← zetaU_add hω, ← zetaU_add hω]
    have h0 : (toAdd x).1 + ((toAdd x).2 - (toAdd x).1) + -(toAdd x).2 = 0 := by abel
    rw [h0, zetaU_zero]
  have := congrArg (fun u : Kˣ => (u : K)) hu
  simpa using this

theorem E0G_comm {ω : Kˣ} (hω : ω ^ 3 = 1) (g h : GL (Fin 3) K)
    (hg : g ∈ E0G (K := K) ω hω) (hh : h ∈ E0G (K := K) ω hω) : g * h = h * g := by
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨y, rfl⟩ := hh
  rw [← map_mul, ← map_mul, mul_comm]

theorem E0G_pow_three {ω : Kˣ} (hω : ω ^ 3 = 1) (g : GL (Fin 3) K)
    (hg : g ∈ E0G (K := K) ω hω) : g ^ 3 = 1 := by
  obtain ⟨x, rfl⟩ := hg
  rw [← map_pow]
  have : x ^ 3 = 1 := by
    apply toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext <;> simp [nsmul_eq_mul, show (3 : ZMod 3) = 0 by decide]
  rw [this, map_one]

@[expose] def IsUTri (A : Matrix (Fin 3) (Fin 3) K) : Prop :=
  ∀ i j : Fin 3, (j < i → A i j = 0) ∧ (i = j → A i j = 1)

theorem isUTri_one : IsUTri (1 : Matrix (Fin 3) (Fin 3) K) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [Matrix.one_apply, ne_of_gt h]
  · simp [Matrix.one_apply, h]

theorem isUTri_mul {A B : Matrix (Fin 3) (Fin 3) K} (hA : IsUTri A) (hB : IsUTri B) :
    IsUTri (A * B) := by
  intro i j
  constructor
  · intro hji
    rw [mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k < i
    · simp [(hA i k).1 hki]
    · have hjk : j < k := lt_of_lt_of_le hji (not_lt.1 hki)
      simp [(hB k j).1 hjk]
  · intro hij
    subst hij
    rw [mul_apply, Finset.sum_eq_single i]
    · simp [(hA i i).2 rfl, (hB i i).2 rfl]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [(hA i k).1 h]
      · simp [(hB k i).1 h]
    · intro h
      exact absurd (Finset.mem_univ i) h

@[expose] def utriG [Finite K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | IsUTri (g : Matrix (Fin 3) (Fin 3) K)}
  mul_mem' := fun {a b} ha hb => by
    show IsUTri ((a * b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [Units.val_mul]
    exact isUTri_mul ha hb
  one_mem' := by
    show IsUTri ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [Units.val_one]
    exact isUTri_one
  inv_mem' := by
    intro g hg
    have hpow : ∀ n : ℕ, IsUTri ((g ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro n
      induction n with
      | zero => simpa using isUTri_one
      | succ n ih =>
        rw [pow_succ, Units.val_mul]
        exact isUTri_mul ih hg
    have hord : 0 < orderOf g := orderOf_pos g
    have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel hord, pow_orderOf_eq_one]
    show IsUTri ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hinv]
    exact hpow _

theorem mem_utriG [Finite K] (g : GL (Fin 3) K) :
    g ∈ utriG (K := K) ↔ IsUTri (g : Matrix (Fin 3) (Fin 3) K) := Iff.rfl

theorem nil3_cube {N : Matrix (Fin 3) (Fin 3) K} (hN : ∀ i j : Fin 3, j ≤ i → N i j = 0) :
    N * N * N = 0 := by
  have h00 := hN 0 0 (by decide)
  have h11 := hN 1 1 (by decide)
  have h22 := hN 2 2 (by decide)
  have h10 := hN 1 0 (by decide)
  have h20 := hN 2 0 (by decide)
  have h21 := hN 2 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, h00, h11, h22, h10, h20, h21]

theorem pow_four_of_isUTri [CharP K 2] {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUTri A) :
    A ^ 4 = 1 := by
  set N : Matrix (Fin 3) (Fin 3) K := A - 1 with hNdef
  have hA' : A = 1 + N := by rw [hNdef]; abel
  have hN : ∀ i j : Fin 3, j ≤ i → N i j = 0 := by
    intro i j hji
    rw [hNdef, Matrix.sub_apply, Matrix.one_apply]
    rcases lt_or_eq_of_le hji with h | h
    · simp [(hA i j).1 h, ne_of_gt h]
    · subst h
      simp [(hA j j).2 rfl]
  have hNN : N + N = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  have hcube := nil3_cube hN
  have e2 : (1 + N) * (1 + N) = 1 + N * N := by
    calc (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
      _ = 1 + N * N := by rw [hNN, add_zero]
  have e4 : (1 + N * N) * (1 + N * N) = 1 := by
    have h4 : N * N * (N * N) = (N * N * N) * N := by simp only [mul_assoc]
    calc (1 + N * N) * (1 + N * N) = 1 + (N * N + N * N) + N * N * (N * N) := by noncomm_ring
      _ = 1 := by rw [CharTwo.add_self_eq_zero, add_zero, h4, hcube, zero_mul, add_zero]
  have h4' : (1 + N) ^ 4 = ((1 + N) * (1 + N)) * ((1 + N) * (1 + N)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [hA', h4', e2, e4]

theorem diagUnit_inv (x y z : Kˣ) : (diagUnit x y z)⁻¹ = diagUnit x⁻¹ y⁻¹ z⁻¹ := by
  apply Units.ext
  rw [diagUnit_inv_val, diagUnit_val]

theorem isUTri_diag_conj {v w : Fin 3 → K} (hvw : ∀ i, v i * w i = 1)
    {M : Matrix (Fin 3) (Fin 3) K} (hM : IsUTri M) :
    IsUTri (diagonal v * M * diagonal w) := by
  have hent : ∀ i j, (diagonal v * M * diagonal w) i j = v i * M i j * w j := by
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro i j
  constructor
  · intro hji
    rw [hent, (hM i j).1 hji, mul_zero, zero_mul]
  · intro hij
    subst hij
    rw [hent, (hM i i).2 rfl, mul_one, hvw]

theorem conj_diagUnit_mem_utriG [Finite K] (x y z : Kˣ) (u : GL (Fin 3) K) (hu : u ∈ utriG (K := K)) :
    diagUnit x y z * u * (diagUnit x y z)⁻¹ ∈ utriG (K := K) := by
  show IsUTri ((diagUnit x y z * u * (diagUnit x y z)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [Units.val_mul, Units.val_mul, diagUnit_val, diagUnit_inv_val]
  apply isUTri_diag_conj _ hu
  intro i
  fin_cases i <;> simp

theorem diagUnit_mem_normalizer [Finite K] (x y z : Kˣ) :
    diagUnit x y z ∈ Subgroup.normalizer ((utriG (K := K)) : Set (GL (Fin 3) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_diagUnit_mem_utriG x y z h hh
  · intro hX
    have hinv : diagUnit x⁻¹ y⁻¹ z⁻¹ = (diagUnit x y z)⁻¹ := (diagUnit_inv x y z).symm
    have := conj_diagUnit_mem_utriG x⁻¹ y⁻¹ z⁻¹ _ hX
    rw [hinv] at this
    have e : (diagUnit x y z)⁻¹ * (diagUnit x y z * h * (diagUnit x y z)⁻¹) *
        ((diagUnit x y z)⁻¹)⁻¹ = h := by group
    rw [e] at this
    exact this

theorem E0G_le_normalizer_utriG [Finite K] {ω : Kˣ} (hω : ω ^ 3 = 1) :
    E0G (K := K) ω hω ≤ Subgroup.normalizer ((utriG (K := K)) : Set (GL (Fin 3) K)) := by
  rintro g ⟨x, rfl⟩
  rw [E0hom_apply]
  exact diagUnit_mem_normalizer _ _ _

theorem utriG_isPGroup [Finite K] [CharP K 2] : IsPGroup 2 (utriG (K := K)) := by
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, show (2 : ℕ) ^ 2 = 4 from rfl]
  exact pow_four_of_isUTri g.2

def involutionMat : Matrix (Fin 3) (Fin 3) K := 1 + Matrix.single 0 1 1

theorem involutionMat_mul [CharP K 2] : involutionMat (K := K) * involutionMat = 1 := by
  have hE : (Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : K)) + Matrix.single 0 1 1 = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.single_apply]
    split_ifs <;> simp [CharTwo.add_self_eq_zero]
  have hEE : Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : K) * Matrix.single 0 1 1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
  unfold involutionMat
  calc (1 + Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : K)) * (1 + Matrix.single 0 1 1)
      = 1 + (Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : K) + Matrix.single 0 1 1) +
          Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : K) * Matrix.single 0 1 1 := by noncomm_ring
    _ = 1 := by rw [hE, hEE, add_zero, add_zero]

theorem involutionMat_isUTri : IsUTri (involutionMat (K := K)) := by
  intro i j
  constructor
  · intro h
    fin_cases i <;> fin_cases j <;> simp_all [involutionMat, Matrix.single_apply, Matrix.one_apply]
  · intro h
    subst h
    fin_cases i <;> simp [involutionMat, Matrix.single_apply, Matrix.one_apply]

theorem involution_mem_utriG [Finite K] [CharP K 2] :
    ∃ u ∈ utriG (K := K), u ≠ 1 ∧ u ^ 2 = 1 := by
  let g : GL (Fin 3) K := ⟨involutionMat, involutionMat, involutionMat_mul, involutionMat_mul⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · exact involutionMat_isUTri
  · intro h
    have h01 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 1) h
    simp [g, involutionMat, Matrix.single_apply] at h01
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    exact involutionMat_mul

theorem isPGroup_E0G [Finite K] {ω : Kˣ} (hω : ω ^ 3 = 1) :
    IsPGroup 3 (E0G (K := K) ω hω) := by
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  exact E0G_pow_three hω x.1 x.2

end CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor
