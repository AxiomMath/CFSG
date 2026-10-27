module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Universal.Unitary.Roots.Generation

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.LieType.Universal.Unitary

namespace T7L

section SU4

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def smat {n : ℕ} (g : SU σ n) : Matrix (Fin n) (Fin n) K :=
  ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem smat_mul {n : ℕ} (g h : SU σ n) : smat (g * h) = smat g * smat h := rfl

theorem smat_inj {n : ℕ} {g h : SU σ n} (e : smat g = smat h) : g = h := Subtype.ext (Units.ext e)

theorem smat_one {n : ℕ} : smat (1 : SU σ n) = 1 := rfl

theorem antidiag_four : (antidiag 4 : Matrix (Fin 4) (Fin 4) K) =
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag, Fin.rev]


@[expose] noncomputable def diagSU {n : ℕ} (d d' : Fin n → K) (h1 : ∀ i, d i * d' i = 1)
    (hdet : ∏ i, d i = 1) (hiso : ∀ i, σ (d i) * d (Fin.rev i) = 1) : SU σ n :=
  ⟨⟨Matrix.diagonal d, Matrix.diagonal d', by
      rw [diagonal_mul_diagonal, show (fun i => d i * d' i) = fun _ => 1 from funext h1,
        diagonal_one],
    by
      rw [diagonal_mul_diagonal, show (fun i => d' i * d i) = fun _ => 1 from
        funext fun i => by rw [mul_comm]; exact h1 i, diagonal_one]⟩,
    by
      show (Matrix.diagonal d).det = 1
      rw [det_diagonal, hdet],
    by
      show conjTr σ (Matrix.diagonal d) * antidiag n * Matrix.diagonal d = antidiag n
      ext i j
      have hc : conjTr σ (Matrix.diagonal d) = Matrix.diagonal fun i => σ (d i) := by
        rw [conjTr, diagonal_map (map_zero σ), diagonal_transpose]
      rw [hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hij : j = Fin.rev i
      · subst hij
        simp only [antidiag, of_apply, ite_true]
        calc σ (d i) * 1 * d (Fin.rev i) = σ (d i) * d (Fin.rev i) := by ring
          _ = 1 := hiso i
      · simp [antidiag, hij]⟩

theorem smat_diagSU {n : ℕ} (d d' : Fin n → K) (h1 : ∀ i, d i * d' i = 1)
    (hdet : ∏ i, d i = 1) (hiso : ∀ i, σ (d i) * d (Fin.rev i) = 1) :
    smat (diagSU (σ := σ) d d' h1 hdet hiso) = Matrix.diagonal d := rfl


@[expose] noncomputable def XelU (σ : K ≃+* K) : SU σ 4 :=
  diagSU ![-1, 1, 1, -1] ![-1, 1, 1, -1] (by intro i; fin_cases i <;> simp)
    (by simp [Fin.prod_univ_four]) (by intro i; fin_cases i <;> simp [Fin.rev])

@[expose] noncomputable def DelU (σ : K ≃+* K) {ω : K} (hω : ω * ω = -1) (hσω : σ ω = ω) : SU σ 4 :=
  diagSU ![ω, ω, -ω, -ω] ![-ω, -ω, ω, ω]
    (by intro i; fin_cases i <;> simp <;> linear_combination -hω)
    (by simp [Fin.prod_univ_four]; linear_combination (ω * ω - 1) * hω)
    (by intro i; fin_cases i <;> simp [Fin.rev, hσω] <;> linear_combination -hω)

theorem smat_XelU : smat (XelU σ) = Matrix.diagonal ![-1, 1, 1, -1] := rfl

theorem smat_DelU {ω : K} (hω : ω * ω = -1) (hσω : σ ω = ω) :
    smat (DelU σ hω hσω) = Matrix.diagonal ![ω, ω, -ω, -ω] := rfl


theorem rootMatrix_comm_diagonal {n : ℕ} (i j : Fin n) (c : K) (d : Fin n → K) (h1 : d i = d j)
    (h2 : d (Fin.rev j) = d (Fin.rev i)) :
    rootMatrix σ i j c * Matrix.diagonal d = Matrix.diagonal d * rootMatrix σ i j c := by
  ext a b
  simp only [rootMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hdab : d a = d b
  · rw [hdab]
    ring
  · have h3 : ¬ (i = a ∧ j = b) := fun h => hdab (by obtain ⟨rfl, rfl⟩ := h; exact h1)
    have h4 : ¬ (Fin.rev j = a ∧ Fin.rev i = b) := fun h =>
      hdab (by obtain ⟨rfl, rfl⟩ := h; exact h2)
    have h5 : a ≠ b := fun h => hdab (by rw [h])
    simp [h3, h4, h5]

theorem longRootMatrix_comm_diagonal {n : ℕ} (i : Fin n) (c : K) (d : Fin n → K)
    (h1 : d i = d (Fin.rev i)) :
    longRootMatrix i c * Matrix.diagonal d = Matrix.diagonal d * longRootMatrix i c := by
  ext a b
  simp only [longRootMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hdab : d a = d b
  · rw [hdab]
    ring
  · have h3 : ¬ (i = a ∧ Fin.rev i = b) := fun h => hdab (by obtain ⟨rfl, rfl⟩ := h; exact h1)
    have h5 : a ≠ b := fun h => hdab (by rw [h])
    simp [h3, h5]

theorem comm_upper (c μ : K) (hμ : σ μ = -μ) :
    rootMatrix σ (0 : Fin 4) 1 c * longRootMatrix (1 : Fin 4) μ * rootMatrix σ (0 : Fin 4) 1 (-c) =
      longRootMatrix (1 : Fin 4) μ * rootMatrix σ (0 : Fin 4) 2 (μ * c) *
        longRootMatrix (0 : Fin 4) (μ * (σ c * c)) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, longRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
      Fin.rev, hμ] <;> ring

theorem comm_lower (c μ : K) (hμ : σ μ = -μ) :
    rootMatrix σ (1 : Fin 4) 0 c * longRootMatrix (2 : Fin 4) μ * rootMatrix σ (1 : Fin 4) 0 (-c) =
      longRootMatrix (2 : Fin 4) μ * rootMatrix σ (2 : Fin 4) 0 (-(μ * c)) *
        longRootMatrix (3 : Fin 4) (μ * (σ c * c)) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, longRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
      Fin.rev, hμ] <;> ring

theorem root13_eq (hσ : ∀ c, σ (σ c) = c) (c : K) :
    rootMatrix σ (1 : Fin 4) 3 c = rootMatrix σ (0 : Fin 4) 2 (-σ c) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, Fin.rev, hσ]

theorem root31_eq (hσ : ∀ c, σ (σ c) = c) (c : K) :
    rootMatrix σ (3 : Fin 4) 1 c = rootMatrix σ (2 : Fin 4) 0 (-σ c) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, Fin.rev, hσ]


section Gen

variable (σ)

theorem rootHom_smat (hσ : ∀ c, σ (σ c) = c) {i j : Fin 4} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (c : Multiplicative K) :
    smat (rootHom σ hσ hij hi hj c) = rootMatrix σ i j c.toAdd := rfl

theorem longRootHom_smat {i : Fin 4} (hi : i ≠ Fin.rev i) (c : Multiplicative (traceZero σ)) :
    smat (longRootHom σ hi c) = longRootMatrix i (c.toAdd : K) := rfl

variable {σ}

theorem top_le_XD (hσ : ∀ c, σ (σ c) = c) (hζ : ∃ ζ : K, ζ ≠ 0 ∧ ζ + σ ζ = 0)
    (htr : ∀ x, σ x = x → ∃ c, c + σ c = x) (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x)
    {ω : K} (hω : ω * ω = -1) (hσω : σ ω = ω) :
    (⊤ : Subgroup (SU σ 4)) ≤ Subgroup.centralizer ({XelU σ} : Set (SU σ 4)) ⊔
      Subgroup.centralizer ({DelU σ hω hσω} : Set (SU σ 4)) := by
  set R : Subgroup (SU σ 4) := Subgroup.centralizer ({XelU σ} : Set (SU σ 4)) ⊔
    Subgroup.centralizer ({DelU σ hω hσω} : Set (SU σ 4)) with hR
  have inX : ∀ g : SU σ 4, smat g * smat (XelU σ) = smat (XelU σ) * smat g → g ∈ R := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr
      (smat_inj (by rw [smat_mul, smat_mul]; exact hg)))
  have inD : ∀ g : SU σ 4, smat g * smat (DelU σ hω hσω) = smat (DelU σ hω hσω) * smat g →
      g ∈ R := fun g hg =>
    Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr
      (smat_inj (by rw [smat_mul, smat_mul]; exact hg)))
  have hshort : ∀ (i j : Fin 4) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j)
      (c : Multiplicative K), (![ω, ω, -ω, -ω] : Fin 4 → K) i = ![ω, ω, -ω, -ω] j →
      (![ω, ω, -ω, -ω] : Fin 4 → K) (Fin.rev j) = ![ω, ω, -ω, -ω] (Fin.rev i) →
      rootHom σ hσ hij hi hj c ∈ R := by
    intro i j hij hi hj c h1 h2
    refine inD _ ?_
    rw [rootHom_smat, smat_DelU]
    exact rootMatrix_comm_diagonal i j _ _ h1 h2
  have hlong : ∀ (i : Fin 4) (hi : i ≠ Fin.rev i) (c : Multiplicative (traceZero σ)),
      (![-1, 1, 1, -1] : Fin 4 → K) i = ![-1, 1, 1, -1] (Fin.rev i) → longRootHom σ hi c ∈ R := by
    intro i hi c h1
    refine inX _ ?_
    rw [longRootHom_smat, smat_XelU]
    exact longRootMatrix_comm_diagonal i _ _ h1
  obtain ⟨ζ, hζ0, hζt⟩ := hζ
  have hζσ : σ ζ = -ζ := by linear_combination hζt
  have hN : ∀ c₁ : K, ζ * (σ c₁ * c₁) + σ (ζ * (σ c₁ * c₁)) = 0 := by
    intro c₁
    rw [map_mul, map_mul, hσ, hζσ]
    ring
  have h02 : ∀ c : K, rootHom σ hσ (show (0 : Fin 4) ≠ 2 by decide) (by decide) (by decide)
      (Multiplicative.ofAdd c) ∈ R := by
    intro c
    have hc : ζ * (c / ζ) = c := by field_simp
    set c₁ := c / ζ with hc₁
    set a : SU σ 4 := rootHom σ hσ (show (0 : Fin 4) ≠ 1 by decide) (by decide) (by decide)
      (Multiplicative.ofAdd c₁) with ha
    set l1 : SU σ 4 := longRootHom σ (show (1 : Fin 4) ≠ Fin.rev 1 by decide)
      (Multiplicative.ofAdd (⟨ζ, hζt⟩ : traceZero σ)) with hl1
    set l0 : SU σ 4 := longRootHom σ (show (0 : Fin 4) ≠ Fin.rev 0 by decide)
      (Multiplicative.ofAdd (⟨ζ * (σ c₁ * c₁), hN c₁⟩ : traceZero σ)) with hl0
    set q : SU σ 4 := rootHom σ hσ (show (0 : Fin 4) ≠ 2 by decide) (by decide) (by decide)
      (Multiplicative.ofAdd c) with hq
    have key : l1 * q * l0 = a * l1 * a⁻¹ := by
      apply smat_inj
      have ha_inv : smat a⁻¹ = rootMatrix σ (0 : Fin 4) 1 (-c₁) := by
        have : a⁻¹ = rootHom σ hσ (show (0 : Fin 4) ≠ 1 by decide) (by decide) (by decide)
            (Multiplicative.ofAdd (-c₁)) := by
          rw [ha, ← map_inv]
          rfl
        rw [this]
        rfl
      rw [smat_mul, smat_mul, smat_mul, smat_mul, ha_inv]
      show longRootMatrix (1 : Fin 4) ζ * rootMatrix σ (0 : Fin 4) 2 c *
        longRootMatrix (0 : Fin 4) (ζ * (σ c₁ * c₁)) = rootMatrix σ (0 : Fin 4) 1 c₁ *
          longRootMatrix (1 : Fin 4) ζ * rootMatrix σ (0 : Fin 4) 1 (-c₁)
      rw [← hc]
      exact (comm_upper c₁ ζ hζσ).symm
    have hqe : q = l1⁻¹ * (a * l1 * a⁻¹) * l0⁻¹ := by
      rw [← key]
      group
    have hamem : a ∈ R := hshort _ _ _ _ _ _ (by simp) (by simp [Fin.rev])
    have hl1m : l1 ∈ R := hlong _ _ _ (by simp [Fin.rev])
    have hl0m : l0 ∈ R := hlong _ _ _ (by simp [Fin.rev])
    rw [hqe]
    exact R.mul_mem (R.mul_mem (R.inv_mem hl1m)
      (R.mul_mem (R.mul_mem hamem hl1m) (R.inv_mem hamem))) (R.inv_mem hl0m)
  have h20 : ∀ x : K, rootHom σ hσ (show (2 : Fin 4) ≠ 0 by decide) (by decide) (by decide)
      (Multiplicative.ofAdd x) ∈ R := by
    intro x
    have hc : -(ζ * (-(x / ζ))) = x := by field_simp
    set c₁ := -(x / ζ) with hc₁
    set a : SU σ 4 := rootHom σ hσ (show (1 : Fin 4) ≠ 0 by decide) (by decide) (by decide)
      (Multiplicative.ofAdd c₁) with ha
    set l2 : SU σ 4 := longRootHom σ (show (2 : Fin 4) ≠ Fin.rev 2 by decide)
      (Multiplicative.ofAdd (⟨ζ, hζt⟩ : traceZero σ)) with hl2
    set l3 : SU σ 4 := longRootHom σ (show (3 : Fin 4) ≠ Fin.rev 3 by decide)
      (Multiplicative.ofAdd (⟨ζ * (σ c₁ * c₁), hN c₁⟩ : traceZero σ)) with hl3
    set q : SU σ 4 := rootHom σ hσ (show (2 : Fin 4) ≠ 0 by decide) (by decide) (by decide)
      (Multiplicative.ofAdd x) with hq
    have key : l2 * q * l3 = a * l2 * a⁻¹ := by
      apply smat_inj
      have ha_inv : smat a⁻¹ = rootMatrix σ (1 : Fin 4) 0 (-c₁) := by
        have : a⁻¹ = rootHom σ hσ (show (1 : Fin 4) ≠ 0 by decide) (by decide) (by decide)
            (Multiplicative.ofAdd (-c₁)) := by
          rw [ha, ← map_inv]
          rfl
        rw [this]
        rfl
      rw [smat_mul, smat_mul, smat_mul, smat_mul, ha_inv]
      show longRootMatrix (2 : Fin 4) ζ * rootMatrix σ (2 : Fin 4) 0 x *
        longRootMatrix (3 : Fin 4) (ζ * (σ c₁ * c₁)) = rootMatrix σ (1 : Fin 4) 0 c₁ *
          longRootMatrix (2 : Fin 4) ζ * rootMatrix σ (1 : Fin 4) 0 (-c₁)
      rw [← hc]
      exact (comm_lower c₁ ζ hζσ).symm
    have hqe : q = l2⁻¹ * (a * l2 * a⁻¹) * l3⁻¹ := by
      rw [← key]
      group
    have hamem : a ∈ R := hshort _ _ _ _ _ _ (by simp) (by simp [Fin.rev])
    have hl2m : l2 ∈ R := hlong _ _ _ (by simp [Fin.rev])
    have hl3m : l3 ∈ R := hlong _ _ _ (by simp [Fin.rev])
    rw [hqe]
    exact R.mul_mem (R.mul_mem (R.inv_mem hl2m)
      (R.mul_mem (R.mul_mem hamem hl2m) (R.inv_mem hamem))) (R.inv_mem hl3m)
  have h13 : ∀ c : K, rootHom σ hσ (show (1 : Fin 4) ≠ 3 by decide) (by decide) (by decide)
      (Multiplicative.ofAdd c) ∈ R := by
    intro c
    have : rootHom σ hσ (show (1 : Fin 4) ≠ 3 by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) = rootHom σ hσ (show (0 : Fin 4) ≠ 2 by decide) (by decide)
          (by decide) (Multiplicative.ofAdd (-σ c)) := smat_inj (root13_eq hσ c)
    rw [this]
    exact h02 _
  have h31 : ∀ c : K, rootHom σ hσ (show (3 : Fin 4) ≠ 1 by decide) (by decide) (by decide)
      (Multiplicative.ofAdd c) ∈ R := by
    intro c
    have : rootHom σ hσ (show (3 : Fin 4) ≠ 1 by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) = rootHom σ hσ (show (2 : Fin 4) ≠ 0 by decide) (by decide)
          (by decide) (Multiplicative.ofAdd (-σ c)) := smat_inj (root31_eq hσ c)
    rw [this]
    exact h20 _
  have hRtop : R = ⊤ := by
    refine eq_top_of_rootElements_le hσ ⟨ζ, hζ0, hζt⟩ htr hnorm (by norm_num) R ?_ ?_ ?_
    · intro i j hij hi hj hji c
      fin_cases i <;> fin_cases j <;> simp [Fin.rev] at hij hji ⊢
      · exact hshort _ _ _ _ _ _ (by simp) (by simp [Fin.rev])
      · exact h02 c.toAdd
      · exact hshort _ _ _ _ _ _ (by simp) (by simp [Fin.rev])
      · exact h13 c.toAdd
      · exact h20 c.toAdd
      · exact hshort _ _ _ _ _ _ (by simp) (by simp [Fin.rev])
      · exact h31 c.toAdd
      · exact hshort _ _ _ _ _ _ (by simp) (by simp [Fin.rev])
    · intro i hi c
      fin_cases i <;> exact hlong _ _ _ (by simp [Fin.rev])
    · intro i k hi hik hk
      exfalso
      fin_cases k <;> simp [Fin.rev] at hk
  exact hRtop.ge

end Gen

end SU4

end T7L

end CFSG.ClassicalInvolution.Asc77
