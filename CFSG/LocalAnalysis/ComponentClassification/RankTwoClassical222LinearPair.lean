module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Linear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Core
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Pair

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

section NormalForm

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem exists_algEquiv_sqZeroStd {N : Matrix ι ι K} (hN : N * N = 0) (hN0 : N ≠ 0) :
    ∃ (ℓ r : ℕ) (φ : Matrix ι ι K ≃ₐ[K]
      Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K),
      ℓ ≠ 0 ∧ Fintype.card ι = 2 * ℓ + r ∧ φ N = sqZeroStd ℓ r ∧
        ∀ Y, (φ.symm Y).det = Y.det := by
  classical
  set Nl := Matrix.toLin' N with hNl
  have hNl2 : Nl ∘ₗ Nl = 0 := by rw [hNl, ← Matrix.toLin'_mul, hN, map_zero]
  obtain ⟨r, b, hb1, hb2⟩ := exists_basis_sq_eq_zero Nl hNl2
  have hcard : Fintype.card ι = 2 * finrank K (LinearMap.range Nl) + r := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_fintype_fun_eq_card] at h
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega
  have hℓ0 : finrank K (LinearMap.range Nl) ≠ 0 := by
    intro h
    apply hN0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
    rw [← LinearMap.toMatrix'_toLin' N, ← hNl, h, map_zero]
  generalize finrank K (LinearMap.range Nl) = ℓ at b hb1 hb2 hcard hℓ0
  let φ : Matrix ι ι K ≃ₐ[K] Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
    Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)
  refine ⟨ℓ, r, φ, hℓ0, hcard, ?_, fun Y => ?_⟩
  · ext m m'
    simp only [φ, AlgEquiv.trans_apply, LinearMap.toMatrixAlgEquiv_apply,
      Matrix.toLinAlgEquiv'_apply, sqZeroStd_apply]
    have hNv : ∀ v, N *ᵥ v = Nl v := fun v => by rw [hNl, Matrix.toLin'_apply]
    rw [hNv]
    rcases m' with c | c
    · rw [hb1, b.repr_self, Finsupp.single_apply]
      simp [eq_comm]
    · rw [hb2, map_zero]
      rfl
  · have h1 : φ.symm Y = LinearMap.toMatrix' (Matrix.toLin b b Y) := by
      apply φ.injective
      rw [AlgEquiv.apply_symm_apply]
      simp only [φ, AlgEquiv.trans_apply]
      rw [show Matrix.toLinAlgEquiv' (LinearMap.toMatrix' (Matrix.toLin b b Y)) =
        Matrix.toLin b b Y from LinearMap.ext fun v => by
          rw [Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix'_mulVec]]
      exact ((LinearMap.toMatrixAlgEquiv_toLinAlgEquiv b Y)).symm
    rw [h1, LinearMap.det_toMatrix', LinearMap.det_toLin]

end NormalForm

section Kappa

variable {κ K : Type} [Fintype κ] [DecidableEq κ] [Field K]

theorem diagonal_mul_single_mul_diagonal (τ τ' : κ → K) (k k' : κ) (a : K) :
    diagonal τ * single k k' a * diagonal τ' = single k k' (τ k * a * τ' k') := by
  ext m m'
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases h : k = m ∧ k' = m'
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

theorem diagonal_conj_single_eq_smul (τ : κ → K) (k k' : κ) :
    diagonal τ * single k k' (1 : K) * diagonal (fun m => (τ m)⁻¹) =
      (τ k * (τ k')⁻¹) • single k k' 1 := by
  rw [diagonal_mul_single_mul_diagonal, Matrix.smul_single, smul_eq_mul, mul_one, mul_one]

theorem diagonal_commutator_eq (τ : κ → K) (hτ : ∀ m, τ m ≠ 0) {E : Matrix κ κ K}
    (hE : E * E = 0) {ρ : K} (hρ : diagonal τ * E * diagonal (fun m => (τ m)⁻¹) = ρ • E)
    (hρ1 : ρ ≠ 1) :
    diagonal τ * (1 + (ρ - 1)⁻¹ • E) * diagonal (fun m => (τ m)⁻¹) *
      (1 - (ρ - 1)⁻¹ • E) = 1 + E := by
  set s := (ρ - 1)⁻¹ with hs
  have hρ0 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hdd : diagonal τ * diagonal (fun m => (τ m)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext m
    exact mul_inv_cancel₀ (hτ m)
  have h1 : diagonal τ * (1 + s • E) * diagonal (fun m => (τ m)⁻¹) = 1 + s • (ρ • E) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hdd, Matrix.mul_smul, Matrix.smul_mul, hρ]
  rw [h1, add_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    smul_mul_smul_comm, Matrix.smul_mul, hE, smul_zero, smul_zero, sub_zero, smul_smul]
  have h2 : (s * ρ) • E - s • E = E := by
    rw [← sub_smul, show s * ρ - s = s * (ρ - 1) by ring, hs, inv_mul_cancel₀ hρ0, one_smul]
  calc 1 - s • E + (s * ρ) • E = 1 + ((s * ρ) • E - s • E) := by abel
    _ = 1 + E := by rw [h2]

end Kappa

section Std

variable {K : Type} [Field K] {ℓ r : ℕ}

theorem sqZeroStd_inl (j : Fin ℓ) (m' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    sqZeroStd (K := K) ℓ r (.inl j) m' = 0 := by
  rw [sqZeroStd_apply]
  rcases m' with c | c
  · simp
  · rfl

theorem sqZeroStd_inr_inr (k : Fin r) (m' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    sqZeroStd (K := K) ℓ r (.inr (.inr k)) m' = 0 := by
  rw [sqZeroStd_apply]
  rcases m' with c | c
  · simp
  · rfl

theorem sqZeroStd_col_inr (m : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (k : Fin ℓ ⊕ Fin r) :
    sqZeroStd (K := K) ℓ r m (.inr k) = 0 := rfl

theorem single_mul_sqZeroStd_eq_zero {k k' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)}
    (h : ∀ m', sqZeroStd (K := K) ℓ r k' m' = 0) :
    Matrix.single k k' (1 : K) * sqZeroStd ℓ r = 0 := by
  ext m m'
  by_cases hm : m = k
  · subst hm
    rw [single_mul_apply_same, h, mul_zero, Matrix.zero_apply]
  · rw [single_mul_apply_of_ne _ _ _ _ _ hm, Matrix.zero_apply]

theorem sqZeroStd_mul_single_eq_zero {k k' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)}
    (h : ∀ m, sqZeroStd (K := K) ℓ r m k = 0) :
    sqZeroStd ℓ r * Matrix.single k k' (1 : K) = 0 := by
  ext m m'
  by_cases hm : m' = k'
  · subst hm
    rw [mul_single_apply_same, h, zero_mul, Matrix.zero_apply]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hm, Matrix.zero_apply]

theorem sqZeroStd_commute_F (i j : Fin ℓ) :
    (Matrix.single (.inl i) (.inl j) (1 : K) + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) *
        sqZeroStd ℓ r =
      sqZeroStd ℓ r *
        (Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) := by
  rw [Matrix.add_mul, Matrix.mul_add, single_mul_sqZeroStd_eq_zero (sqZeroStd_inl j),
    sqZeroStd_mul_single_eq_zero (fun m => sqZeroStd_col_inr m (.inl i)), zero_add, add_zero]
  ext m m'
  by_cases hm : m = .inr (.inl i)
  · subst hm
    rw [single_mul_apply_same, one_mul]
    by_cases hm' : m' = .inl j
    · subst hm'
      rw [mul_single_apply_same, mul_one, sqZeroStd_apply, sqZeroStd_apply]
      simp
    · rw [mul_single_apply_of_ne _ _ _ _ _ hm', sqZeroStd_apply]
      rcases m' with c | c
      · simp only [Sum.elim_inl]
        rw [ite_eq_right (by intro h; apply hm'; simpa [eq_comm] using h)]
      · rfl
  · rw [single_mul_apply_of_ne _ _ _ _ _ hm]
    by_cases hm' : m' = .inl j
    · subst hm'
      rw [mul_single_apply_same, mul_one, sqZeroStd_apply]
      simp [hm]
    · rw [mul_single_apply_of_ne _ _ _ _ _ hm']

end Std

section Lift

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] [CharP K 2] {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem commute_of_torus_commutator (hZ : Odd (Nat.card (center ↥A)))
    (hH1 : ∀ X : GL ι K, (X : Matrix ι ι K).det = 1 → X ∈ H)
    {κ : Type} [Fintype κ] [DecidableEq κ] (φ : Matrix ι ι K ≃ₐ[K] Matrix κ κ K)
    (hdet : ∀ Y, (φ.symm Y).det = Y.det) {p u : G} {M U : GL ι K} (hpM : Represents e p M)
    (hM2 : M ^ 2 = 1) (hp2 : p ^ 2 = 1) (huU : Represents e u U) (hup : u * p = p * u)
    (hcomm : ∀ h ∈ A ⊓ centralizer ({p} : Set G), ∀ s ∈ A ⊓ centralizer ({p} : Set G),
      (h * s * h⁻¹ * s⁻¹) * u = u * (h * s * h⁻¹ * s⁻¹))
    {E : Matrix κ κ K} (hE2 : E * E = 0) (hEM : E * φ M = φ M * E) {τ : κ → K}
    (hτ0 : ∀ m, τ m ≠ 0) (hτM : diagonal τ * φ M = φ M * diagonal τ) (hτdet : ∏ m, τ m = 1)
    {ρ : K} (hρ : diagonal τ * E * diagonal (fun m => (τ m)⁻¹) = ρ • E) (hρ1 : ρ ≠ 1) :
    φ U * E = E * φ U := by
  set ψ := φ.symm with hψ
  have hφψ : ∀ Y, φ (ψ Y) = Y := fun Y => φ.apply_symm_apply Y
  have hψφ : ∀ X, ψ (φ X) = X := fun X => φ.symm_apply_apply X
  let ψm : Matrix κ κ K →* Matrix ι ι K := ψ.toRingEquiv.toMonoidHom
  have hψm : ∀ Y, ψm Y = ψ Y := fun Y => rfl
  have hdd : diagonal τ * diagonal (fun m => (τ m)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext m
    exact mul_inv_cancel₀ (hτ0 m)
  have hdd' : diagonal (fun m => (τ m)⁻¹) * diagonal τ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext m
    exact inv_mul_cancel₀ (hτ0 m)
  let Dκ : GL κ K := ⟨diagonal τ, diagonal fun m => (τ m)⁻¹, hdd, hdd'⟩
  set sc := (ρ - 1)⁻¹ with hsc
  let Sκ : GL κ K := unipGL E hE2 sc
  let Hm : GL ι K := Units.map ψm Dκ
  let Sm : GL ι K := Units.map ψm Sκ
  have hHv : (Hm : Matrix ι ι K) = ψ (diagonal τ) := rfl
  have hHv' : ((Hm⁻¹ : GL ι K) : Matrix ι ι K) = ψ (diagonal fun m => (τ m)⁻¹) := rfl
  have hSv : (Sm : Matrix ι ι K) = ψ (1 + sc • E) := rfl
  have hSv' : ((Sm⁻¹ : GL ι K) : Matrix ι ι K) = ψ (1 - sc • E) := rfl
  have hMv : (M : Matrix ι ι K) = ψ (φ M) := (hψφ _).symm
  have hHH : Hm ∈ H := hH1 _ (by rw [hHv, hdet, Matrix.det_diagonal, hτdet])
  have hSH : Sm ∈ H := hH1 _ (by
    rw [hSv, hdet]
    have h := det_unipGL hE2 sc
    rwa [coe_unipGL] at h)
  have hHM : Hm * M = M * Hm := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hHv, hMv, ← map_mul, ← map_mul, hτM])
  have hSM : Sm * M = M * Sm := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hSv, hMv, ← map_mul, ← map_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hEM])
  obtain ⟨h, hh⟩ := exists_represents_of_mem (e := e) hHH
  obtain ⟨t, ht⟩ := exists_represents_of_mem (e := e) hSH
  have hhp : h * p = p * h := commute_of_represents hZ hh hpM hp2 hHM
  have htp : t * p = p * t := commute_of_represents hZ ht hpM hp2 hSM
  have hhC : h ∈ A ⊓ centralizer ({p} : Set G) :=
    mem_inf.mpr ⟨hh.1, mem_centralizer_singleton_iff.mpr hhp⟩
  have htC : t ∈ A ⊓ centralizer ({p} : Set G) :=
    mem_inf.mpr ⟨ht.1, mem_centralizer_singleton_iff.mpr htp⟩
  have hcu := hcomm h hhC t htC
  have hrep : Represents e (h * t * h⁻¹ * t⁻¹) (Hm * Sm * Hm⁻¹ * Sm⁻¹) :=
    ((hh.mul ht).mul hh.inv).mul ht.inv
  have hX : ((Hm * Sm * Hm⁻¹ * Sm⁻¹ : GL ι K) : Matrix ι ι K) = ψ (1 + E) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hHv, hSv, hHv', hSv', ← map_mul, ← map_mul,
      ← map_mul, diagonal_commutator_eq τ hτ0 hE2 hρ hρ1]
  set X : GL ι K := Hm * Sm * Hm⁻¹ * Sm⁻¹ with hXdef
  have hXM : (X : Matrix ι ι K) * M = M * X := by
    rw [hX, hMv, ← map_mul, ← map_mul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hEM]
  have hM2' : (M : Matrix ι ι K) * M = 1 := by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hM2
    simpa [sq] using h1
  have hX2 : (X : Matrix ι ι K) * X = 1 := by
    have h1 : (1 + E) * (1 + E) = (1 : Matrix κ κ K) := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hE2, add_zero, add_assoc, matrix_add_self, add_zero]
    rw [hX, ← map_mul, h1, map_one]
  have hMX2 : (M * X) ^ 2 = 1 := Units.ext (by
    rw [sq, Units.val_mul, Units.val_mul, Units.val_one]
    calc (M : Matrix ι ι K) * X * (M * X) = M * ((X : Matrix ι ι K) * M) * X := by
          simp only [Matrix.mul_assoc]
      _ = M * (M * X) * X := by rw [hXM]
      _ = M * M * (X * X) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM2', hX2, Matrix.one_mul])
  have hd : Represents e (p * (h * t * h⁻¹ * t⁻¹)) (M * X) := hpM.mul hrep
  have hud : u * (p * (h * t * h⁻¹ * t⁻¹)) = p * (h * t * h⁻¹ * t⁻¹) * u := by
    rw [← mul_assoc, hup, mul_assoc, ← hcu, ← mul_assoc]
  have hUMX := huU.mul_comm_of_commute hd hMX2 hud
  have hUM := huU.mul_comm_of_commute hpM hM2 hup
  have hUX : (U : Matrix ι ι K) * X = X * U := by
    have h1 : (M : Matrix ι ι K) * (U * X) = M * (X * U) := by
      calc (M : Matrix ι ι K) * (U * X) = U * M * X := by rw [← Matrix.mul_assoc, hUM]
        _ = (M * X) * U := by rw [Matrix.mul_assoc, ← Units.val_mul, hUMX]
        _ = M * (X * U) := by rw [Matrix.mul_assoc]
    have h2 := congrArg (fun Y => (M : Matrix ι ι K) * Y) h1
    simp only [← Matrix.mul_assoc, hM2', Matrix.one_mul] at h2
    exact h2
  have h3 := congrArg φ hUX
  rw [map_mul, map_mul, hX, hφψ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul] at h3
  exact add_left_cancel h3

end Lift

section Tori

variable {K : Type} [Field K] {ℓ r : ℕ}

theorem exists_scalar_ne_zero_ne_one [Finite K] (hK : 3 ≤ Nat.card K) :
    ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 := by
  by_contra h
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · by_cases hx1 : x = 1
      · exact Or.inr hx1
      · exact absurd ⟨x, hx, hx1⟩ h
  have h2 := Set.ncard_le_ncard hsub
  rw [Set.ncard_univ, Set.ncard_pair zero_ne_one] at h2
  omega

theorem mul_self_ne_one_of_ne_one [CharP K 2] {μ : K} (hμ : μ ≠ 1) : μ * μ ≠ 1 := by
  intro h
  apply hμ
  have h1 : (μ + 1) * (μ + 1) = 0 := by
    have e1 : (μ + 1) * (μ + 1) = μ * μ + (μ + μ) + 1 := by ring
    rw [e1, h, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  exact (eq_neg_of_add_eq_zero_left (mul_self_eq_zero.mp h1)).trans (CharTwo.neg_eq 1)

theorem diagonal_commute_one_add_sqZeroStd {τ : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K}
    (hτN : ∀ c, τ (.inl c) = τ (.inr (.inl c))) :
    diagonal τ * (1 + sqZeroStd ℓ r) = (1 + sqZeroStd ℓ r) * diagonal τ := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext m m'
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, sqZeroStd_apply]
  rcases m' with c | c
  · rw [Sum.elim_inl]
    by_cases hm : m = .inr (.inl c)
    · subst hm
      rw [ite_eq_left rfl, mul_one, one_mul, hτN]
    · rw [ite_eq_right hm, mul_zero, zero_mul]
  · rw [Sum.elim_inr, mul_zero, zero_mul]

theorem commute_one_add_sqZeroStd
    {E : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (h : E * sqZeroStd ℓ r = sqZeroStd ℓ r * E) :
    E * (1 + sqZeroStd ℓ r) = (1 + sqZeroStd ℓ r) * E := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h]

theorem prod_torusEntries_eq_one {ι' : Type} [Fintype ι'] [DecidableEq ι'] {i j : ι'}
    (hij : i ≠ j) {μ : K} (hμ : μ ≠ 0) :
    ∏ c, (if c = i then μ else if c = j then μ⁻¹ else 1) = 1 := by
  have h : (fun c => if c = i then μ else if c = j then μ⁻¹ else 1) =
      fun c => Pi.mulSingle i μ c * Pi.mulSingle j μ⁻¹ c := by
    ext c
    by_cases hci : c = i
    · subst hci
      simp [hij]
    · by_cases hcj : c = j
      · subst hcj
        simp [hci]
      · simp [hci, hcj]
  rw [h, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle']
  simp [hμ]

@[expose] def sqZeroTorusX (i j : Fin ℓ) (μ : K) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K :=
  Sum.elim (fun c => if c = i then μ else if c = j then μ⁻¹ else 1)
    (Sum.elim (fun c => if c = i then μ else if c = j then μ⁻¹ else 1) fun _ => 1)

@[expose] def sqZeroTorusY (k k' : Fin r) (μ : K) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K :=
  Sum.elim (fun _ => 1)
    (Sum.elim (fun _ => 1) fun c => if c = k then μ else if c = k' then μ⁻¹ else 1)

theorem sqZeroTorusX_inl_left (i j : Fin ℓ) (μ : K) :
    sqZeroTorusX (r := r) i j μ (.inl i) = μ := by
  simp [sqZeroTorusX]

theorem sqZeroTorusX_inr_left (i j : Fin ℓ) (μ : K) :
    sqZeroTorusX (r := r) i j μ (.inr (.inl i)) = μ := by
  simp [sqZeroTorusX]

theorem sqZeroTorusX_inl_right {i j : Fin ℓ} (hij : i ≠ j) (μ : K) :
    sqZeroTorusX (r := r) i j μ (.inl j) = μ⁻¹ := by
  simp [sqZeroTorusX, hij.symm]

theorem sqZeroTorusX_inr_right {i j : Fin ℓ} (hij : i ≠ j) (μ : K) :
    sqZeroTorusX (r := r) i j μ (.inr (.inl j)) = μ⁻¹ := by
  simp [sqZeroTorusX, hij.symm]

theorem sqZeroTorusX_inr_inr (i j : Fin ℓ) (μ : K) (k : Fin r) :
    sqZeroTorusX i j μ (.inr (.inr k)) = 1 := rfl

theorem sqZeroTorusY_inl (k k' : Fin r) (μ : K) (c : Fin ℓ) :
    sqZeroTorusY k k' μ (.inl c) = 1 := rfl

theorem sqZeroTorusY_inr_inl (k k' : Fin r) (μ : K) (c : Fin ℓ) :
    sqZeroTorusY k k' μ (.inr (.inl c)) = 1 := rfl

theorem sqZeroTorusY_left (k k' : Fin r) (μ : K) :
    sqZeroTorusY (ℓ := ℓ) k k' μ (.inr (.inr k)) = μ := by
  simp [sqZeroTorusY]

theorem sqZeroTorusX_ne_zero {i j : Fin ℓ} {μ : K} (hμ : μ ≠ 0) (m : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    sqZeroTorusX i j μ m ≠ 0 := by
  rcases m with c | c | c <;> simp only [sqZeroTorusX, Sum.elim_inl, Sum.elim_inr] <;>
    (try split_ifs) <;> simp [hμ]

theorem sqZeroTorusY_ne_zero {k k' : Fin r} {μ : K} (hμ : μ ≠ 0) (m : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    sqZeroTorusY k k' μ m ≠ 0 := by
  rcases m with c | c | c <;> simp only [sqZeroTorusY, Sum.elim_inl, Sum.elim_inr] <;>
    (try split_ifs) <;> simp [hμ]

theorem sqZeroTorusX_prod {i j : Fin ℓ} (hij : i ≠ j) {μ : K} (hμ : μ ≠ 0) :
    ∏ m, sqZeroTorusX (r := r) i j μ m = 1 := by
  simp only [sqZeroTorusX, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    prod_torusEntries_eq_one hij hμ, Finset.prod_const_one, mul_one]

theorem sqZeroTorusY_prod {k k' : Fin r} (hkk : k ≠ k') {μ : K} (hμ : μ ≠ 0) :
    ∏ m, sqZeroTorusY (ℓ := ℓ) k k' μ m = 1 := by
  simp only [sqZeroTorusY, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    prod_torusEntries_eq_one hkk hμ, Finset.prod_const_one, one_mul]

theorem sqZeroPairF_mul_self {i j : Fin ℓ} (hij : i ≠ j) :
    ((Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1 :
        Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K) *
      (Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1)) =
    0 := by
  simp [Matrix.add_mul, Matrix.mul_add, hij.symm]

theorem diagonal_sqZeroTorusX_conj_F {i j : Fin ℓ} (hij : i ≠ j) (μ : K) :
    diagonal (sqZeroTorusX (r := r) i j μ) *
        (Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) *
        diagonal (fun m => (sqZeroTorusX i j μ m)⁻¹) =
      (μ * μ) •
        (Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) := by
  rw [Matrix.mul_add, Matrix.add_mul, diagonal_conj_single_eq_smul, diagonal_conj_single_eq_smul,
    sqZeroTorusX_inl_left, sqZeroTorusX_inl_right hij, sqZeroTorusX_inr_left,
    sqZeroTorusX_inr_right hij, inv_inv, smul_add]

end Tori

section Linear

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem pairOrbitFree_linear : PairOrbitFree .linear := by
  intro G _ _ A D hD _ hZ hq p ℓ0 hp
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨hpo, M, hpM, hM2, -⟩ := hp
    have hp2' : p ^ 2 = 1 := by rw [← hpo]; exact pow_orderOf_eq_one p
    have hp1 : p * p = 1 := by rw [← sq]; exact hp2'
    have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hM1 : M ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hM2
      omega
    have hSL : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K).det = 1 →
        X ∈ StatedSL n K := fun X hX => subset_closure hX
    obtain ⟨μ, hμ0, hμ1⟩ := exists_scalar_ne_zero_ne_one (K := K) (by
      have h4 : 4 ≤ 2 ^ m := hq
      omega)
    have hμ2 : μ * μ ≠ 1 := mul_self_ne_one_of_ne_one hμ1
    set N := (M : Matrix (Fin n) (Fin n) K) - 1 with hNdef
    have hE : N * N = 0 := sub_one_mul_self hMsq
    have hN0 : N ≠ 0 := sub_one_ne_zero hM1
    have hMN : (M : Matrix (Fin n) (Fin n) K) = 1 + N := (add_sub_cancel 1 _).symm
    obtain ⟨l, r, φ, hl0, hcardι, hφN, hdet⟩ := exists_algEquiv_sqZeroStd hE hN0
    rw [Fintype.card_fin] at hcardι
    have hφM : φ (M : Matrix (Fin n) (Fin n) K) = 1 + sqZeroStd l r := by
      rw [hMN, map_add, map_one, hφN]
    refine noPairOrbit_of_commutator hp1 fun u hu hu2 hC a ha => ?_
    obtain ⟨U, hU⟩ := exists_represents e (mem_inf.mp hu).1
    have hup : u * p = p * u := mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2
    have hcomm : ∀ h ∈ A ⊓ centralizer ({p} : Set G), ∀ s ∈ A ⊓ centralizer ({p} : Set G),
        (h * s * h⁻¹ * s⁻¹) * u = u * (h * s * h⁻¹ * s⁻¹) := fun h hh s hs => by
      have h1 := mem_centralizer_singleton_iff.mp (hC (commutator_mem_commutator hh hs))
      rwa [commutatorElement_def] at h1
    have key : ∀ (E : Matrix (Fin l ⊕ (Fin l ⊕ Fin r)) (Fin l ⊕ (Fin l ⊕ Fin r)) K)
        (τ : Fin l ⊕ (Fin l ⊕ Fin r) → K), E * E = 0 →
        E * sqZeroStd l r = sqZeroStd l r * E → (∀ m, τ m ≠ 0) →
        (∀ c, τ (.inl c) = τ (.inr (.inl c))) → ∏ m, τ m = 1 → ∀ ρ : K,
        diagonal τ * E * diagonal (fun m => (τ m)⁻¹) = ρ • E → ρ ≠ 1 →
        φ U * E = E * φ U := by
      intro E τ hE2 hES hτ0 hτN hτdet ρ hρ hρ1
      refine commute_of_torus_commutator hZ hSL φ hdet hpM hMsq hp2' hU hup hcomm hE2 ?_ hτ0 ?_
        hτdet hρ hρ1
      · rw [hφM]
        exact commute_one_add_sqZeroStd hES
      · rw [hφM]
        exact diagonal_commute_one_add_sqZeroStd hτN
    have keyS : ∀ (k k' : Fin l ⊕ (Fin l ⊕ Fin r)) (τ : Fin l ⊕ (Fin l ⊕ Fin r) → K), k' ≠ k →
        Matrix.single k k' (1 : K) * sqZeroStd l r = sqZeroStd l r * Matrix.single k k' 1 →
        (∀ m, τ m ≠ 0) → (∀ c, τ (.inl c) = τ (.inr (.inl c))) → ∏ m, τ m = 1 →
        τ k * (τ k')⁻¹ ≠ 1 → φ U * Matrix.single k k' 1 = Matrix.single k k' 1 * φ U :=
      fun k k' τ hkk hES hτ0 hτN hτdet hρ1 =>
        key _ τ (single_mul_single_of_ne (1 : K) k k' k hkk 1) hES hτ0 hτN hτdet _
          (diagonal_conj_single_eq_smul τ k k') hρ1
    have hC1 : ∀ i j : Fin l, i ≠ j →
        φ U * Matrix.single (.inr (.inl i)) (.inl j) 1 =
          Matrix.single (.inr (.inl i)) (.inl j) 1 * φ U := fun i j hij =>
      keyS (.inr (.inl i)) (.inl j) (sqZeroTorusX i j μ) Sum.inl_ne_inr
        (by rw [single_mul_sqZeroStd_eq_zero (sqZeroStd_inl j),
          sqZeroStd_mul_single_eq_zero fun m => sqZeroStd_col_inr m (.inl i)])
        (sqZeroTorusX_ne_zero hμ0) (fun _ => rfl) (sqZeroTorusX_prod hij hμ0)
        (by rw [sqZeroTorusX_inr_left, sqZeroTorusX_inl_right hij, inv_inv]; exact hμ2)
    have hC2 : ∀ (k : Fin r) (j : Fin l),
        φ U * Matrix.single (.inr (.inr k)) (.inl j) 1 =
          Matrix.single (.inr (.inr k)) (.inl j) 1 * φ U := by
      intro k j
      have hES : Matrix.single (.inr (.inr k)) (.inl j) (1 : K) * sqZeroStd l r =
          sqZeroStd l r * Matrix.single (.inr (.inr k)) (.inl j) 1 := by
        rw [single_mul_sqZeroStd_eq_zero (sqZeroStd_inl j),
          sqZeroStd_mul_single_eq_zero fun m => sqZeroStd_col_inr m (.inr k)]
      rcases Nat.lt_or_ge l 2 with hl1 | hl2
      · have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
        obtain ⟨k', hk'⟩ := exists_ne k
        exact keyS (.inr (.inr k)) (.inl j) (sqZeroTorusY k k' μ) Sum.inl_ne_inr hES
          (sqZeroTorusY_ne_zero hμ0) (fun _ => rfl) (sqZeroTorusY_prod hk'.symm hμ0)
          (by rw [sqZeroTorusY_left, sqZeroTorusY_inl, inv_one, mul_one]; exact hμ1)
      · have : Nontrivial (Fin l) := Fin.nontrivial_iff_two_le.mpr hl2
        obtain ⟨j', hj'⟩ := exists_ne j
        exact keyS (.inr (.inr k)) (.inl j) (sqZeroTorusX j j' μ) Sum.inl_ne_inr hES
          (sqZeroTorusX_ne_zero hμ0) (fun _ => rfl) (sqZeroTorusX_prod hj'.symm hμ0)
          (by
            rw [sqZeroTorusX_inr_inr, sqZeroTorusX_inl_left, one_mul]
            exact inv_ne_one.mpr hμ1)
    have hC3 : ∀ (i : Fin l) (k : Fin r),
        φ U * Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 =
          Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 * φ U := by
      intro i k
      have hES : Matrix.single (.inr (.inl i)) (.inr (.inr k)) (1 : K) * sqZeroStd l r =
          sqZeroStd l r * Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 := by
        rw [single_mul_sqZeroStd_eq_zero (sqZeroStd_inr_inr k),
          sqZeroStd_mul_single_eq_zero fun m => sqZeroStd_col_inr m (.inl i)]
      have hkk : (Sum.inr (Sum.inr k) : Fin l ⊕ (Fin l ⊕ Fin r)) ≠ .inr (.inl i) := by simp
      rcases Nat.lt_or_ge l 2 with hl1 | hl2
      · have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
        obtain ⟨k', hk'⟩ := exists_ne k
        exact keyS (.inr (.inl i)) (.inr (.inr k)) (sqZeroTorusY k k' μ) hkk hES
          (sqZeroTorusY_ne_zero hμ0) (fun _ => rfl) (sqZeroTorusY_prod hk'.symm hμ0)
          (by
            rw [sqZeroTorusY_inr_inl, sqZeroTorusY_left, one_mul]
            exact inv_ne_one.mpr hμ1)
      · have : Nontrivial (Fin l) := Fin.nontrivial_iff_two_le.mpr hl2
        obtain ⟨i', hi'⟩ := exists_ne i
        exact keyS (.inr (.inl i)) (.inr (.inr k)) (sqZeroTorusX i i' μ) hkk hES
          (sqZeroTorusX_ne_zero hμ0) (fun _ => rfl) (sqZeroTorusX_prod hi'.symm hμ0)
          (by rw [sqZeroTorusX_inr_left, sqZeroTorusX_inr_inr, inv_one, mul_one]; exact hμ1)
    have hC4 : ∀ i j : Fin l, i ≠ j →
        φ U * (Matrix.single (.inl i) (.inl j) 1 +
          Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) =
        (Matrix.single (.inl i) (.inl j) 1 +
          Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) * φ U := fun i j hij =>
      key _ (sqZeroTorusX i j μ) (sqZeroPairF_mul_self hij) (sqZeroStd_commute_F i j)
        (sqZeroTorusX_ne_zero hμ0) (fun _ => rfl) (sqZeroTorusX_prod hij hμ0) (μ * μ)
        (diagonal_sqZeroTorusX_conj_F hij μ) hμ2
    have hUM := hU.mul_comm_of_commute hpM hMsq hup
    have hUN : (U : Matrix (Fin n) (Fin n) K) * N = N * U := by
      rw [hNdef, mul_sub, sub_mul, hUM, mul_one, one_mul]
    have hBN : φ U * sqZeroStd l r = sqZeroStd l r * φ U := by
      rw [← hφN, ← map_mul, ← map_mul, hUN]
    obtain ⟨c, d, hcd⟩ := commutant_kappa hl0 (by omega) hBN hC1 hC2 hC3 hC4
    have hUcd : (U : Matrix (Fin n) (Fin n) K) = c • 1 + d • N := by
      apply φ.injective
      rw [hcd, map_add, map_smul, map_smul, map_one, hφN]
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hUU : (U : Matrix (Fin n) (Fin n) K) * U = 0 := by
        rw [hUcd, zero_smul, zero_add, smul_mul_smul_comm, hE, smul_zero]
      have hu : IsUnit ((U : Matrix (Fin n) (Fin n) K) * U) :=
        (Units.isUnit U).mul (Units.isUnit U)
      rw [hUU] at hu
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      exact not_isUnit_zero hu
    have hrep : Represents e u (unipGL N hE (d / c)) :=
      hU.of_eq_mul_scalar (hSL _ (det_unipGL hE _)) (c := Units.mk0 c hc0) (Units.ext (by
        rw [hUcd, Units.val_mul, coe_unipGL, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
          Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, add_mul, Matrix.one_mul,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
        have hcd' : c * (d / c) = d := by field_simp
        rw [hcd']))
    have hmem : u ∈ alphaGroup e p :=
      subset_closure ⟨⟨1, by rw [pow_one]; exact hu2⟩, M, unipGL N hE (d / c), hpM, hM2, hrep,
        d / c, by rw [coe_unipGL, add_sub_cancel_left]⟩
    have hau : a * u = u * a :=
      mem_centralizer_iff.mp (alphaGroup_le_centralizer hZ hpM hM2 hmem) a ha
    rw [hau, mul_inv_cancel_right]
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end Linear

end CFSG.ComponentClassification.RankTwoClassical
