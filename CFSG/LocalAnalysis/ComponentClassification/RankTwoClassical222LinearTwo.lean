module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222TwoB

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard

theorem one_add_commutator_eq {R : Type} [Ring R] {E F : R} (hE : E * E = 0) (hF : F * F = 0)
    (hFE : F * E = 0) : (1 + E) * (1 + F) * (1 - E) * (1 - F) = 1 + E * F := by
  have hE' : ∀ X : R, E * (E * X) = 0 := fun X => by rw [← mul_assoc, hE, zero_mul]
  have hFE' : ∀ X : R, F * (E * X) = 0 := fun X => by rw [← mul_assoc, hFE, zero_mul]
  have h : (1 + E) * (1 + F) * (1 - E) * (1 - F) = 1 + E * F - E * E - F * E - F * F +
      E * (E * F) + F * (E * F) - E * (F * E) - E * (F * F) + E * (F * (E * F)) := by
    noncomm_ring
  rw [h]
  simp only [hE, hF, hFE, hE', hFE', mul_zero, sub_zero, add_zero]

section NormalForm

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem exists_algEquiv_sqZeroStd_rank {N : Matrix ι ι K} (hN : N * N = 0) (hN0 : N ≠ 0) :
    ∃ (ℓ r : ℕ) (φ : Matrix ι ι K ≃ₐ[K]
      Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K),
      ℓ = N.rank ∧ ℓ ≠ 0 ∧ Fintype.card ι = 2 * ℓ + r ∧ φ N = sqZeroStd ℓ r ∧
        ∀ Y, (φ.symm Y).det = Y.det := by
  classical
  set Nl := Matrix.toLin' N with hNl
  have hNl2 : Nl ∘ₗ Nl = 0 := by rw [hNl, ← Matrix.toLin'_mul, hN, map_zero]
  obtain ⟨r, b, hb1, hb2⟩ := exists_basis_sq_eq_zero Nl hNl2
  have hrank : finrank K (LinearMap.range Nl) = N.rank := rfl
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
  generalize finrank K (LinearMap.range Nl) = ℓ at b hb1 hb2 hcard hℓ0 hrank
  let φ : Matrix ι ι K ≃ₐ[K] Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
    Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)
  refine ⟨ℓ, r, φ, hrank, hℓ0, hcard, ?_, fun Y => ?_⟩
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

section Lift

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] [CharP K 2] {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem commute_of_root_commutator (hZ : Odd (Nat.card (center ↥A)))
    (hH1 : ∀ X : GL ι K, (X : Matrix ι ι K).det = 1 → X ∈ H)
    {κ : Type} [Fintype κ] [DecidableEq κ] (φ : Matrix ι ι K ≃ₐ[K] Matrix κ κ K)
    (hdet : ∀ Y, (φ.symm Y).det = Y.det) {p u : G} {M U : GL ι K} (hpM : Represents e p M)
    (hM2 : M ^ 2 = 1) (hp2 : p ^ 2 = 1) (huU : Represents e u U) (hup : u * p = p * u)
    (hcomm : ∀ h ∈ A ⊓ centralizer ({p} : Set G), ∀ s ∈ A ⊓ centralizer ({p} : Set G),
      (h * s * h⁻¹ * s⁻¹) * u = u * (h * s * h⁻¹ * s⁻¹))
    {E F : Matrix κ κ K} (hE2 : E * E = 0) (hF2 : F * F = 0) (hFE : F * E = 0)
    (hEM : E * φ M = φ M * E) (hFM : F * φ M = φ M * F) :
    φ U * (E * F) = (E * F) * φ U := by
  set ψ := φ.symm with hψ
  have hφψ : ∀ Y, φ (ψ Y) = Y := fun Y => φ.apply_symm_apply Y
  have hψφ : ∀ X, ψ (φ X) = X := fun X => φ.symm_apply_apply X
  let ψm : Matrix κ κ K →* Matrix ι ι K := ψ.toRingEquiv.toMonoidHom
  let Hm : GL ι K := Units.map ψm (unipGL E hE2 1)
  let Sm : GL ι K := Units.map ψm (unipGL F hF2 1)
  have hHv : (Hm : Matrix ι ι K) = ψ (1 + (1 : K) • E) := rfl
  have hHv' : ((Hm⁻¹ : GL ι K) : Matrix ι ι K) = ψ (1 - (1 : K) • E) := rfl
  have hSv : (Sm : Matrix ι ι K) = ψ (1 + (1 : K) • F) := rfl
  have hSv' : ((Sm⁻¹ : GL ι K) : Matrix ι ι K) = ψ (1 - (1 : K) • F) := rfl
  have hMv : (M : Matrix ι ι K) = ψ (φ M) := (hψφ _).symm
  have hHH : Hm ∈ H := hH1 _ (by
    rw [hHv, hdet]
    have h := det_unipGL hE2 (1 : K)
    rwa [coe_unipGL] at h)
  have hSH : Sm ∈ H := hH1 _ (by
    rw [hSv, hdet]
    have h := det_unipGL hF2 (1 : K)
    rwa [coe_unipGL] at h)
  have hHM : Hm * M = M * Hm := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hHv, hMv, ← map_mul, ← map_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hEM])
  have hSM : Sm * M = M * Sm := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hSv, hMv, ← map_mul, ← map_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hFM])
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
  have hX : ((Hm * Sm * Hm⁻¹ * Sm⁻¹ : GL ι K) : Matrix ι ι K) = ψ (1 + E * F) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hHv, hSv, hHv', hSv', ← map_mul, ← map_mul,
      ← map_mul]
    simp only [one_smul]
    rw [one_add_commutator_eq hE2 hF2 hFE]
  set X : GL ι K := Hm * Sm * Hm⁻¹ * Sm⁻¹ with hXdef
  have hEF2 : (E * F) * (E * F) = 0 := by
    rw [mul_assoc, ← mul_assoc F E F, hFE, zero_mul, mul_zero]
  have hEFM : (E * F) * φ M = φ M * (E * F) := by
    rw [mul_assoc, hFM, ← mul_assoc, hEM, mul_assoc]
  have hXM : (X : Matrix ι ι K) * M = M * X := by
    rw [hX, hMv, ← map_mul, ← map_mul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hEFM]
  have hM2' : (M : Matrix ι ι K) * M = 1 := by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hM2
    simpa [sq] using h1
  have hX2 : (X : Matrix ι ι K) * X = 1 := by
    have h1 : (1 + E * F) * (1 + E * F) = (1 : Matrix κ κ K) := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hEF2, add_zero, add_assoc, matrix_add_self, add_zero]
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

section Std

variable {K : Type} [Field K] {ℓ r : ℕ}

theorem single_one_mul_single_one {κ : Type} [Fintype κ] [DecidableEq κ] (a b c : κ) :
    Matrix.single a b (1 : K) * Matrix.single b c 1 = Matrix.single a c 1 := by
  rw [Matrix.single_mul_single_same, one_mul]

theorem single_one_mul_single_one_of_ne {κ : Type} [Fintype κ] [DecidableEq κ] {a b b' c : κ}
    (h : b ≠ b') : Matrix.single a b (1 : K) * Matrix.single b' c 1 = 0 :=
  Matrix.single_mul_single_of_ne (1 : K) a b b' h 1

@[expose] def sqZeroLevi (i j : Fin ℓ) :
    Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
  Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1

theorem sqZeroLevi_mul_sqZeroLevi (i m j : Fin ℓ) :
    sqZeroLevi (K := K) (r := r) i m * sqZeroLevi m j = sqZeroLevi i j := by
  simp only [sqZeroLevi, Matrix.add_mul, Matrix.mul_add, single_one_mul_single_one]
  rw [single_one_mul_single_one_of_ne (by simp), single_one_mul_single_one_of_ne (by simp),
    add_zero,
    zero_add]

theorem sqZeroLevi_mul_eq_zero {i m j : Fin ℓ} (hij : i ≠ j) :
    sqZeroLevi (K := K) (r := r) m j * sqZeroLevi i m = 0 := by
  simp only [sqZeroLevi, Matrix.add_mul, Matrix.mul_add]
  rw [single_one_mul_single_one_of_ne (by simpa using hij.symm),
    single_one_mul_single_one_of_ne (by simp), single_one_mul_single_one_of_ne (by simp),
    single_one_mul_single_one_of_ne (by simpa using hij.symm)]
  simp

theorem sqZeroLevi_mul_self {i j : Fin ℓ} (hij : i ≠ j) :
    sqZeroLevi (K := K) (r := r) i j * sqZeroLevi i j = 0 := by
  simp only [sqZeroLevi, Matrix.add_mul, Matrix.mul_add]
  rw [single_one_mul_single_one_of_ne (by simpa using hij.symm),
    single_one_mul_single_one_of_ne (by simp), single_one_mul_single_one_of_ne (by simp),
    single_one_mul_single_one_of_ne (by simpa using hij.symm)]
  simp

theorem sqZeroLevi_commute (i j : Fin ℓ) :
    sqZeroLevi (K := K) (r := r) i j * sqZeroStd ℓ r = sqZeroStd ℓ r * sqZeroLevi i j :=
  sqZeroStd_commute_F i j

theorem sqZeroLevi_mul_single (i j : Fin ℓ) (c : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    sqZeroLevi (K := K) i j * Matrix.single (.inr (.inl j)) c 1 =
      Matrix.single (.inr (.inl i)) c 1 := by
  rw [sqZeroLevi, Matrix.add_mul, single_one_mul_single_one,
    single_one_mul_single_one_of_ne (by simp), zero_add]

theorem single_mul_sqZeroLevi (a : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (i j : Fin ℓ) :
    Matrix.single a (.inl i) (1 : K) * sqZeroLevi i j = Matrix.single a (.inl j) 1 := by
  rw [sqZeroLevi, Matrix.mul_add, single_one_mul_single_one,
    single_one_mul_single_one_of_ne (by simp), add_zero]

theorem single_commute_sqZeroStd {a b : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)}
    (hb : ∀ m', sqZeroStd (K := K) ℓ r b m' = 0) (ha : ∀ m, sqZeroStd (K := K) ℓ r m a = 0) :
    Matrix.single a b (1 : K) * sqZeroStd ℓ r = sqZeroStd ℓ r * Matrix.single a b 1 := by
  rw [single_mul_sqZeroStd_eq_zero hb, sqZeroStd_mul_single_eq_zero ha]

end Std

section Linear

variable {G : Type} [Group G] {A : Subgroup G}

private theorem exists_ne_ne_fin {ℓ : ℕ} (hℓ : 3 ≤ ℓ) (i j : Fin ℓ) : ∃ m, m ≠ i ∧ m ≠ j := by
  classical
  have h : 0 < ((Finset.univ.erase i).erase j).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase i) (a := j)
    have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (Fin ℓ))) (a := i)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  obtain ⟨m, hm⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hm
  exact ⟨m, hm.2, hm.1⟩

theorem noPairOrbit_linear_two (D : ClassicalModel A) (hD : D.family = .linear)
    (hZ : Odd (Nat.card (center ↥A))) (hq : D.q = 2) {p : G} {ℓ0 : ℕ} (hp : D.HasRank p ℓ0)
    (hℓ2 : ℓ0 ≠ 2) : NoPairOrbit A p := by
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    have hm1 : m = 1 := Nat.pow_right_injective (le_refl 2) (show 2 ^ m = 2 ^ 1 from hq)
    subst hm1
    have hn5 : 5 ≤ n := by
      rcases Nat.lt_or_ge n 5 with h | h
      · exact absurd (by rw [show n = 4 by omega]) hnm
      · exact h
    obtain ⟨hpo, M, hpM, hM2, hrk⟩ := hp
    have hp2' : p ^ 2 = 1 := by rw [← hpo]; exact pow_orderOf_eq_one p
    have hp1 : p * p = 1 := by rw [← sq]; exact hp2'
    have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hM1 : M ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hM2
      omega
    have hSL : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K).det = 1 →
        X ∈ StatedSL n K := fun X hX => subset_closure hX
    set N := (M : Matrix (Fin n) (Fin n) K) - 1 with hNdef
    have hE : N * N = 0 := sub_one_mul_self hMsq
    have hN0 : N ≠ 0 := sub_one_ne_zero hM1
    have hMN : (M : Matrix (Fin n) (Fin n) K) = 1 + N := (add_sub_cancel 1 _).symm
    obtain ⟨l, r, φ, hlN, hl0, hcardι, hφN, hdet⟩ := exists_algEquiv_sqZeroStd_rank hE hN0
    have hl : l = ℓ0 := by rw [hlN, ← hrk]; rfl
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
    have key : ∀ E F : Matrix (Fin l ⊕ (Fin l ⊕ Fin r)) (Fin l ⊕ (Fin l ⊕ Fin r)) K,
        E * E = 0 → F * F = 0 → F * E = 0 → E * sqZeroStd l r = sqZeroStd l r * E →
        F * sqZeroStd l r = sqZeroStd l r * F → φ U * (E * F) = (E * F) * φ U :=
      fun E F hE2 hF2 hFE hES hFS =>
        commute_of_root_commutator hZ hSL φ hdet hpM hMsq hp2' hU hup hcomm hE2 hF2 hFE
          (by rw [hφM]; exact commute_one_add_sqZeroStd hES)
          (by rw [hφM]; exact commute_one_add_sqZeroStd hFS)
    have hl13 : l = 1 ∨ 3 ≤ l := by omega
    have hWX : ∀ i j : Fin l, Matrix.single (.inr (.inl i)) (.inl j) (1 : K) * sqZeroStd l r =
        sqZeroStd l r * Matrix.single (.inr (.inl i)) (.inl j) 1 := fun i j =>
      single_commute_sqZeroStd (sqZeroStd_inl j) fun m => sqZeroStd_col_inr m (.inl i)
    have hYX : ∀ (k : Fin r) (j : Fin l), Matrix.single (.inr (.inr k)) (.inl j) (1 : K) *
        sqZeroStd l r = sqZeroStd l r * Matrix.single (.inr (.inr k)) (.inl j) 1 := fun k j =>
      single_commute_sqZeroStd (sqZeroStd_inl j) fun m => sqZeroStd_col_inr m (.inr k)
    have hWY : ∀ (i : Fin l) (k : Fin r), Matrix.single (.inr (.inl i)) (.inr (.inr k)) (1 : K) *
        sqZeroStd l r = sqZeroStd l r * Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 :=
      fun i k => single_commute_sqZeroStd (sqZeroStd_inr_inr k) fun m =>
        sqZeroStd_col_inr m (.inl i)
    have hYY : ∀ k k' : Fin r, Matrix.single (.inr (.inr k)) (.inr (.inr k')) (1 : K) *
        sqZeroStd l r = sqZeroStd l r * Matrix.single (.inr (.inr k)) (.inr (.inr k')) 1 :=
      fun k k' => single_commute_sqZeroStd (sqZeroStd_inr_inr k') fun m =>
        sqZeroStd_col_inr m (.inr k)
    have hC1 : ∀ i j : Fin l, i ≠ j →
        φ U * Matrix.single (.inr (.inl i)) (.inl j) 1 =
          Matrix.single (.inr (.inl i)) (.inl j) 1 * φ U := by
      intro i j hij
      have h := key (sqZeroLevi i j) (Matrix.single (.inr (.inl j)) (.inl j) 1)
        (sqZeroLevi_mul_self hij)
        (single_one_mul_single_one_of_ne (by simp))
        (by rw [sqZeroLevi, Matrix.mul_add,
          single_one_mul_single_one_of_ne (by simpa using hij.symm),
          single_one_mul_single_one_of_ne (by simp), add_zero])
        (sqZeroLevi_commute i j) (hWX j j)
      rwa [sqZeroLevi_mul_single] at h
    have hC4 : ∀ i j : Fin l, i ≠ j →
        φ U * (Matrix.single (.inl i) (.inl j) 1 +
          Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) =
        (Matrix.single (.inl i) (.inl j) 1 +
          Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) * φ U := by
      intro i j hij
      rcases hl13 with h1 | h3
      · subst h1
        exact absurd (Subsingleton.elim i j) hij
      obtain ⟨m, hmi, hmj⟩ := exists_ne_ne_fin h3 i j
      have h := key (sqZeroLevi i m) (sqZeroLevi m j) (sqZeroLevi_mul_self hmi.symm)
        (sqZeroLevi_mul_self hmj)
        (sqZeroLevi_mul_eq_zero hij) (sqZeroLevi_commute i m) (sqZeroLevi_commute m j)
      rwa [sqZeroLevi_mul_sqZeroLevi] at h
    have hC2 : ∀ (k : Fin r) (j : Fin l),
        φ U * Matrix.single (.inr (.inr k)) (.inl j) 1 =
          Matrix.single (.inr (.inr k)) (.inl j) 1 * φ U := by
      intro k j
      rcases hl13 with h1 | h3
      · have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
        obtain ⟨k', hk'⟩ := exists_ne k
        have h := key (Matrix.single (.inr (.inr k)) (.inr (.inr k')) 1)
          (Matrix.single (.inr (.inr k')) (.inl j) 1)
          (single_one_mul_single_one_of_ne (by simpa using hk'))
          (single_one_mul_single_one_of_ne (by simp)) (single_one_mul_single_one_of_ne (by simp))
          (hYY k k') (hYX k' j)
        rwa [single_one_mul_single_one] at h
      · obtain ⟨m, hmj, -⟩ := exists_ne_ne_fin h3 j j
        have h := key (Matrix.single (.inr (.inr k)) (.inl m) 1) (sqZeroLevi m j)
          (single_one_mul_single_one_of_ne (by simp)) (sqZeroLevi_mul_self hmj)
          (by rw [sqZeroLevi, Matrix.add_mul, single_one_mul_single_one_of_ne (by simp),
            single_one_mul_single_one_of_ne (by simp), add_zero])
          (hYX k m) (sqZeroLevi_commute m j)
        rwa [single_mul_sqZeroLevi] at h
    have hC3 : ∀ (i : Fin l) (k : Fin r),
        φ U * Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 =
          Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 * φ U := by
      intro i k
      rcases hl13 with h1 | h3
      · have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
        obtain ⟨k', hk'⟩ := exists_ne k
        have h := key (Matrix.single (.inr (.inl i)) (.inr (.inr k')) 1)
          (Matrix.single (.inr (.inr k')) (.inr (.inr k)) 1)
          (single_one_mul_single_one_of_ne (by simp))
          (single_one_mul_single_one_of_ne (by simpa using hk'.symm))
          (single_one_mul_single_one_of_ne (by simp)) (hWY i k') (hYY k' k)
        rwa [single_one_mul_single_one] at h
      · obtain ⟨m, hmi, -⟩ := exists_ne_ne_fin h3 i i
        have h := key (sqZeroLevi i m) (Matrix.single (.inr (.inl m)) (.inr (.inr k)) 1)
          (sqZeroLevi_mul_self hmi.symm) (single_one_mul_single_one_of_ne (by simp))
          (by rw [sqZeroLevi, Matrix.mul_add, single_one_mul_single_one_of_ne (by simp),
            single_one_mul_single_one_of_ne (by simp), add_zero])
          (sqZeroLevi_commute i m) (hWY m k)
        rwa [sqZeroLevi_mul_single] at h
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

theorem linearCaseIITwo : LinearCaseIITwo := by
  intro G _ _ A D hD _ hZ hq t u h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : orderOf t = 2 := orderOf_eq_prime h.t_sq h.t_ne_one
  obtain ⟨ℓ, hℓ⟩ := D.exists_hasRank hZ h.mem_t ht2
  by_cases h2 : ℓ = 2
  · exact h2 ▸ hℓ
  · exact absurd (noPairOrbit_linear_two D hD hZ hq hℓ h2) h.not_noPairOrbit

end Linear

end CFSG.ComponentClassification.RankTwoClassical
