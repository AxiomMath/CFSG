module

public import CFSG.LieType.SeitzGeneration.HeisTorusU81
public import CFSG.LieType.SeitzGeneration.HeisTorusU83
public import CFSG.LieType.SeitzGeneration.HeisTorusU84

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

section Blk

variable {m : ℕ}

@[expose] def ug85_blk (ε : K) (A : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  Matrix.of (vecCons (vecCons ε fun _ => 0) fun i => vecCons 0 (A i))

@[simp] theorem ug85_blk_zero_zero (ε : K) (A : Matrix (Fin m) (Fin m) K) :
    ug85_blk ε A 0 0 = ε := rfl

@[simp] theorem ug85_blk_zero_succ (ε : K) (A : Matrix (Fin m) (Fin m) K) (j : Fin m) :
    ug85_blk ε A 0 j.succ = 0 := rfl

@[simp] theorem ug85_blk_succ_zero (ε : K) (A : Matrix (Fin m) (Fin m) K) (i : Fin m) :
    ug85_blk ε A i.succ 0 = 0 := rfl

@[simp] theorem ug85_blk_succ_succ (ε : K) (A : Matrix (Fin m) (Fin m) K) (i j : Fin m) :
    ug85_blk ε A i.succ j.succ = A i j := rfl

theorem ug85_ext {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (h00 : M 0 0 = N 0 0)
    (h01 : ∀ j : Fin m, M 0 j.succ = N 0 j.succ) (h10 : ∀ i : Fin m, M i.succ 0 = N i.succ 0)
    (h11 : ∀ i j : Fin m, M i.succ j.succ = N i.succ j.succ) : M = N := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> simp [*]

theorem ug85_eq_blk {M : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (h01 : ∀ j : Fin m, M 0 j.succ = 0)
    (h10 : ∀ i : Fin m, M i.succ 0 = 0) :
    M = ug85_blk (M 0 0) (M.submatrix Fin.succ Fin.succ) :=
  ug85_ext rfl (fun j => by simp [h01]) (fun i => by simp [h10]) (fun i j => by simp)

theorem ug85_blk_inj {ε ε' : K} {A A' : Matrix (Fin m) (Fin m) K}
    (hEq : ug85_blk ε A = ug85_blk ε' A') : ε = ε' ∧ A = A' :=
  ⟨by simpa using congrFun (congrFun hEq 0) 0,
    Matrix.ext fun i j => by simpa using congrFun (congrFun hEq i.succ) j.succ⟩

theorem ug85_blk_one : ug85_blk (1 : K) (1 : Matrix (Fin m) (Fin m) K) = 1 := by
  refine ug85_ext ?_ ?_ ?_ ?_ <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem ug85_blk_mul (ε ε' : K) (A A' : Matrix (Fin m) (Fin m) K) :
    ug85_blk ε A * ug85_blk ε' A' = ug85_blk (ε * ε') (A * A') := by
  refine ug85_ext ?_ ?_ ?_ ?_ <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem ug85_blk_map (g : K →+* K) (ε : K) (A : Matrix (Fin m) (Fin m) K) :
    (ug85_blk ε A).map g = ug85_blk (g ε) (A.map g) := by
  refine ug85_ext ?_ ?_ ?_ ?_ <;> simp

theorem ug85_blk_transpose (ε : K) (A : Matrix (Fin m) (Fin m) K) :
    (ug85_blk ε A)ᵀ = ug85_blk ε Aᵀ := by
  refine ug85_ext ?_ ?_ ?_ ?_ <;> simp

theorem ug85_blk_diagonal (ε : K) (t : Fin m → K) :
    ug85_blk ε (diagonal t) = diagonal (vecCons ε t) := by
  refine ug85_ext ?_ ?_ ?_ ?_ <;>
    simp [Matrix.diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem ug85_blk_submatrix (ε : K) (A : Matrix (Fin m) (Fin m) K) :
    (ug85_blk ε A).submatrix Fin.succ Fin.succ = A := rfl

theorem ug85_blk_det (ε : K) (A : Matrix (Fin m) (Fin m) K) :
    (ug85_blk ε A).det = ε * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove_zero, ug85_blk_submatrix]

theorem ug85_adj_blk (h : UnitaryFieldData ℓ f K) (ε : K) (A : Matrix (Fin m) (Fin m) K) :
    ug83_adj h (ug85_blk ε A) = ug85_blk (h.bar ε) (ug83_adj h A) := by
  simp only [ug83_adj, ug85_blk_map, ug85_blk_transpose]

theorem ug85_row_zero (h : UnitaryFieldData ℓ f K) {M : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (hM : ug83_adj h M * M = 1) (h10 : ∀ i : Fin m, M i.succ 0 = 0) (j : Fin m) :
    M 0 j.succ = 0 := by
  have h00 : h.bar (M 0 0) * M 0 0 = 1 := by
    have := congrFun (congrFun hM 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, ug83_adj_apply, h10] using this
  have hj := congrFun (congrFun hM j.succ) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ, ug83_adj_apply, h10, Matrix.one_apply,
    Fin.succ_ne_zero] at hj
  rcases hj with hj | hj
  · exact hj
  · rw [hj, mul_zero] at h00
    exact absurd h00 zero_ne_one

theorem ug85_blk_monomial {ε : K} {A : Matrix (Fin m) (Fin m) K} (hA : IsMonomialMat A) :
    IsMonomialMat (ug85_blk ε A) := by
  intro j
  induction j using Fin.cases with
  | zero =>
    intro i i' hi hi'
    have h0 : ∀ i : Fin (m + 1), ug85_blk ε A i 0 ≠ 0 → i = 0 := by
      intro i hi
      induction i using Fin.cases with
      | zero => rfl
      | succ i => exact absurd (ug85_blk_succ_zero ε A i) hi
    rw [h0 i hi, h0 i' hi']
  | succ j =>
    intro i i' hi hi'
    have h1 : ∀ i : Fin (m + 1), ug85_blk ε A i j.succ ≠ 0 → ∃ i₁ : Fin m, i = i₁.succ ∧
        A i₁ j ≠ 0 := by
      intro i hi
      induction i using Fin.cases with
      | zero => exact absurd (ug85_blk_zero_succ ε A j) hi
      | succ i => exact ⟨i, rfl, hi⟩
    obtain ⟨i₁, rfl, hi₁⟩ := h1 i hi
    obtain ⟨i₂, rfl, hi₂⟩ := h1 i' hi'
    rw [hA j i₁ i₂ hi₁ hi₂]

theorem ug85_block_succ {a b : Fin m} {y : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (hy : IsCoordBlockOn a.succ b.succ y) :
    y 0 0 = 1 ∧ (∀ j : Fin m, y 0 j.succ = 0) ∧ (∀ i : Fin m, y i.succ 0 = 0) ∧
      IsCoordBlockOn a b (y.submatrix Fin.succ Fin.succ) := by
  have hz : (0 : Fin (m + 1)) ≠ a.succ ∧ (0 : Fin (m + 1)) ≠ b.succ :=
    ⟨(Fin.succ_ne_zero a).symm, (Fin.succ_ne_zero b).symm⟩
  refine ⟨by simpa using hy 0 0 (Or.inl hz), fun j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · simpa [(Fin.succ_ne_zero j).symm] using hy 0 j.succ (Or.inl hz)
  · simpa [Fin.succ_ne_zero i] using hy i.succ 0 (Or.inr hz)
  · have := hy i.succ j.succ (by simpa [Fin.succ_inj] using hij)
    simpa [Fin.succ_inj] using this

end Blk

section Emb

variable {m : ℕ}

@[expose] noncomputable def ug85_embMat (m : ℕ) :
    Matrix (Fin m) (Fin m) K →* Matrix (Fin (m + 1)) (Fin (m + 1)) K where
  toFun A := ug85_blk A.det⁻¹ A
  map_one' := by simpa using ug85_blk_one
  map_mul' A B := by rw [ug85_blk_mul, Matrix.det_mul, mul_inv]

@[expose] noncomputable def ug85_emb (m : ℕ) : GL (Fin m) K →* GL (Fin (m + 1)) K :=
  Units.map (ug85_embMat m)

theorem ug85_emb_val (A : GL (Fin m) K) :
    ((ug85_emb m A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      ug85_blk ((A : Matrix (Fin m) (Fin m) K).det)⁻¹ (A : Matrix (Fin m) (Fin m) K) := rfl

theorem ug85_bar_det_mul (h : UnitaryFieldData ℓ f K) {A : Matrix (Fin m) (Fin m) K}
    (hA : ug83_adj h A * A = 1) : h.bar A.det * A.det = 1 := by
  have h1 := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_one] at h1
  have h2 : (ug83_adj h A).det = h.bar A.det := by
    rw [ug83_adj, Matrix.det_transpose]
    exact (RingHom.map_det h.bar A).symm
  rwa [h2] at h1

theorem ug85_emb_mem_su (h : UnitaryFieldData ℓ f K) {A : GL (Fin m) K}
    (hA : A ∈ primeFormUnitary h 1) : ug85_emb m A ∈ unitarySU ℓ f K (m + 1) := by
  have hA' : ug83_adj h (A : Matrix (Fin m) (Fin m) K) * (A : Matrix (Fin m) (Fin m) K) = 1 := by
    have := hA
    rw [mem_primeFormUnitary, Matrix.mul_one] at this
    exact this
  have hdet0 : (A : Matrix (Fin m) (Fin m) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
  have hnorm : h.bar ((A : Matrix (Fin m) (Fin m) K).det)⁻¹ *
      ((A : Matrix (Fin m) (Fin m) K).det)⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, ug85_bar_det_mul h hA', inv_one]
  rw [mem_unitarySU_iff h, ug85_emb_val, ug85_blk_det, inv_mul_cancel₀ hdet0]
  refine ⟨rfl, ?_⟩
  change ug83_adj h (ug85_blk _ _) * ug85_blk _ _ = 1
  rw [ug85_adj_blk, ug85_blk_mul, hnorm, hA', ug85_blk_one]

theorem ug85_adj_of_emb_mem_su (h : UnitaryFieldData ℓ f K) {A : GL (Fin m) K}
    (hA : ug85_emb m A ∈ unitarySU ℓ f K (m + 1)) :
    ug83_adj h (A : Matrix (Fin m) (Fin m) K) * (A : Matrix (Fin m) (Fin m) K) = 1 := by
  have h1 := ((mem_unitarySU_iff h).1 hA).2
  rw [ug85_emb_val] at h1
  change ug83_adj h (ug85_blk _ _) * ug85_blk _ _ = 1 at h1
  rw [ug85_adj_blk, ug85_blk_mul, ← ug85_blk_one] at h1
  exact (ug85_blk_inj h1).2

theorem ug85_exists_emb {g : GL (Fin (m + 1)) K}
    (h01 : ∀ j : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 j.succ = 0)
    (h10 : ∀ i : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.succ 0 = 0)
    (hdet : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = 1) :
    ∃ A : GL (Fin m) K, ug85_emb m A = g ∧ (A : Matrix (Fin m) (Fin m) K) =
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.succ Fin.succ := by
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) K := (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
  have hM := ug85_eq_blk h01 h10
  have hd : M 0 0 * (M.submatrix Fin.succ Fin.succ).det = 1 := by
    rw [← ug85_blk_det, ← hM]
    exact hdet
  have hne : (M.submatrix Fin.succ Fin.succ).det ≠ 0 := right_ne_zero_of_mul_eq_one hd
  have hinv : (M.submatrix Fin.succ Fin.succ).det⁻¹ = M 0 0 :=
    (eq_inv_of_mul_eq_one_left hd).symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne, Units.ext ?_, rfl⟩
  rw [ug85_emb_val]
  change ug85_blk ((M.submatrix Fin.succ Fin.succ).det)⁻¹ _ = M
  rw [hinv]
  exact hM.symm

end Emb

section Core

theorem ug85_core (h : UnitaryFieldData ℓ f K) (hq : 4 ≤ ℓ ^ f)
    (he : 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1)) {m : ℕ} (hm : 2 ≤ m)
    (H : Subgroup (GL (Fin (m + 1)) K)) (hHU : H ≤ unitarySU ℓ f K (m + 1))
    (hT : ∀ g ∈ unitarySU ℓ f K (m + 1),
      (∃ t, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = diagonal t) → g ∈ H)
    (hfix : ∃ g ∈ H, (∀ i : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.succ 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) :
    ∃ a b : Fin m, a ≠ b ∧ ∀ y ∈ unitarySU ℓ f K (m + 1),
      IsCoordBlockOn a.succ b.succ (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) → y ∈ H := by
  classical
  set X : Subgroup (GL (Fin m) K) := H.comap (ug85_emb m) with hX
  have hXU : X ≤ primeFormUnitary h 1 := by
    intro A hA
    have hA' := ug85_adj_of_emb_mem_su h (hHU hA)
    rw [mem_primeFormUnitary, Matrix.mul_one]
    exact hA'
  have hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin m) (Fin m) K),
      (∃ t, (g : Matrix (Fin m) (Fin m) K) = diagonal t) → g ∈ X := by
    rintro g hg ⟨t, ht⟩
    refine hT _ (ug85_emb_mem_su h hg) ⟨vecCons ((g : Matrix (Fin m) (Fin m) K).det)⁻¹ t, ?_⟩
    rw [ug85_emb_val, ht, ug85_blk_diagonal]
  have hx : ∃ x ∈ X, ¬ IsMonomialMat (x : Matrix (Fin m) (Fin m) K) := by
    obtain ⟨g, hgH, hg10, hgm⟩ := hfix
    have hgU := (mem_unitarySU_iff h).1 (hHU hgH)
    have hg01 := ug85_row_zero h hgU.2 hg10
    obtain ⟨A, hAg, hAsub⟩ := ug85_exists_emb hg01 hg10 hgU.1
    refine ⟨A, by rw [hX, Subgroup.mem_comap, hAg]; exact hgH, fun hAm => hgm ?_⟩
    rw [ug85_eq_blk hg01 hg10, ← hAsub]
    exact ug85_blk_monomial hAm
  obtain ⟨a, b, hab, hblk⟩ := exists_block_su_of_diag h hq he hm X hXU hD hx
  refine ⟨a, b, hab, fun y hy hyb => ?_⟩
  obtain ⟨h00, h01, h10, hsub⟩ := ug85_block_succ hyb
  have hyU := (mem_unitarySU_iff h).1 hy
  obtain ⟨A, hAy, hAsub⟩ := ug85_exists_emb h01 h10 hyU.1
  have hyblk : (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      ug85_blk 1 (A : Matrix (Fin m) (Fin m) K) := by
    rw [hAsub, ← h00]
    exact ug85_eq_blk h01 h10
  have hAS : A ∈ unitarySU ℓ f K m := by
    rw [mem_unitarySU_iff h]
    have hd := hyU.1
    have hu : ug83_adj h (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := hyU.2
    rw [hyblk, ug85_blk_det, one_mul] at hd
    rw [hyblk, ug85_adj_blk, ug85_blk_mul, ← ug85_blk_one] at hu
    exact ⟨hd, (ug85_blk_inj hu).2⟩
  have hAX := hblk A hAS (by rw [hAsub]; exact hsub)
  rw [hX, Subgroup.mem_comap, hAy] at hAX
  exact hAX

end Core

section Perm

variable {r : ℕ}

theorem ug85_good_perm [NeZero r] (S H : Subgroup (GL (Fin r) K)) (hHS : H ≤ S)
    (σ : Equiv.Perm (Fin r))
    (hσ : ∃ c : K, ∃ g ∈ H, (g : Matrix (Fin r) (Fin r) K) = c • Equiv.Perm.permMatrix K σ)
    {a b : Fin r}
    (hab : ∀ y ∈ S, IsCoordBlockOn a b (y : Matrix (Fin r) (Fin r) K) → y ∈ H) :
    ∀ y ∈ S, IsCoordBlockOn (σ a) (σ b) (y : Matrix (Fin r) (Fin r) K) → y ∈ H := by
  obtain ⟨c, g, hgH, hg⟩ := hσ
  intro y' hy' hblk
  have h1 : (g : Matrix (Fin r) (Fin r) K) *
      ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc : c ≠ 0 := by
    rintro rfl
    rw [hg, zero_smul, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hginv : ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      c⁻¹ • Equiv.Perm.permMatrix K σ⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_left ?_
    rw [hg, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
      ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  have hyentry : ∀ i j, ((g * y' * g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j =
      (y' : Matrix (Fin r) (Fin r) K) (σ i) (σ j) := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hginv, hg, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, mul_inv_cancel₀ hc, one_smul, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp [Equiv.Perm.inv_def]
  have hyblk : IsCoordBlockOn a b ((g * y' * g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) := by
    intro i j hij
    rw [hyentry]
    have hij' : (σ i ≠ σ a ∧ σ i ≠ σ b) ∨ (σ j ≠ σ a ∧ σ j ≠ σ b) := by
      rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨fun e => h1 (σ.injective e), fun e => h2 (σ.injective e)⟩
      · exact Or.inr ⟨fun e => h1 (σ.injective e), fun e => h2 (σ.injective e)⟩
    rw [hblk (σ i) (σ j) hij']
    simp [σ.injective.eq_iff]
  have hyH := hab _ (mul_mem (mul_mem (hHS hgH) hy') (inv_mem (hHS hgH))) hyblk
  have : y' = g⁻¹ * (g * y' * g⁻¹) * g := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hgH) hyH) hgH

theorem ug85_rot_cast [NeZero r] (i : Fin r) :
    (((finRotate r i : Fin r) : ℕ) : ZMod r) = ((i : ℕ) : ZMod r) + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos r)).symm⟩
  rw [coe_finRotate]
  split_ifs with hi
  · subst hi
    simp only [Fin.val_last, Nat.cast_zero]
    rw [← Nat.cast_add_one, ZMod.natCast_self]
  · push_cast
    rfl

theorem ug85_rot_pow_cast [NeZero r] (l : ℕ) (i : Fin r) :
    ((((finRotate r ^ l) i : Fin r) : ℕ) : ZMod r) = ((i : ℕ) : ZMod r) + l := by
  induction l with
  | zero => simp
  | succ l ih => rw [pow_succ', Equiv.Perm.mul_apply, ug85_rot_cast, ih, Nat.cast_succ, add_assoc]

theorem ug85_exists_affine [Fact r.Prime] {a b a' b' : Fin r} (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ (k l : ℕ) (hk : ¬ r ∣ k), (finRotate r ^ l) (mulPerm r k hk a) = a' ∧
      (finRotate r ^ l) (mulPerm r k hk b) = b' := by
  set φ : Fin r → ZMod r := fun i => ((i : ℕ) : ZMod r)
  have hinj : ∀ {i j : Fin r}, φ i = φ j ↔ i = j := ug81_natCast_inj
  have hba : φ b - φ a ≠ 0 := sub_ne_zero.2 (fun e => hab (hinj.1 e.symm))
  have hba' : φ b' - φ a' ≠ 0 := sub_ne_zero.2 (fun e => hab' (hinj.1 e.symm))
  set k₀ : ZMod r := (φ b' - φ a') / (φ b - φ a)
  have hk₀ne : k₀ ≠ 0 := div_ne_zero hba' hba
  have hk : ¬ r ∣ k₀.val := by
    intro hd
    apply hk₀ne
    rw [← ZMod.natCast_zmod_val k₀]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hd
  have hmul : ∀ i : Fin r, φ (mulPerm r k₀.val hk i) = k₀ * φ i := by
    intro i
    have := (mulPerm_apply_eq_iff k₀.val hk i _).1 rfl
    rwa [ZMod.natCast_zmod_val] at this
  have hk₀mul : k₀ * (φ b - φ a) = φ b' - φ a' := div_mul_cancel₀ _ hba
  refine ⟨k₀.val, (φ a' - k₀ * φ a).val, hk, hinj.1 ?_, hinj.1 ?_⟩
  · show ((((finRotate r ^ (φ a' - k₀ * φ a).val) (mulPerm r k₀.val hk a) : Fin r) : ℕ) :
      ZMod r) = φ a'
    rw [ug85_rot_pow_cast, ZMod.natCast_zmod_val]
    change φ (mulPerm r k₀.val hk a) + _ = _
    rw [hmul]
    ring
  · show ((((finRotate r ^ (φ a' - k₀ * φ a).val) (mulPerm r k₀.val hk b) : Fin r) : ℕ) :
      ZMod r) = φ b'
    rw [ug85_rot_pow_cast, ZMod.natCast_zmod_val]
    change φ (mulPerm r k₀.val hk b) + _ = _
    rw [hmul]
    linear_combination hk₀mul

end Perm

theorem ug85_bounds {r q : ℕ} [Fact r.Prime] (hr : 5 ≤ r) (hrq : r ∣ q + 1) :
    4 ≤ q ∧ 5 ≤ (q + 1) / Nat.gcd 2 (q + 1) := by
  have hq1 : r ≤ q + 1 := Nat.le_of_dvd (Nat.succ_pos q) hrq
  refine ⟨by omega, ?_⟩
  by_cases h2 : 2 ∣ q + 1
  · have hcop : Nat.Coprime 2 r :=
      (Nat.coprime_primes Nat.prime_two (Fact.out : r.Prime)).2 (by omega)
    have h2r : 2 * r ∣ q + 1 := hcop.mul_dvd_of_dvd_of_dvd h2 hrq
    have := Nat.le_of_dvd (Nat.succ_pos q) h2r
    rw [Nat.gcd_eq_left h2]
    omega
  · have hg : Nat.gcd 2 (q + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2
    rw [hg, Nat.div_one]
    omega

theorem eq_unitarySU_of_fixer (h : UnitaryFieldData ℓ f K) {r : ℕ}
    [Fact r.Prime] (hr : 5 ≤ r) (hrq : r ∣ ℓ ^ f + 1) {ζ : K} (hζ : IsPrimitiveRoot ζ r)
    (H : Subgroup (GL (Fin r) K)) (hHU : H ≤ unitarySU ℓ f K r)
    (hT : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) = diagonal t) → g ∈ H)
    (hTw : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal t) → g ∈ H)
    (hfix : ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin r) (Fin r) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin r) (Fin r) K)) :
    H = unitarySU ℓ f K r := by
  obtain ⟨hq, he⟩ := ug85_bounds hr hrq
  refine le_antisymm hHU ?_
  have hplane : ∃ a b : Fin r, a ≠ b ∧ ∀ y ∈ unitarySU ℓ f K r,
      IsCoordBlockOn a b (y : Matrix (Fin r) (Fin r) K) → y ∈ H := by
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    obtain ⟨g, hgH, hg0, hgm⟩ := hfix
    obtain ⟨a, b, hab, hblk⟩ := ug85_core h hq he (by omega) H hHU hT
      ⟨g, hgH, fun i => hg0 i.succ (Fin.succ_ne_zero i), hgm⟩
    exact ⟨a.succ, b.succ, fun e => hab (Fin.succ_injective _ e), hblk⟩
  obtain ⟨a, b, hab, hgood⟩ := hplane
  have hshift : ∃ c : K, ∃ g ∈ H, (g : Matrix (Fin r) (Fin r) K) =
      c • Equiv.Perm.permMatrix K (finRotate r) := by
    obtain ⟨g, hg, hgS⟩ := ug81_shift_mem h hr hζ H hTw
    exact ⟨1, g, hg, by rw [hgS, one_smul]; rfl⟩
  have hshiftpow : ∀ (l : ℕ) (a₀ b₀ : Fin r),
      (∀ y ∈ unitarySU ℓ f K r, IsCoordBlockOn a₀ b₀ (y : Matrix (Fin r) (Fin r) K) → y ∈ H) →
      ∀ y ∈ unitarySU ℓ f K r, IsCoordBlockOn ((finRotate r ^ l) a₀) ((finRotate r ^ l) b₀)
        (y : Matrix (Fin r) (Fin r) K) → y ∈ H := by
    intro l
    induction l with
    | zero => intro a₀ b₀ hab₀; simpa using hab₀
    | succ l ih =>
      intro a₀ b₀ hab₀
      simpa only [pow_succ', Equiv.Perm.mul_apply] using
        ug85_good_perm (unitarySU ℓ f K r) H hHU (finRotate r) hshift (ih a₀ b₀ hab₀)
  refine unitarySU_le_of_blocks h hq (by omega) H ?_
  intro a' b' hne y hy hyb
  obtain ⟨k, l, hk, h1, h2⟩ := ug85_exists_affine hab hne
  have hmult := ug85_good_perm (unitarySU ℓ f K r) H hHU (mulPerm r k hk)
    (ug81_mult_mem h hr hrq hζ H hT hTw k hk) hgood
  have hfin := hshiftpow l _ _ hmult
  rw [h1, h2] at hfin
  exact hfin y hy hyb

end CFSG.LieType.SeitzGeneration
