module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

abbrev hypSU (h : UnitaryFieldData p f K) (r ε : ℕ) : Subgroup (GL (HypIndex r ε) K) :=
  gramSU h (hypGram r ε K)

theorem mem_hypSU {h : UnitaryFieldData p f K} {g : GL (HypIndex r ε) K} :
    g ∈ hypSU h r ε ↔ ((g : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      g = hypGram r ε K ∧ (g : Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1 :=
  Iff.rfl

theorem hypForm_smul_smul (h : UnitaryFieldData p f K) (g : hypSU h r ε)
    (x y : HypIndex r ε → K) : hypForm h r ε (g • x) (g • y) = hypForm h r ε x y :=
  (mem_gramSU_iff_isometry.mp g.2).1 x y

abbrev hypScalars (h : UnitaryFieldData p f K) (r ε : ℕ) : Subgroup (hypSU h r ε) :=
  normOneScalars h (hypSU h r ε) (2 * r + ε)

abbrev hypPSU (h : UnitaryFieldData p f K) (r ε : ℕ) : Type :=
  hypSU h r ε ⧸ hypScalars h r ε

@[expose] def hypProj (h : UnitaryFieldData p f K) (r ε : ℕ) : hypSU h r ε →* hypPSU h r ε :=
  QuotientGroup.mk' _

theorem hypProj_surjective (h : UnitaryFieldData p f K) (r ε : ℕ) :
    Function.Surjective (hypProj h r ε) :=
  QuotientGroup.mk'_surjective _

theorem ker_hypProj (h : UnitaryFieldData p f K) (r ε : ℕ) :
    (hypProj h r ε).ker = hypScalars h r ε :=
  QuotientGroup.ker_mk' _

@[expose] noncomputable def hypProjAction (h : UnitaryFieldData p f K) (r ε : ℕ) :
    hypPSU h r ε →* Equiv.Perm (Submodule K (HypIndex r ε → K)) :=
  QuotientGroup.lift (hypScalars h r ε) (MulAction.toPermHom _ _) fun _ hg =>
    Equiv.ext fun L => smul_submodule_of_mem_normOneScalars hg L

noncomputable instance (h : UnitaryFieldData p f K) (r ε : ℕ) :
    MulAction (hypPSU h r ε) (Submodule K (HypIndex r ε → K)) :=
  MulAction.compHom _ (hypProjAction h r ε)

theorem hypProj_smul (h : UnitaryFieldData p f K) (g : hypSU h r ε)
    (L : Submodule K (HypIndex r ε → K)) : hypProj h r ε g • L = g • L :=
  rfl

@[expose] def fullPos : HypIndex r ε → ℕ
  | .inl i => i
  | .inr (.inl k) => r + k
  | .inr (.inr i) => 2 * r + ε - 1 - i

@[simp] theorem fullPos_inl (i : Fin r) : fullPos (.inl i : HypIndex r ε) = i := rfl

@[simp] theorem fullPos_inr_inl (k : Fin ε) : fullPos (.inr (.inl k) : HypIndex r ε) = r + k :=
  rfl

@[simp] theorem fullPos_inr_inr (i : Fin r) :
    fullPos (.inr (.inr i) : HypIndex r ε) = 2 * r + ε - 1 - i :=
  rfl

theorem fullPos_lt (a : HypIndex r ε) : fullPos a < 2 * r + ε := by
  rcases a with ⟨i, hi⟩ | ⟨k, hk⟩ | ⟨i, hi⟩ <;> simp <;> omega

theorem fullPos_injective : Function.Injective (fullPos (r := r) (ε := ε)) := by
  intro a b hab
  rcases a with ⟨i, hi⟩ | ⟨k, hk⟩ | ⟨i, hi⟩ <;> rcases b with ⟨j, hj⟩ | ⟨l, hl⟩ | ⟨j, hj⟩ <;>
    simp only [fullPos_inl, fullPos_inr_inl, fullPos_inr_inr] at hab <;>
    first
    | (congr 1; ext; simp only; omega)
    | (congr 2; ext; simp only; omega)
    | omega

theorem fullPos_hypPartner (hε : ε ≤ 1) (a : HypIndex r ε) :
    fullPos (hypPartner a) = 2 * r + ε - 1 - fullPos a := by
  rcases a with ⟨i, hi⟩ | ⟨k, hk⟩ | ⟨i, hi⟩ <;> simp <;> omega

@[expose] def posFlag (r ε : ℕ) (K : Type) [Field K] (i : ℕ) :
    Submodule K (HypIndex r ε → K) where
  carrier := {v | ∀ a, i ≤ fullPos a → v a = 0}
  add_mem' hv hw a ha := by simp [hv a ha, hw a ha]
  zero_mem' _ _ := rfl
  smul_mem' c v hv a ha := by simp [hv a ha]

theorem mem_posFlag {i : ℕ} {v : HypIndex r ε → K} :
    v ∈ posFlag r ε K i ↔ ∀ a, i ≤ fullPos a → v a = 0 :=
  Iff.rfl

theorem blockTriangular_fullPos_iff {M : Matrix (HypIndex r ε) (HypIndex r ε) K} :
    M.BlockTriangular fullPos ↔ ∀ i, ∀ v ∈ posFlag r ε K i, M *ᵥ v ∈ posFlag r ε K i := by
  constructor
  · intro hM i v hv a ha
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : i ≤ fullPos c
    · rw [hv c hc, mul_zero]
    · rw [hM (lt_of_lt_of_le (not_le.mp hc) ha), zero_mul]
  · intro hM a c hca
    have hv : (Pi.single c 1 : HypIndex r ε → K) ∈ posFlag r ε K (fullPos c + 1) := by
      intro b hb
      have : b ≠ c := by
        rintro rfl
        omega
      simp [this]
    have := hM _ _ hv a (by omega)
    rwa [mulVec_single_one, col_apply] at this

@[expose] def isoFlag (r ε : ℕ) (K : Type) [Field K] (i : ℕ) : Submodule K (HypIndex r ε → K) :=
  Submodule.span K
    ((fun j : Fin r => (Pi.single (Sum.inl j) (1 : K) : HypIndex r ε → K)) '' {j | (j : ℕ) < i})

@[expose] noncomputable def hypFlag (h : UnitaryFieldData p f K) (r ε : ℕ) (i : ℕ) :
    Submodule K (HypIndex r ε → K) :=
  if i ≤ r then isoFlag r ε K i
  else (isoFlag r ε K (2 * r + ε - i)).orthogonalBilin (hypForm h r ε)

theorem isoFlag_eq_posFlag {i : ℕ} (hi : i ≤ r) : isoFlag r ε K i = posFlag r ε K i := by
  apply le_antisymm
  · rw [isoFlag, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩ a ha
    have : a ≠ .inl j := by
      rintro rfl
      simp only [Set.mem_ofPred_eq] at hj
      simp only [fullPos_inl] at ha
      omega
    simp [this]
  · intro v hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : i ≤ fullPos a
    · rw [hv a ha, Pi.single_zero]
      exact Submodule.zero_mem _
    · rcases a with j | k | j
      · have : (Pi.single (Sum.inl j) (v (Sum.inl j)) : HypIndex r ε → K) =
            v (Sum.inl j) • Pi.single (Sum.inl j) 1 := by
          rw [← Pi.single_smul, smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, by simpa using ha, rfl⟩)
      · simp at ha
        omega
      · simp at ha
        omega

theorem hypForm_single_inl (h : UnitaryFieldData p f K) (j : Fin r) (v : HypIndex r ε → K) :
    hypForm h r ε (Pi.single (.inl j) 1) v = v (.inr (.inr j)) := by
  rw [hypForm_apply, Finset.sum_eq_single (.inl j)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem orthogonal_isoFlag (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {i : ℕ} (hi : i ≤ r) :
    (isoFlag r ε K i).orthogonalBilin (hypForm h r ε) = posFlag r ε K (2 * r + ε - i) := by
  ext v
  rw [Submodule.mem_orthogonalBilin, mem_posFlag]
  constructor
  · intro hv a ha
    rcases a with j | k | j
    · simp at ha
      omega
    · simp at ha
      omega
    · simp only [fullPos_inr_inr] at ha
      rw [← hypForm_single_inl h j v]
      exact hv _ (Submodule.subset_span ⟨j, by simp; omega, rfl⟩)
  · intro hv u hu
    rw [isoFlag_eq_posFlag hi] at hu
    change hypForm h r ε u v = 0
    rw [hypForm_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : i ≤ fullPos a
    · rw [hu a ha, map_zero, zero_mul]
    · rw [hv _ (by rw [fullPos_hypPartner hε]; omega), mul_zero]

theorem hypFlag_eq_posFlag (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {i : ℕ}
    (hi : i ≤ 2 * r + ε) : hypFlag h r ε i = posFlag r ε K i := by
  rw [hypFlag]
  split_ifs with hir
  · exact isoFlag_eq_posFlag hir
  · rw [orthogonal_isoFlag h hε (by omega)]
    congr 1
    omega

@[expose] noncomputable def hypBorel (h : UnitaryFieldData p f K) (r ε : ℕ) :
    Subgroup (hypSU h r ε) :=
  ⨅ i ∈ Set.Icc 1 r, MulAction.stabilizer (hypSU h r ε) (hypFlag h r ε i)

theorem mem_hypBorel {h : UnitaryFieldData p f K} {g : hypSU h r ε} :
    g ∈ hypBorel h r ε ↔ ∀ i, 1 ≤ i → i ≤ r → g • hypFlag h r ε i = hypFlag h r ε i := by
  simp only [hypBorel, Subgroup.mem_iInf, Set.mem_Icc, and_imp, MulAction.mem_stabilizer_iff]

theorem smul_eq_of_mulVec_mem {ι : Type} [Fintype ι] [DecidableEq ι] {g : GL ι K}
    {W : Submodule K (ι → K)} (h₁ : ∀ v ∈ W, (g : Matrix ι ι K) *ᵥ v ∈ W)
    (h₂ : ∀ v ∈ W, ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v ∈ W) : g • W = W := by
  refine le_antisymm (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x _ W).mp hx
    exact h₁ y hy
  · refine (Submodule.mem_smul_pointwise_iff_exists x _ W).mpr ⟨_, h₂ x hx, ?_⟩
    change (g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) = x
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem blockTriangular_inv_fullPos {g : GL (HypIndex r ε) K}
    (hg : (g : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular fullPos) :
    ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular
      fullPos := by
  have := Units.invertible g
  rw [Matrix.coe_units_inv]
  exact blockTriangular_inv_of_blockTriangular hg

theorem mem_hypBorel_of_blockTriangular (h : UnitaryFieldData p f K) {g : hypSU h r ε}
    (hg : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular
      fullPos) : g ∈ hypBorel h r ε := by
  rw [mem_hypBorel]
  intro i _ hir
  have hF : hypFlag h r ε i = posFlag r ε K i := by
    rw [hypFlag, ite_eq_left hir, isoFlag_eq_posFlag hir]
  rw [hF, Subgroup.smul_def]
  exact smul_eq_of_mulVec_mem (blockTriangular_fullPos_iff.mp hg i)
    (blockTriangular_fullPos_iff.mp (blockTriangular_inv_fullPos hg) i)

theorem mul_apply_self_of_blockTriangular {ι : Type} [Fintype ι] {b : ι → ℕ}
    (hb : Function.Injective b) {M N : Matrix ι ι K} (hM : M.BlockTriangular b)
    (hN : N.BlockTriangular b) (a : ι) : (M * N) a a = M a a * N a a := by
  rw [mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne (fun h' => hca (hb h')) with h' | h'
    · rw [hM h', zero_mul]
    · rw [hN h', mul_zero]
  · simp

@[expose] def fullUnitriangular (r ε : ℕ) (K : Type) [Field K] :
    Subgroup (GL (HypIndex r ε) K) where
  carrier := {g | (g : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular fullPos ∧
    ∀ a, (g : Matrix (HypIndex r ε) (HypIndex r ε) K) a a = 1}
  mul_mem' {g g'} hg hg' := by
    refine ⟨by rw [Units.val_mul]; exact hg.1.mul hg'.1, fun a => ?_⟩
    rw [Units.val_mul, mul_apply_self_of_blockTriangular fullPos_injective hg.1 hg'.1, hg.2,
      hg'.2, one_mul]
  one_mem' := ⟨by rw [Units.val_one]; exact blockTriangular_one, fun a => by simp⟩
  inv_mem' {g} hg := by
    refine ⟨blockTriangular_inv_fullPos hg.1, fun a => ?_⟩
    have := mul_apply_self_of_blockTriangular fullPos_injective hg.1
      (blockTriangular_inv_fullPos hg.1) a
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq, hg.2, one_mul] at this
    exact this.symm

theorem mem_fullUnitriangular {g : GL (HypIndex r ε) K} :
    g ∈ fullUnitriangular r ε K ↔
      (g : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular fullPos ∧
        ∀ a, (g : Matrix (HypIndex r ε) (HypIndex r ε) K) a a = 1 :=
  Iff.rfl

abbrev hypUnitriangular (h : UnitaryFieldData p f K) (r ε : ℕ) : Subgroup (hypSU h r ε) :=
  (fullUnitriangular r ε K).subgroupOf (hypSU h r ε)

theorem mem_hypUnitriangular {h : UnitaryFieldData p f K} {g : hypSU h r ε} :
    g ∈ hypUnitriangular h r ε ↔
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular
        fullPos ∧
        ∀ a, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a = 1 :=
  Iff.rfl

theorem hypUnitriangular_le_hypBorel (h : UnitaryFieldData p f K) :
    hypUnitriangular h r ε ≤ hypBorel h r ε := fun _ hg =>
  mem_hypBorel_of_blockTriangular h (mem_hypUnitriangular.mp hg).1

@[expose] noncomputable def hypProjBorel (h : UnitaryFieldData p f K) (r ε : ℕ) :
    Subgroup (hypPSU h r ε) :=
  (hypBorel h r ε).map (hypProj h r ε)

@[expose] def hypProjUnitriangular (h : UnitaryFieldData p f K) (r ε : ℕ) :
    Subgroup (hypPSU h r ε) :=
  (hypUnitriangular h r ε).map (hypProj h r ε)

@[expose] noncomputable def torusEntries (h : UnitaryFieldData p f K) (a : Fin r → Kˣ)
    (d : Fin ε → Kˣ) : HypIndex r ε → K
  | .inl i => a i
  | .inr (.inl k) => d k
  | .inr (.inr i) => (h.bar (a i))⁻¹

@[expose] noncomputable def torusRatio (h : UnitaryFieldData p f K) (a : Fin r → Kˣ)
    (d : Fin ε → Kˣ) : K :=
  (∏ i, (a i : K) / h.bar (a i)) * ∏ k, (d k : K)

theorem torusRatio_mul (h : UnitaryFieldData p f K) (a a' : Fin r → Kˣ) (d d' : Fin ε → Kˣ) :
    torusRatio h (a * a') (d * d') = torusRatio h a d * torusRatio h a' d' := by
  simp only [torusRatio, Pi.mul_apply, Units.val_mul, map_mul]
  rw [show ∏ i, (a i : K) * a' i / (h.bar (a i) * h.bar (a' i)) =
      (∏ i, (a i : K) / h.bar (a i)) * ∏ i, (a' i : K) / h.bar (a' i) by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (div_mul_div_comm _ _ _ _).symm,
    Finset.prod_mul_distrib]
  ring

theorem torusRatio_inv (h : UnitaryFieldData p f K) (a : Fin r → Kˣ) (d : Fin ε → Kˣ) :
    torusRatio h a⁻¹ d⁻¹ = (torusRatio h a d)⁻¹ := by
  simp only [torusRatio, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, mul_inv,
    ← Finset.prod_inv_distrib, div_eq_mul_inv, inv_inv]

theorem det_diagonal_torusEntries (h : UnitaryFieldData p f K) (a : Fin r → Kˣ)
    (d : Fin ε → Kˣ) : (diagonal (torusEntries h a d)).det = torusRatio h a d := by
  rw [det_diagonal, Fintype.prod_sum_type, Fintype.prod_sum_type, torusRatio]
  simp only [torusEntries, div_eq_mul_inv, Finset.prod_mul_distrib]
  ring

theorem diagonal_torusEntries_isometry (h : UnitaryFieldData p f K) (a : Fin r → Kˣ)
    {d : Fin ε → Kˣ} (hd : ∀ k, h.norm (d k) = 1) :
    ((diagonal (torusEntries h a d)).map h.bar)ᵀ * hypGram r ε K * diagonal (torusEntries h a d) =
      hypGram r ε K := by
  ext x y
  rw [mul_diagonal, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul, hypGram_apply]
  split_ifs with hxy
  · subst hxy
    rcases x with i | k | i
    · simp [torusEntries]
    · have := hd k
      simp only [UnitaryFieldData.norm] at this
      simp [torusEntries, mul_comm, this]
    · simp [torusEntries, h.bar_bar]
  · simp

@[expose] noncomputable def hypTorus (h : UnitaryFieldData p f K) (r ε : ℕ) :
    Subgroup (hypSU h r ε) where
  carrier := {g | ∃ (a : Fin r → Kˣ) (d : Fin ε → Kˣ), (∀ k, h.norm (d k : K) = 1) ∧
    torusRatio h a d = 1 ∧
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (torusEntries h a d)}
  mul_mem' := by
    rintro g g' ⟨a, d, hd, hp, hg⟩ ⟨a', d', hd', hp', hg'⟩
    refine ⟨a * a', d * d', fun k => ?_, by rw [torusRatio_mul, hp, hp', one_mul], ?_⟩
    · rw [Pi.mul_apply, Units.val_mul, norm_mul_eq h, hd, hd', one_mul]
    · rw [Subgroup.coe_mul, Units.val_mul, hg, hg', diagonal_mul_diagonal]
      congr 1
      funext x
      rcases x with i | k | i <;> simp [torusEntries, mul_comm]
  one_mem' := ⟨1, 1, fun k => by simp [UnitaryFieldData.norm], by simp [torusRatio], by
    rw [Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext x
    rcases x with i | k | i <;> simp [torusEntries]⟩
  inv_mem' := by
    rintro g ⟨a, d, hd, hp, hg⟩
    refine ⟨a⁻¹, d⁻¹, fun k => ?_, by rw [torusRatio_inv, hp, inv_one], ?_⟩
    · rw [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv_eq h, hd, inv_one]
    · rw [Subgroup.coe_inv]
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hg, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext x
      rcases x with i | k | i <;> simp [torusEntries]

theorem torusMat_mem_hypSU (h : UnitaryFieldData p f K) (a : Fin r → Kˣ) {d : Fin ε → Kˣ}
    (hd : ∀ k, h.norm (d k : K) = 1) (hp : torusRatio h a d = 1) :
    ∃ g ∈ hypTorus h r ε, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (torusEntries h a d) := by
  have hdet : (diagonal (torusEntries h a d)).det = 1 := by rw [det_diagonal_torusEntries, hp]
  let g : GL (HypIndex r ε) K :=
    GeneralLinearGroup.mkOfDetNeZero _ (by rw [hdet]; exact one_ne_zero)
  exact ⟨⟨g, diagonal_torusEntries_isometry h a hd, hdet⟩, ⟨a, d, hd, hp, rfl⟩, rfl⟩

theorem hypTorus_le_hypBorel (h : UnitaryFieldData p f K) : hypTorus h r ε ≤ hypBorel h r ε := by
  rintro g ⟨a, d, -, -, hg⟩
  refine mem_hypBorel_of_blockTriangular h ?_
  rw [hg]
  exact blockTriangular_diagonal _

end CFSG.ClassicalGroups.UnitaryFlag
