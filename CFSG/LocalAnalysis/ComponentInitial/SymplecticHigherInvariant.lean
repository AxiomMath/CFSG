module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagTriangular
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix SymplecticFlag CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

theorem mem_flag_iff {i : ℕ} {v : Fin r ⊕ Fin r → K} :
    v ∈ flag r K i ↔ ∀ x, i ≤ (flagOrder r x : ℕ) → v x = 0 := by
  by_cases hi : i ≤ r
  · rw [mem_flag_of_le hi, mem_isoFlag]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases x with j | j
      · rw [flagOrder_inl] at hx
        exact h2 j hx
      · exact h1 j
    · intro h
      refine ⟨fun j => h _ ?_, fun j hj => h _ ?_⟩
      · rw [flagOrder_inr]
        omega
      · rw [flagOrder_inl]
        exact hj
  · rw [mem_flag_of_lt (not_le.mp hi)]
    constructor
    · intro h x hx
      rcases x with j | j
      · rw [flagOrder_inl] at hx
        have := j.2
        omega
      · rw [flagOrder_inr] at hx
        exact h j (by have := j.2; omega)
    · intro h j hj
      exact h _ (by rw [flagOrder_inr]; have := j.2; omega)

theorem flag_zero : flag r K 0 = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hv => funext fun x => mem_flag_iff.mp hv x (Nat.zero_le _)

theorem flag_two_mul : flag r K (2 * r) = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_flag_iff.mpr fun x hx => absurd (flagOrder r x).2 (by omega)

theorem flag_mono {i j : ℕ} (hij : i ≤ j) : flag r K i ≤ flag r K j :=
  fun _ hv => mem_flag_iff.mpr fun x hx => mem_flag_iff.mp hv x (hij.trans hx)

@[expose] def IsFlagUpper (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) : Prop :=
  ∀ x y, (flagOrder r x : ℕ) < flagOrder r y → M y x = 0

theorem isFlagUpper_iff (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    IsFlagUpper M ↔ (reindex (flagOrder r) (flagOrder r) M).IsUpperTriangular := by
  constructor
  · intro h a b hba
    simp only [reindex_apply, submatrix_apply]
    exact h _ _ (by simpa using hba)
  · intro h x y hxy
    have := @h (flagOrder r y) (flagOrder r x) hxy
    simpa using this

theorem mem_borelSubgroup_iff_isFlagUpper {g : StatedSp r K} :
    g ∈ borelSubgroup r K ↔
      IsFlagUpper ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  rw [mem_borelSubgroup_iff_reindex, isFlagUpper_iff]

theorem mem_unipotent_iff_isFlagUpper {g : StatedSp r K} :
    g ∈ unipotent r K ↔
      IsFlagUpper ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ∧
        ∀ x, ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) x x = 1 := by
  rw [mem_unipotent_iff_reindex, isFlagUpper_iff]
  refine and_congr Iff.rfl ⟨fun h x => ?_, fun h a => h _⟩
  simpa using h (flagOrder r x)

theorem IsFlagUpper.mulVec_mem_flag {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hM : IsFlagUpper M) {i : ℕ} {v : Fin r ⊕ Fin r → K} (hv : v ∈ flag r K i) :
    M *ᵥ v ∈ flag r K i := by
  rw [mem_flag_iff] at hv ⊢
  intro y hy
  change ∑ x, M y x * v x = 0
  refine Finset.sum_eq_zero fun x _ => ?_
  rcases lt_or_ge (flagOrder r x : ℕ) (flagOrder r y) with h | h
  · rw [hM x y h, zero_mul]
  · rw [hv x (hy.trans h), mul_zero]

theorem unipotent_sub_mulVec_mem_flag {u : StatedSp r K} (hu : u ∈ unipotent r K) {i : ℕ}
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ flag r K (i + 1)) :
    ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v - v ∈
      flag r K i := by
  obtain ⟨hup, hdiag⟩ := mem_unipotent_iff_isFlagUpper.mp hu
  rw [mem_flag_iff] at hv ⊢
  intro y hy
  rw [Pi.sub_apply, mulVec, dotProduct, Finset.sum_eq_single y, hdiag, one_mul, sub_self]
  · intro x _ hxy
    rcases lt_or_gt_of_ne (fun h : (flagOrder r x : ℕ) = flagOrder r y =>
      hxy ((flagOrder r).injective (Fin.ext h))) with h | h
    · rw [hup x y h, zero_mul]
    · rw [hv x (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ y) h

theorem blockMat_mulVec_inl (A C : Matrix (Fin r) (Fin r) K) (v : Fin r ⊕ Fin r → K)
    (m : Fin r) :
    (blockMat A C *ᵥ v) (Sum.inl m) = (A *ᵥ (v ∘ Sum.inl) + (A * C) *ᵥ (v ∘ Sum.inr)) m := by
  rw [blockMat, fromBlocks_mulVec, Sum.elim_inl]

theorem mem_isoFlag_succ_of_forall_unipotent {d : ℕ} (hd : d < r) {v : Fin r ⊕ Fin r → K}
    (hv : ∀ j : Fin r, (j : ℕ) < d → v (Sum.inr j) = 0)
    (hu : ∀ u ∈ unipotent r K,
      ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v - v ∈
        isoFlag r K d) :
    v ∈ isoFlag r K (d + 1) := by
  rw [mem_isoFlag]
  constructor
  · intro j
    by_cases hj : (j : ℕ) < d
    · exact hv j hj
    obtain ⟨u, hu', hcoe⟩ := exists_mem_unipotent (K := K) isUnitriangular_one
      (transpose_single j j (1 : K))
    have h := (mem_isoFlag.mp (hu u hu')).2 j (not_lt.mp hj)
    rw [hcoe, Pi.sub_apply, blockMat_mulVec_inl] at h
    simpa [single_mulVec] using h
  · intro j hj
    set d' : Fin r := ⟨d, hd⟩
    have hdj : d' < j := by
      change d < (j : ℕ)
      omega
    have hA : IsUnitriangular (1 + single d' j (1 : K)) := by
      refine ⟨fun a b hba => ?_, fun a => ?_⟩
      · have hab : a ≠ b := fun h => (lt_irrefl a) (h ▸ hba)
        rw [Matrix.add_apply, one_apply_ne hab, single_apply, ite_eq_right, zero_add]
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hdj hba
      · rw [Matrix.add_apply, one_apply_eq, single_apply, ite_eq_right, add_zero]
        rintro ⟨rfl, h⟩
        exact (ne_of_lt hdj) h.symm
    obtain ⟨u, hu', hcoe⟩ := exists_mem_unipotent hA (transpose_zero (m := Fin r) (n := Fin r))
    have h := (mem_isoFlag.mp (hu u hu')).2 d' le_rfl
    rw [hcoe, Pi.sub_apply, blockMat_mulVec_inl] at h
    simpa [add_mulVec, single_mulVec] using h

theorem isTotallyIsotropic_isoFlag (d : ℕ) :
    IsTotallyIsotropic (pairedSympForm K r) (isoFlag r K d) := by
  intro v hv w hw
  have hv' := (mem_isoFlag.mp hv).1
  have hw' := (mem_isoFlag.mp hw).1
  have hvr : (v ∘ Sum.inr : Fin r → K) = 0 := funext hv'
  have hwr : (w ∘ Sum.inr : Fin r → K) = 0 := funext hw'
  rw [pairedSympForm_apply, hvr, hwr, dotProduct_zero, zero_dotProduct, sub_zero]

theorem finrank_isoFlag {d : ℕ} (hd : d ≤ r) : Module.finrank K (isoFlag r K d) = d := by
  have h := finrank_span_inl_image (Pi.basisFun K (Fin r ⊕ Fin r)) hd
  rw [← Set.image_comp] at h
  have hfun : (fun j : Fin r => (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K)) =
      ⇑(Pi.basisFun K (Fin r ⊕ Fin r)) ∘ Sum.inl :=
    funext fun j => (Pi.basisFun_apply K (Fin r ⊕ Fin r) (Sum.inl j)).symm
  rw [isoFlag, hfun]
  exact h

theorem apply_inr_eq_zero_of_isoFlag_le {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) {d : ℕ} (hdW : isoFlag r K d ≤ W)
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ W) (j : Fin r) (hj : (j : ℕ) < d) :
    v (Sum.inr j) = 0 := by
  have hmem : v ∈ (pairedSympForm K r).orthogonal (isoFlag r K d) :=
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => hW n (hdW hn) v hv
  exact mem_orthogonal_isoFlag.mp hmem j hj

theorem eq_isoFlag_or_succ_le {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W)
    (hU : ∀ u ∈ unipotent r K, ∀ v ∈ W,
      ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W)
    {d : ℕ} (hdr : d ≤ r) (hdW : isoFlag r K d ≤ W) :
    W = isoFlag r K d ∨ (d < r ∧ isoFlag r K (d + 1) ≤ W) := by
  classical
  by_cases hWd : W = isoFlag r K d
  · exact Or.inl hWd
  right
  obtain ⟨v₀, hv₀W, hv₀d⟩ : ∃ v ∈ W, v ∉ isoFlag r K d := by
    by_contra! h
    exact hWd (le_antisymm (fun v hv => h v hv) hdW)
  have hd : d < r := by
    refine lt_of_le_of_ne hdr fun hdr' => hv₀d ?_
    subst hdr'
    exact mem_isoFlag.mpr ⟨fun j => apply_inr_eq_zero_of_isoFlag_le hW hdW hv₀W j j.2,
      fun j hj => absurd j.2 (not_lt.mpr hj)⟩
  refine ⟨hd, ?_⟩
  have hex : ∃ i, ∃ v ∈ W, v ∈ flag r K i ∧ v ∉ isoFlag r K d :=
    ⟨2 * r, v₀, hv₀W, by rw [flag_two_mul]; trivial, hv₀d⟩
  obtain ⟨v, hvW, hvi, hvd⟩ := Nat.find_spec hex
  have hi0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, flag_zero] at hvi
    exact hvd ((Submodule.mem_bot K).mp hvi ▸ Submodule.zero_mem _)
  obtain ⟨i', hi'⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hmin : ∀ u ∈ unipotent r K,
      ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v - v ∈
        isoFlag r K d := by
    intro u hu
    by_contra hnot
    have := Nat.find_min hex (show i' < Nat.find hex by omega)
    exact this ⟨_, sub_mem (hU u hu v hvW) hvW,
      unipotent_sub_mulVec_mem_flag hu (by rw [hi'] at hvi; exact hvi), hnot⟩
  have hv1 := mem_isoFlag_succ_of_forall_unipotent hd
    (apply_inr_eq_zero_of_isoFlag_le hW hdW hvW) hmin
  set d' : Fin r := ⟨d, hd⟩
  have hvd' : v (Sum.inl d') ≠ 0 := by
    intro h0
    refine hvd (mem_isoFlag.mpr ⟨(mem_isoFlag.mp hv1).1, fun j hj => ?_⟩)
    rcases lt_or_eq_of_le hj with hj | hj
    · exact (mem_isoFlag.mp hv1).2 j hj
    · rw [show j = d' from Fin.ext hj.symm]
      exact h0
  have hrest : v - v (Sum.inl d') • Pi.single (Sum.inl d') 1 ∈ isoFlag r K d := by
    refine mem_isoFlag.mpr ⟨fun j => ?_, fun j hj => ?_⟩
    · simp [(mem_isoFlag.mp hv1).1 j]
    · rcases lt_or_eq_of_le hj with hj | hj
      · have hjd : j ≠ d' := fun h => by rw [h] at hj; exact lt_irrefl _ hj
        simp [(mem_isoFlag.mp hv1).2 j hj, hjd]
      · rw [show j = d' from Fin.ext hj.symm]
        simp
  have hed : (Pi.single (Sum.inl d') (1 : K) : Fin r ⊕ Fin r → K) ∈ W := by
    have h := sub_mem hvW (hdW hrest)
    rw [sub_sub_cancel] at h
    have := W.smul_mem (v (Sum.inl d'))⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hvd', one_smul] at this
  rw [isoFlag, Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj | hj
  · exact hdW (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [show j = d' from Fin.ext hj]
    exact hed

theorem exists_eq_isoFlag {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W)
    (hU : ∀ u ∈ unipotent r K, ∀ v ∈ W,
      ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W) :
    ∃ d ≤ r, W = isoFlag r K d := by
  have key : ∀ n d, d + n = r → isoFlag r K d ≤ W → ∃ d ≤ r, W = isoFlag r K d := by
    intro n
    induction n with
    | zero =>
      intro d hd hdW
      rcases eq_isoFlag_or_succ_le hW hU (by omega) hdW with h | h
      · exact ⟨d, by omega, h⟩
      · omega
    | succ n ih =>
      intro d hd hdW
      rcases eq_isoFlag_or_succ_le hW hU (by omega) hdW with h | h
      · exact ⟨d, by omega, h⟩
      · exact ih (d + 1) (by omega) h.2
  refine key r 0 (zero_add r) ?_
  rw [isoFlag, Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  exact absurd hj (Nat.not_lt_zero _)

theorem unipotent_mulVec_mem_isoFlag {u : StatedSp r K} (hu : u ∈ unipotent r K) (d : ℕ)
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ isoFlag r K d) :
    ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈
      isoFlag r K d := by
  obtain ⟨A, C, hA, -, hcoe⟩ := mem_unipotent.mp hu
  rw [hcoe]
  exact blockMat_mulVec_mem_isoFlag hA.1 C hv

theorem unitriangular_invariant_isotropic_subspaces :
    {v : Fin r ⊕ Fin r → K | ∀ u ∈ unipotent r K,
      ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = v} =
      (flag r K 1 : Set (Fin r ⊕ Fin r → K)) ∧
    (∀ W : Submodule K (Fin r ⊕ Fin r → K),
      (IsTotallyIsotropic (pairedSympForm K r) W ∧ ∀ u ∈ unipotent r K, ∀ v ∈ W,
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W) ↔
      ∃ d ≤ r, W = flag r K d) ∧
    IsCompleteIsotropicFlag (pairedSympForm K r) r (flag r K) ∧
    (∀ i ≤ r, ∀ u ∈ unipotent r K, ∀ v ∈ flag r K i,
      ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈
        flag r K i) ∧
    ∀ G : ℕ → Submodule K (Fin r ⊕ Fin r → K),
      IsCompleteIsotropicFlag (pairedSympForm K r) r G →
      (∀ i ≤ r, ∀ u ∈ unipotent r K, ∀ v ∈ G i,
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ G i) →
      ∀ i ≤ r, G i = flag r K i := by
  have hsub : ∀ W : Submodule K (Fin r ⊕ Fin r → K),
      (IsTotallyIsotropic (pairedSympForm K r) W ∧ ∀ u ∈ unipotent r K, ∀ v ∈ W,
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W) ↔
      ∃ d ≤ r, W = flag r K d := by
    intro W
    constructor
    · rintro ⟨hW, hU⟩
      obtain ⟨d, hd, rfl⟩ := exists_eq_isoFlag hW hU
      exact ⟨d, hd, (Submodule.ext fun v => (mem_flag_of_le hd).symm)⟩
    · rintro ⟨d, hd, rfl⟩
      have hfl : flag r K d = isoFlag r K d := Submodule.ext fun v => mem_flag_of_le hd
      rw [hfl]
      exact ⟨isTotallyIsotropic_isoFlag d, fun u hu v hv => unipotent_mulVec_mem_isoFlag hu d hv⟩
  refine ⟨?_, hsub, ⟨fun i hi => ?_, fun i _ => flag_mono (Nat.le_succ i), fun i hi => ?_⟩,
    fun i hi u hu v hv => ?_, fun G hG hGU i hi => ?_⟩
  · ext v
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        exact mem_flag_iff.mpr fun x => x.elim (fun j => j.elim0) (fun j => j.elim0)
      rw [mem_flag_of_le hr]
      refine mem_isoFlag_succ_of_forall_unipotent hr (fun j hj => absurd hj (Nat.not_lt_zero _))
        fun u hu => ?_
      rw [h u hu, sub_self]
      exact Submodule.zero_mem _
    · intro hv u hu
      have h := unipotent_sub_mulVec_mem_flag hu (i := 0) hv
      rw [flag_zero, Submodule.mem_bot, sub_eq_zero] at h
      exact h
  · rw [Submodule.ext fun v => mem_flag_of_le hi]
    exact finrank_isoFlag hi
  · rw [Submodule.ext fun v => mem_flag_of_le hi]
    exact isTotallyIsotropic_isoFlag i
  · obtain ⟨A, C, hA, -, hcoe⟩ := mem_unipotent.mp hu
    rw [mem_flag_of_le hi] at hv ⊢
    rw [hcoe]
    exact blockMat_mulVec_mem_isoFlag hA.1 C hv
  · obtain ⟨d, hd, hGd⟩ := (hsub (G i)).mp ⟨hG.2.2 i hi, hGU i hi⟩
    have h1 := hG.1 i hi
    rw [hGd, Submodule.ext fun v => mem_flag_of_le hd, finrank_isoFlag hd] at h1
    rw [hGd, h1]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
