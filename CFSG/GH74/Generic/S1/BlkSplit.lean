module

public import CFSG.GH74.Generic.S1.SymBlocksLin
public import CFSG.GH74.Generic.S1.SymBlocksUni
public import CFSG.ClassicalInvolution.Generic.SL2Involution

public section

namespace CFSG.GH74.Generic.S1

open Matrix SymBlocksUni CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup
  CFSG.LieType.Universal.Unitary
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

section Split

theorem fin4_cover {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (i : Fin 4) : i = a ∨ i = b ∨ i = c ∨ i = d := by
  revert a b c d i
  decide

@[expose] def SplitAt (a b c d : Fin 4) (M : Matrix (Fin 4) (Fin 4) F) : Prop :=
  ∀ i j : Fin 4, (((i = a ∨ i = b) ∧ (j = c ∨ j = d)) ∨ ((i = c ∨ i = d) ∧ (j = a ∨ j = b))) →
    M i j = 0

theorem SplitAt.symm {a b c d : Fin 4} {M : Matrix (Fin 4) (Fin 4) F} (h : SplitAt a b c d M) :
    SplitAt c d a b M := fun i j hij => h i j hij.symm

variable {a b c d : Fin 4}

theorem SplitAt.mul (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) {M N : Matrix (Fin 4) (Fin 4) F} (hM : SplitAt a b c d M)
    (hN : SplitAt a b c d N) : SplitAt a b c d (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := fin4_cover hab hac had hbc hbd hcd k
  rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rcases hk with rfl | rfl | rfl | rfl
    · rw [hN _ j (Or.inl ⟨Or.inl rfl, hj⟩), mul_zero]
    · rw [hN _ j (Or.inl ⟨Or.inr rfl, hj⟩), mul_zero]
    · rw [hM i _ (Or.inl ⟨hi, Or.inl rfl⟩), zero_mul]
    · rw [hM i _ (Or.inl ⟨hi, Or.inr rfl⟩), zero_mul]
  · rcases hk with rfl | rfl | rfl | rfl
    · rw [hM i _ (Or.inr ⟨hi, Or.inl rfl⟩), zero_mul]
    · rw [hM i _ (Or.inr ⟨hi, Or.inr rfl⟩), zero_mul]
    · rw [hN _ j (Or.inr ⟨Or.inl rfl, hj⟩), mul_zero]
    · rw [hN _ j (Or.inr ⟨Or.inr rfl, hj⟩), mul_zero]

@[expose] def ablk (a b : Fin 4) (M : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun x y => M (pairIdx a b x) (pairIdx a b y)

theorem ablk_one (a b : Fin 4) (hab : a ≠ b) : ablk a b (1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  ext x y
  simp only [ablk, Matrix.of_apply, Matrix.one_apply, (pairIdx_injective hab).eq_iff]

theorem ablk_mul (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) {M N : Matrix (Fin 4) (Fin 4) F} (hM : SplitAt a b c d M) :
    ablk a b (M * N) = ablk a b M * ablk a b N := by
  ext x y
  simp only [ablk, Matrix.of_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective (pairIdx a b) (pairIdx_injective hab)
    (fun z => M (pairIdx a b x) (pairIdx a b z) * N (pairIdx a b z) (pairIdx a b y))
    (fun k => M (pairIdx a b x) k * N k (pairIdx a b y)) ?_ fun z => rfl).symm
  intro k hk
  have hk' : k = c ∨ k = d := by
    have := fin4_cover hab hac had hbc hbd hcd k
    rcases this with h | h | h | h
    · exact absurd ⟨0, by simp [pairIdx, h]⟩ hk
    · exact absurd ⟨1, by simp [pairIdx, h]⟩ hk
    · exact Or.inl h
    · exact Or.inr h
  have hx : pairIdx a b x = a ∨ pairIdx a b x = b := by
    fin_cases x <;> simp [pairIdx]
  rw [hM _ k (Or.inl ⟨hx, hk'⟩), zero_mul]

theorem selL_transpose_mul_selL_of_disjoint {k l m : ℕ} {ι : Fin k → Fin m} {ι' : Fin l → Fin m}
    (hdisj : ∀ x y, ι x ≠ ι' y) : (selL F ι)ᵀ * selL F ι' = 0 := by
  ext x y
  rw [Matrix.mul_apply]
  refine (Finset.sum_eq_zero fun t _ => ?_).trans (Matrix.zero_apply x y).symm
  simp only [Matrix.transpose_apply, selL_apply]
  by_cases h : t = ι x
  · have : t ≠ ι' y := fun h' => hdisj x y (h.symm.trans h')
    simp [this]
  · simp [h]

theorem blkMat_mul_disjoint {k l m : ℕ} {ι : Fin k → Fin m} {ι' : Fin l → Fin m}
    (hdisj : ∀ x y, ι x ≠ ι' y) (A : Matrix (Fin k) (Fin k) F) (B : Matrix (Fin l) (Fin l) F) :
    blkMat ι A * blkMat ι' B = blkMat ι A + blkMat ι' B - 1 := by
  have hL := selL_transpose_mul_selL_of_disjoint (F := F) hdisj
  unfold blkMat
  set L : Matrix (Fin m) (Fin k) F := selL F ι
  set L' : Matrix (Fin m) (Fin l) F := selL F ι'
  have hXY : (L * (A - 1) * Lᵀ) * (L' * (B - 1) * L'ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Lᵀ L' ((B - 1) * L'ᵀ), hL]
    simp
  have : (1 + L * (A - 1) * Lᵀ) * (1 + L' * (B - 1) * L'ᵀ) =
      1 + L * (A - 1) * Lᵀ + L' * (B - 1) * L'ᵀ +
        (L * (A - 1) * Lᵀ) * (L' * (B - 1) * L'ᵀ) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [this, hXY]
  abel

theorem pairIdx_disjoint (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∀ x y, pairIdx a b x ≠ pairIdx c d y := by
  intro x y
  fin_cases x <;> fin_cases y <;> simp [pairIdx] <;> assumption

theorem exists_pairIdx_or (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (i : Fin 4) :
    (∃ x, i = pairIdx a b x) ∨ (∃ y, i = pairIdx c d y) := by
  rcases fin4_cover hab hac had hbc hbd hcd i with h | h | h | h
  · exact Or.inl (exists_pairIdx_iff.2 (Or.inl h))
  · exact Or.inl (exists_pairIdx_iff.2 (Or.inr h))
  · exact Or.inr (exists_pairIdx_iff.2 (Or.inl h))
  · exact Or.inr (exists_pairIdx_iff.2 (Or.inr h))

theorem split_eq_add (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) {M : Matrix (Fin 4) (Fin 4) F} (hM : SplitAt a b c d M) :
    M = blkMat (pairIdx a b) (ablk a b M) + blkMat (pairIdx c d) (ablk c d M) - 1 := by
  have hι := pairIdx_injective hab
  have hι' := pairIdx_injective hcd
  have hdisj := pairIdx_disjoint hac had hbc hbd
  have hdisj' : ∀ x y, pairIdx c d x ≠ pairIdx a b y := fun x y => (hdisj y x).symm
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply]
  rcases exists_pairIdx_or hab hac had hbc hbd hcd i with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases exists_pairIdx_or hab hac had hbc hbd hcd j with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rw [blkMat_apply_ι hι, blkMat_apply_of_not_mem_left _ (fun z => hdisj x z)]
    simp [ablk]
  · have h0 : M (pairIdx a b x) (pairIdx c d y) = 0 :=
      hM _ _ (Or.inl ⟨exists_pairIdx_iff.1 ⟨x, rfl⟩, exists_pairIdx_iff.1 ⟨y, rfl⟩⟩)
    rw [blkMat_apply_of_not_mem_right _ _ (fun z => hdisj' y z),
      blkMat_apply_of_not_mem_left _ (fun z => hdisj x z), h0,
      Matrix.one_apply_ne (hdisj x y)]
    ring
  · have h0 : M (pairIdx c d x) (pairIdx a b y) = 0 :=
      hM _ _ (Or.inr ⟨exists_pairIdx_iff.1 ⟨x, rfl⟩, exists_pairIdx_iff.1 ⟨y, rfl⟩⟩)
    rw [blkMat_apply_of_not_mem_right _ _ (fun z => hdisj y z),
      blkMat_apply_of_not_mem_left _ (fun z => hdisj' x z), h0,
      Matrix.one_apply_ne (hdisj' x y)]
    ring
  · rw [blkMat_apply_ι hι', blkMat_apply_of_not_mem_left _ (fun z => hdisj' x z)]
    simp [ablk]

theorem split_eq_mul (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) {M : Matrix (Fin 4) (Fin 4) F} (hM : SplitAt a b c d M) :
    M = blkMat (pairIdx a b) (ablk a b M) * blkMat (pairIdx c d) (ablk c d M) := by
  rw [blkMat_mul_disjoint (pairIdx_disjoint hac had hbc hbd)]
  exact split_eq_add hab hac had hbc hbd hcd hM

theorem det_split (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) {M : Matrix (Fin 4) (Fin 4) F} (hM : SplitAt a b c d M) :
    M.det = (ablk a b M).det * (ablk c d M).det := by
  have := congrArg Matrix.det (split_eq_mul hab hac had hbc hbd hcd hM)
  rwa [Matrix.det_mul, det_blkMat (pairIdx_injective hab), det_blkMat (pairIdx_injective hcd)]
    at this

@[expose] def zblkMat (F : Type) [Field F] (c d : Fin 4) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal fun i => if i = c ∨ i = d then -1 else 1

theorem splitAt_of_comm (h2 : (2 : F) ≠ 0) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) {M : Matrix (Fin 4) (Fin 4) F}
    (h : M * zblkMat F c d = zblkMat F c d * M) : SplitAt a b c d M := by
  intro i j hij
  have h1 := congrFun (congrFun h i) j
  simp only [zblkMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have hnab : ∀ k, (k = a ∨ k = b) → ¬ (k = c ∨ k = d) := by
    rintro k (rfl | rfl) (h' | h') <;> simp_all
  rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have e1 : (if j = c ∨ j = d then (-1 : F) else 1) = -1 := by simp [hj]
    have e2 : (if i = c ∨ i = d then (-1 : F) else 1) = 1 := by simp [hnab i hi]
    rw [e1, e2] at h1
    have h' : (2 : F) * M i j = 0 := by linear_combination -h1
    exact (mul_eq_zero.1 h').resolve_left h2
  · have e1 : (if j = c ∨ j = d then (-1 : F) else 1) = 1 := by simp [hnab j hj]
    have e2 : (if i = c ∨ i = d then (-1 : F) else 1) = -1 := by simp [hi]
    rw [e1, e2] at h1
    have h' : (2 : F) * M i j = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h').resolve_left h2

theorem blkMat_neg_one_eq_zblk (hcd : c ≠ d) :
    blkMat (pairIdx c d) (-1 : Matrix (Fin 2) (Fin 2) F) = zblkMat F c d := by
  have hι := pairIdx_injective hcd
  ext i j
  by_cases hi : ∃ x, i = pairIdx c d x
  · by_cases hj : ∃ y, j = pairIdx c d y
    · obtain ⟨x, rfl⟩ := hi
      obtain ⟨y, rfl⟩ := hj
      rw [blkMat_apply_ι hι]
      have hx : pairIdx c d x = c ∨ pairIdx c d x = d := exists_pairIdx_iff.1 ⟨x, rfl⟩
      simp only [zblkMat, Matrix.diagonal_apply, hι.eq_iff, hx, ↓reduceIte]
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy]
    · rw [blkMat_apply_of_not_mem_right _ _ (fun y h => hj ⟨y, h⟩)]
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp only [zblkMat, Matrix.diagonal_apply, hij, ↓reduceIte, Matrix.one_apply_ne hij]
  · rw [blkMat_apply_of_not_mem_left _ (fun x h => hi ⟨x, h⟩)]
    by_cases hij : i = j
    · subst hij
      have : ¬ (i = c ∨ i = d) := fun h => hi (exists_pairIdx_iff.2 h)
      simp [zblkMat, this]
    · simp only [zblkMat, Matrix.diagonal_apply, hij, ↓reduceIte, Matrix.one_apply_ne hij]

theorem eq_zblk_of_involution (h2 : (2 : F) ≠ 0) (hcd : c ≠ d) {Z0 : Matrix (Fin 4) (Fin 4) F}
    (hid : IdOut c d Z0) (hsq : Z0 * Z0 = 1) (hdet : Z0.det = 1) (hne : Z0 ≠ 1) :
    Z0 = zblkMat F c d := by
  have hι := pairIdx_injective hcd
  have hZ := eq_blkMat_of_idOut hcd hid
  set Zb : Matrix (Fin 2) (Fin 2) F := Matrix.of fun x y => Z0 (pairIdx c d x) (pairIdx c d y)
    with hZb
  have h1 : Zb * Zb = 1 := by
    apply blkMat_injective hι
    rw [blkMat_mul hι, ← hZ, hsq, blkMat_one]
  have hdZ : Zb.det = 1 := by
    rw [← det_blkMat hι, ← hZ, hdet]
  let u : SL(2, F) := ⟨Zb, hdZ⟩
  have hu : u * u = 1 := Subtype.ext h1
  rcases CFSG.ClassicalInvolution.Generic.sl2_sq_eq_one h2 hu with h | h
  · exfalso
    apply hne
    have : Zb = 1 := congrArg Subtype.val h
    rw [hZ, this, blkMat_one]
  · have : Zb = -1 := by simpa using congrArg Subtype.val h
    rw [hZ, this, blkMat_neg_one_eq_zblk hcd]

@[expose] noncomputable def mkBlkSL (a b : Fin 4) (hab : a ≠ b) (A : Matrix (Fin 2) (Fin 2) F)
    (hA : A.det = 1) : ↥(StatedSL 4 F) :=
  ⟨⟨blkMat (pairIdx a b) A, blkMat (pairIdx a b) A⁻¹, by
      rw [← blkMat_mul (pairIdx_injective hab), Matrix.mul_nonsing_inv _ (by rw [hA]; exact isUnit_one),
        blkMat_one], by
      rw [← blkMat_mul (pairIdx_injective hab), Matrix.nonsing_inv_mul _ (by rw [hA]; exact isUnit_one),
        blkMat_one]⟩, by
    rw [statedSL_eq_detOne, mem_detOne]
    show (blkMat (pairIdx a b) A).det = 1
    rw [det_blkMat (pairIdx_injective hab), hA]⟩

theorem coe_mkBlkSL (a b : Fin 4) (hab : a ≠ b) (A : Matrix (Fin 2) (Fin 2) F) (hA : A.det = 1) :
    (((mkBlkSL a b hab A hA : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blkMat (pairIdx a b) A := rfl

theorem mkBlkSL_mem (a b : Fin 4) (hab : a ≠ b) (A : Matrix (Fin 2) (Fin 2) F) (hA : A.det = 1) :
    mkBlkSL a b hab A hA ∈ blkLin (F := F) a b := by
  rw [mem_blkLin, coe_mkBlkSL]
  exact idOut_blkMat A

theorem perfect_le_pair_lin (h2 : (2 : F) ≠ 0) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {z0 : ↥(StatedSL 4 F)}
    (hz0 : z0 ∈ blkLin (F := F) c d) (hz0sq : z0 * z0 = 1) (hz01 : z0 ≠ 1)
    (P : Subgroup ↥(StatedSL 4 F)) (hP : ∀ g ∈ P, g * z0 = z0 * g) (hperf : ⁅P, P⁆ = P) :
    P ≤ blkLin (F := F) a b ⊔ blkLin (F := F) c d := by
  have hz0mat : (((z0 : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      zblkMat F c d := by
    refine eq_zblk_of_involution h2 hcd (fun i j hij => hz0 i j hij) ?_ ?_ ?_
    · have := congrArg
        (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hz0sq
      simpa using this
    · have h1 : ((z0 : ↥(StatedSL 4 F)) : GL (Fin 4) F) ∈ detOne F 4 := by
        rw [← statedSL_eq_detOne]
        exact z0.2
      rw [mem_detOne] at h1
      exact h1
    · intro h
      apply hz01
      exact Subtype.ext (Units.ext (by simpa using h))
  have hsplit : ∀ g ∈ P,
      SplitAt a b c d (((g : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro g hg
    refine splitAt_of_comm h2 hac had hbc hbd ?_
    have := congrArg
      (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) (hP g hg)
    simpa [hz0mat] using this
  conv_lhs => rw [← hperf]
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hgs := hsplit g hg
  have hhs := hsplit h hh
  have hgis := hsplit _ (P.inv_mem hg)
  have hhis := hsplit _ (P.inv_mem hh)
  have hQ : (((⁅g, h⁆ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (g : GL (Fin 4) F) * (h : GL (Fin 4) F) * ((g⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) *
        ((h⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) := by
    rw [commutatorElement_def]
    simp [mul_assoc]
  set G : Matrix (Fin 4) (Fin 4) F := (((g : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    with hG
  set Hm : Matrix (Fin 4) (Fin 4) F := (((h : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    with hHm
  set Gi : Matrix (Fin 4) (Fin 4) F :=
    (((g⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hGi
  set Hi : Matrix (Fin 4) (Fin 4) F :=
    (((h⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hHi
  have hGGi : G * Gi = 1 := by
    have h1 : ((g : GL (Fin 4) F) * (g : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) = 1 := mul_inv_cancel _
    have h2' := congrArg Units.val h1
    rw [Units.val_mul, Units.val_one] at h2'
    exact h2'
  have hHHi : Hm * Hi = 1 := by
    have h1 : ((h : GL (Fin 4) F) * (h : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) = 1 := mul_inv_cancel _
    have h2' := congrArg Units.val h1
    rw [Units.val_mul, Units.val_one] at h2'
    exact h2'
  have hsGH : SplitAt a b c d (G * Hm) := SplitAt.mul hab hac had hbc hbd hcd hgs hhs
  have hsGHG : SplitAt a b c d (G * Hm * Gi) := SplitAt.mul hab hac had hbc hbd hcd hsGH hgis
  have hsK : SplitAt a b c d (G * Hm * Gi * Hi) := SplitAt.mul hab hac had hbc hbd hcd hsGHG hhis
  have hdet1 : ∀ X Y : Matrix (Fin 4) (Fin 4) F, SplitAt a b c d X → X * Y = 1 →
      (ablk a b X).det * (ablk a b Y).det = 1 := by
    intro X Y hX hXY
    have h1 := ablk_mul hab hac had hbc hbd hcd (N := Y) hX
    rw [hXY, ablk_one a b hab] at h1
    rw [← Matrix.det_mul, ← h1, Matrix.det_one]
  have hdG := hdet1 G Gi hgs hGGi
  have hdH := hdet1 Hm Hi hhs hHHi
  have hKab : (ablk a b (G * Hm * Gi * Hi)).det = 1 := by
    rw [ablk_mul hab hac had hbc hbd hcd hsGHG, ablk_mul hab hac had hbc hbd hcd hsGH,
      ablk_mul hab hac had hbc hbd hcd hgs]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    calc (ablk a b G).det * (ablk a b Hm).det * (ablk a b Gi).det * (ablk a b Hi).det
        = ((ablk a b G).det * (ablk a b Gi).det) * ((ablk a b Hm).det * (ablk a b Hi).det) := by
          ring
      _ = 1 := by rw [hdG, hdH, one_mul]
  have hdetK : (G * Hm * Gi * Hi).det = 1 := by
    have h1 : (((⁅g, h⁆ : ↥(StatedSL 4 F)) : GL (Fin 4) F)) ∈ detOne F 4 := by
      rw [← statedSL_eq_detOne]
      exact (⁅g, h⁆ : ↥(StatedSL 4 F)).2
    rw [mem_detOne, hQ] at h1
    exact h1
  have hKcd : (ablk c d (G * Hm * Gi * Hi)).det = 1 := by
    have h1 := det_split hab hac had hbc hbd hcd hsK
    rw [hdetK, hKab, one_mul] at h1
    exact h1.symm
  have hKeq := split_eq_mul hab hac had hbc hbd hcd hsK
  have hgh : ⁅g, h⁆ = mkBlkSL a b hab _ hKab * mkBlkSL c d hcd _ hKcd := by
    apply Subtype.ext
    apply Units.ext
    rw [hQ]
    exact hKeq
  rw [hgh]
  exact (blkLin a b ⊔ blkLin c d).mul_mem (Subgroup.mem_sup_left (mkBlkSL_mem a b hab _ hKab))
    (Subgroup.mem_sup_right (mkBlkSL_mem c d hcd _ hKcd))

theorem conjTr_mul_ablk (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (σ : F ≃+* F) {K : Matrix (Fin 4) (Fin 4) F} (hs : SplitAt a b c d K)
    (hU : conjTr σ K * K = 1) : conjTr σ (ablk a b K) * ablk a b K = 1 := by
  ext x y
  have h1 := congrFun (congrFun hU (pairIdx a b x)) (pairIdx a b y)
  have hone : (1 : Matrix (Fin 4) (Fin 4) F) (pairIdx a b x) (pairIdx a b y) =
      (1 : Matrix (Fin 2) (Fin 2) F) x y := by
    simp only [Matrix.one_apply, (pairIdx_injective hab).eq_iff]
  rw [hone] at h1
  rw [← h1]
  simp only [Matrix.mul_apply]
  refine Fintype.sum_of_injective (pairIdx a b) (pairIdx_injective hab)
    (fun z => (conjTr σ (ablk a b K)) x z * (ablk a b K) z y)
    (fun k => (conjTr σ K) (pairIdx a b x) k * K k (pairIdx a b y)) ?_ fun z => rfl
  intro k hk
  have hk' : k = c ∨ k = d := by
    have := fin4_cover hab hac had hbc hbd hcd k
    rcases this with h | h | h | h
    · exact absurd ⟨0, by simp [pairIdx, h]⟩ hk
    · exact absurd ⟨1, by simp [pairIdx, h]⟩ hk
    · exact Or.inl h
    · exact Or.inr h
  have hx : pairIdx a b x = a ∨ pairIdx a b x = b := by
    fin_cases x <;> simp [pairIdx]
  have h0 : K k (pairIdx a b x) = 0 := hs _ _ (Or.inr ⟨hk', hx⟩)
  simp [conjTr, h0]

theorem conjTr_mul_ablk' (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (σ : F ≃+* F) {K : Matrix (Fin 4) (Fin 4) F} (hs : SplitAt a b c d K)
    (hU : conjTr σ K * K = 1) : conjTr σ (ablk c d K) * ablk c d K = 1 :=
  conjTr_mul_ablk hcd hac.symm hbc.symm had.symm hbd.symm hab σ hs.symm hU

section Uni

variable {p f : ℕ} [Finite F] [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)

include hF in
theorem perfect_le_pair_uni (h2 : (2 : F) ≠ 0) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {z0 : ↥(StatedSU 4 (p ^ f) F)}
    (hz0 : z0 ∈ uniBlk F (p ^ f) c d) (hz0sq : z0 * z0 = 1) (hz01 : z0 ≠ 1)
    (P : Subgroup ↥(StatedSU 4 (p ^ f) F)) (hP : ∀ g ∈ P, g * z0 = z0 * g) (hperf : ⁅P, P⁆ = P) :
    P ≤ uniBlk F (p ^ f) a b ⊔ uniBlk F (p ^ f) c d := by
  have hz0mat : (((z0 : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      zblkMat F c d := by
    refine eq_zblk_of_involution h2 hcd ((mem_uniBlk_iff hF).1 hz0) ?_
      (unitary_of_mem_statedSU hF z0).1 ?_
    · have := congrArg
        (fun x : ↥(StatedSU 4 (p ^ f) F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hz0sq
      simpa using this
    · intro h
      apply hz01
      exact Subtype.ext (Units.ext (by simpa using h))
  have hsplit : ∀ g ∈ P,
      SplitAt a b c d (((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro g hg
    refine splitAt_of_comm h2 hac had hbc hbd ?_
    have := congrArg
      (fun x : ↥(StatedSU 4 (p ^ f) F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) (hP g hg)
    simpa [hz0mat] using this
  conv_lhs => rw [← hperf]
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hgs := hsplit g hg
  have hhs := hsplit h hh
  have hgis := hsplit _ (P.inv_mem hg)
  have hhis := hsplit _ (P.inv_mem hh)
  have hQ : (((⁅g, h⁆ : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (g : GL (Fin 4) F) * (h : GL (Fin 4) F) * ((g⁻¹ : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) *
        ((h⁻¹ : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) := by
    rw [commutatorElement_def]
    simp [mul_assoc]
  set G : Matrix (Fin 4) (Fin 4) F :=
    (((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hG
  set Hm : Matrix (Fin 4) (Fin 4) F :=
    (((h : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hHm
  set Gi : Matrix (Fin 4) (Fin 4) F :=
    (((g⁻¹ : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hGi
  set Hi : Matrix (Fin 4) (Fin 4) F :=
    (((h⁻¹ : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hHi
  have hGGi : G * Gi = 1 := by
    have h1 : ((g : GL (Fin 4) F) * (g : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) = 1 := mul_inv_cancel _
    have h2' := congrArg Units.val h1
    rw [Units.val_mul, Units.val_one] at h2'
    exact h2'
  have hHHi : Hm * Hi = 1 := by
    have h1 : ((h : GL (Fin 4) F) * (h : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) = 1 := mul_inv_cancel _
    have h2' := congrArg Units.val h1
    rw [Units.val_mul, Units.val_one] at h2'
    exact h2'
  have hsGH : SplitAt a b c d (G * Hm) := SplitAt.mul hab hac had hbc hbd hcd hgs hhs
  have hsGHG : SplitAt a b c d (G * Hm * Gi) := SplitAt.mul hab hac had hbc hbd hcd hsGH hgis
  have hsK : SplitAt a b c d (G * Hm * Gi * Hi) := SplitAt.mul hab hac had hbc hbd hcd hsGHG hhis
  have hdet1 : ∀ X Y : Matrix (Fin 4) (Fin 4) F, SplitAt a b c d X → X * Y = 1 →
      (ablk a b X).det * (ablk a b Y).det = 1 := by
    intro X Y hX hXY
    have h1 := ablk_mul hab hac had hbc hbd hcd (N := Y) hX
    rw [hXY, ablk_one a b hab] at h1
    rw [← Matrix.det_mul, ← h1, Matrix.det_one]
  have hdG := hdet1 G Gi hgs hGGi
  have hdH := hdet1 Hm Hi hhs hHHi
  have hKab : (ablk a b (G * Hm * Gi * Hi)).det = 1 := by
    rw [ablk_mul hab hac had hbc hbd hcd hsGHG, ablk_mul hab hac had hbc hbd hcd hsGH,
      ablk_mul hab hac had hbc hbd hcd hgs]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    calc (ablk a b G).det * (ablk a b Hm).det * (ablk a b Gi).det * (ablk a b Hi).det
        = ((ablk a b G).det * (ablk a b Gi).det) * ((ablk a b Hm).det * (ablk a b Hi).det) := by
          ring
      _ = 1 := by rw [hdG, hdH, one_mul]
  have hKU := (unitary_of_mem_statedSU hF (⁅g, h⁆ : ↥(StatedSU 4 (p ^ f) F)))
  rw [hQ] at hKU
  obtain ⟨hdetK, hUK⟩ := hKU
  have hKcd : (ablk c d (G * Hm * Gi * Hi)).det = 1 := by
    have h1 := det_split hab hac had hbc hbd hcd hsK
    rw [hdetK, hKab, one_mul] at h1
    exact h1.symm
  have hUab := conjTr_mul_ablk hab hac had hbc hbd hcd (LieType.BorelTits.unitaryInvolution F p f)
    hsK hUK
  have hUcd := conjTr_mul_ablk' hab hac had hbc hbd hcd (LieType.BorelTits.unitaryInvolution F p f)
    hsK hUK
  have hKeq := split_eq_mul hab hac had hbc hbd hcd hsK
  let Aab : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (ablk a b (G * Hm * Gi * Hi)) (by rw [hKab]; exact one_ne_zero)
  let Acd : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (ablk c d (G * Hm * Gi * Hi)) (by rw [hKcd]; exact one_ne_zero)
  have hAab : Aab ∈ SUid (LieType.BorelTits.unitaryInvolution F p f) 2 := ⟨hKab, hUab⟩
  have hAcd : Acd ∈ SUid (LieType.BorelTits.unitaryInvolution F p f) 2 := ⟨hKcd, hUcd⟩
  have hgh : ⁅g, h⁆ = uniEmb hF hab ⟨Aab, hAab⟩ * uniEmb hF hcd ⟨Acd, hAcd⟩ := by
    apply Subtype.ext
    apply Units.ext
    rw [hQ]
    exact hKeq
  rw [hgh]
  refine (uniBlk F (p ^ f) a b ⊔ uniBlk F (p ^ f) c d).mul_mem
    (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
  · rw [← range_uniEmb hF hab]
    exact ⟨_, rfl⟩
  · rw [← range_uniEmb hF hcd]
    exact ⟨_, rfl⟩

end Uni

end Split

theorem neg_zblkMat_eq {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : -(zblkMat F c d) = zblkMat F a b := by
  ext i j
  simp only [Matrix.neg_apply, zblkMat, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rcases fin4_cover hab hac had hbc hbd hcd i with h | h | h | h <;> subst h <;>
      simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm,
        hcd.symm]
  · simp [hij]

theorem neg_mul_mem_lin [Finite F] (hF : Nat.card F % 4 = 3) (h2 : (2 : F) ≠ 0) {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {s : ↥(StatedSL 4 F)} (hs : s ∈ Subgroup.center ↥(StatedSL 4 F)) (hs1 : s ≠ 1)
    {z : ↥(StatedSL 4 F)} (hz : z ∈ blkLin (F := F) c d) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    s * z ∈ blkLin (F := F) a b := by
  have hzmat : (((z : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      zblkMat F c d := by
    refine eq_zblk_of_involution h2 hcd (fun i j hij => hz i j hij) ?_ ?_ ?_
    · have := congrArg
        (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hz2
      simpa using this
    · have h1 : ((z : ↥(StatedSL 4 F)) : GL (Fin 4) F) ∈ detOne F 4 := by
        rw [← statedSL_eq_detOne]
        exact z.2
      rw [mem_detOne] at h1
      exact h1
    · intro h
      apply hz1
      exact Subtype.ext (Units.ext (by simpa using h))
  have hsmat : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 := by
    rcases (mem_center_statedSL_four_iff hF s).1 hs with h | h
    · exact absurd (Subtype.ext h) hs1
    · rw [h, xGL_eq_neg_one]
      simp
  rw [mem_blkLin]
  have : (((s * z : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = zblkMat F a b := by
    rw [Subgroup.coe_mul, Units.val_mul, hsmat, hzmat, neg_mul, one_mul,
      neg_zblkMat_eq hab hac had hbc hbd hcd]
  intro i j hij
  rw [this, ← blkMat_neg_one_eq_zblk hab]
  exact idOut_blkMat _ i j hij

theorem neg_mul_mem_uni {p f : ℕ} [Finite F] [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) (h2 : (2 : F) ≠ 0) {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {s : ↥(StatedSU 4 (p ^ f) F)} (hs : s ∈ Subgroup.center ↥(StatedSU 4 (p ^ f) F)) (hs1 : s ≠ 1)
    {z : ↥(StatedSU 4 (p ^ f) F)} (hz : z ∈ uniBlk F (p ^ f) c d) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    s * z ∈ uniBlk F (p ^ f) a b := by
  have hzmat : (((z : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      zblkMat F c d := by
    refine eq_zblk_of_involution h2 hcd ((mem_uniBlk_iff hF).1 hz) ?_
      (unitary_of_mem_statedSU hF z).1 ?_
    · have := congrArg
        (fun x : ↥(StatedSU 4 (p ^ f) F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hz2
      simpa using this
    · intro h
      apply hz1
      exact Subtype.ext (Units.ext (by simpa using h))
  have hsmat : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 := by
    rcases (mem_center_statedSU_four_iff hF hq s).1 hs with h | h
    · exact absurd (Subtype.ext h) hs1
    · rw [h, xGL_eq_neg_one]
      simp
  rw [mem_uniBlk_iff hF]
  have : (((s * z : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      zblkMat F a b := by
    rw [Subgroup.coe_mul, Units.val_mul, hsmat, hzmat, neg_mul, one_mul,
      neg_zblkMat_eq hab hac had hbc hbd hcd]
  intro i j hij
  rw [this, ← blkMat_neg_one_eq_zblk hab]
  exact idOut_blkMat _ i j hij

structure PairFacts {S : Subgroup (GL (Fin 4) F)} (ops : BlockOps F S) : Prop where
  inf_bot : ∀ a b c d : Fin 4, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    ops.blk a b ⊓ ops.blk c d = ⊥
  perf_le : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ z0 ∈ ops.blk c d, z0 * z0 = 1 → z0 ≠ 1 → ∀ P : Subgroup ↥S,
      (∀ g ∈ P, g * z0 = z0 * g) → ⁅P, P⁆ = P → P ≤ ops.blk a b ⊔ ops.blk c d
  neg_mul : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ s ∈ Subgroup.center ↥S, s * s = 1 → s ≠ 1 → ∀ z ∈ ops.blk c d, z * z = 1 → z ≠ 1 →
      s * z ∈ ops.blk a b

theorem blkLin_inf_bot {a b c d : Fin 4} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    blkLin (F := F) a b ⊓ blkLin (F := F) c d = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨h1, h2⟩ := hg
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  by_cases hij : (i = a ∨ i = b) ∧ (j = a ∨ j = b)
  · have hn : ¬ ((i = c ∨ i = d) ∧ (j = c ∨ j = d)) := by
      rintro ⟨hi | hi, _⟩ <;> rcases hij.1 with h | h <;> subst hi <;> subst h <;> simp_all
    exact h2 i j hn
  · exact h1 i j hij

theorem uniBlk_inf_bot {q : ℕ} {a b c d : Fin 4} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) :
    uniBlk F q a b ⊓ uniBlk F q c d = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hg
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  by_cases hij : (i = a ∨ i = b) ∧ (j = a ∨ j = b)
  · have hn : ¬ ((i = c ∨ i = d) ∧ (j = c ∨ j = d)) := by
      rintro ⟨hi | hi, _⟩ <;> rcases hij.1 with h | h <;> subst hi <;> subst h <;> simp_all
    exact h2 i j hn
  · exact h1 i j hij

theorem linPairFacts [Finite F] (hF : Nat.card F % 4 = 3) (h4 : 3 < Nat.card F) :
    PairFacts (linBlockOps hF h4) where
  inf_bot a b c d _ _ hac had hbc hbd := blkLin_inf_bot hac had hbc hbd
  perf_le a b c d hab hac had hbc hbd hcd z0 hz0 hz0sq hz01 P hP hperf :=
    perfect_le_pair_lin (two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))) hab hac had hbc hbd
      hcd hz0 hz0sq hz01 P hP hperf
  neg_mul a b c d hab hac had hbc hbd hcd s hs _ hs1 z hz hz2 hz1 :=
    neg_mul_mem_lin hF (two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))) hab hac had hbc hbd hcd
      hs hs1 hz hz2 hz1

theorem uniPairFacts [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) :
    PairFacts (uniBlockOps hF hq) where
  inf_bot a b c d _ _ hac had hbc hbd := uniBlk_inf_bot hac had hbc hbd
  perf_le a b c d hab hac had hbc hbd hcd z0 hz0 hz0sq hz01 P hP hperf := by
    obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨h.prime⟩
    have : CharP F p := h.charP
    have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
    exact perfect_le_pair_uni hF (Ring.two_ne_zero hchar) hab hac had hbc hbd hcd hz0 hz0sq hz01 P
      hP hperf
  neg_mul a b c d hab hac had hbc hbd hcd s hs _ hs1 z hz hz2 hz1 := by
    obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨h.prime⟩
    have : CharP F p := h.charP
    have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
    exact neg_mul_mem_uni hF hq (Ring.two_ne_zero hchar) hab hac had hbc hbd hcd hs hs1 hz hz2 hz1

end CFSG.GH74.Generic.S1
