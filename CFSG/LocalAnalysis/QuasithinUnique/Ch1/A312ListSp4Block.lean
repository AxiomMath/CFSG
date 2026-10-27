module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Blk

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

@[expose] def blkIdx (σ : Fin m → ι) (A : Matrix ι ι K) : Matrix (Fin m) (Fin m) K :=
  A.submatrix σ σ

omit [Fintype ι] in
theorem blkIdx_one {σ : Fin m → ι} (hσ : Function.Injective σ) :
    blkIdx σ (1 : Matrix ι ι K) = 1 :=
  Matrix.submatrix_one σ hσ

theorem blkIdx_mul {σ : Fin m → ι} (hσ : Function.Injective σ) (A B : Matrix ι ι K)
    (h : ∀ k, k ∉ Set.range σ → (∀ i, A (σ i) k = 0) ∨ (∀ j, B k (σ j) = 0)) :
    blkIdx σ (A * B) = blkIdx σ A * blkIdx σ B := by
  classical
  ext i j
  simp only [blkIdx, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image σ)) ?_,
    Finset.sum_image (fun a _ b _ hab => hσ hab)]
  intro k _ hk
  have hk' : k ∉ Set.range σ := fun ⟨l, hl⟩ => hk (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hl⟩)
  rcases h k hk' with h | h
  · rw [h i, zero_mul]
  · rw [h j, mul_zero]

end Blk

section Entries

variable {K : Type} [Field K]

abbrev spMat (g : StatedSp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem spMat_mul (g h : StatedSp 2 K) : spMat (g * h) = spMat g * spMat h := rfl

theorem spMat_one : spMat (1 : StatedSp 2 K) = 1 := rfl

theorem spMat_inr_inl_of_mem_Q2_one {g : StatedSp 2 K} (hg : g ∈ Q2 K 1) (i c : Fin 2) :
    spMat g (Sum.inr i) (Sum.inl c) = 0 := by
  have h1 : (Pi.single (Sum.inl c) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 2 := by
    rw [mem_flag_of_le (le_refl 2), mem_isoFlag]
    refine ⟨fun j => by simp, fun j hj => ?_⟩
    have : (j : ℕ) < 2 := j.isLt
    omega
  have h2 : spMat g *ᵥ (Pi.single (Sum.inl c) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 2 := by
    have hq : g ∈ stabilizer 2 K (flag 2 K 2) := hg
    have : spMat g *ᵥ (Pi.single (Sum.inl c) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈
        (flag 2 K 2).map (mulVecLin (spMat g)) := ⟨_, h1, rfl⟩
    rwa [mem_stabilizer.mp hq] at this
  rw [mem_flag_of_le (le_refl 2), mem_isoFlag] at h2
  have := h2.1 i
  simpa [Matrix.mulVec_single_one] using this

theorem spMat_col_zero_of_mem_Q2_zero {g : StatedSp 2 K} (hg : g ∈ Q2 K 0) (x : Fin 2 ⊕ Fin 2)
    (hx : x ≠ Sum.inl 0) : spMat g x (Sum.inl 0) = 0 := by
  have h1 : (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 1 := by
    rw [mem_flag_of_le (by norm_num), mem_isoFlag]
    refine ⟨fun j => by simp, fun j hj => ?_⟩
    have : j ≠ 0 := fun h => by subst h; simp at hj
    simp [this]
  have h2 : spMat g *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 1 := by
    have hq : g ∈ stabilizer 2 K (flag 2 K 1) := hg
    have : spMat g *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈
        (flag 2 K 1).map (mulVecLin (spMat g)) := ⟨_, h1, rfl⟩
    rwa [mem_stabilizer.mp hq] at this
  rw [mem_flag_of_le (by norm_num), mem_isoFlag] at h2
  rcases x with j | j
  · have hj : j ≠ 0 := fun h => hx (by rw [h])
    have h3 := h2.2 j (by
      have : j = 1 := by
        fin_cases j
        · exact absurd rfl hj
        · rfl
      rw [this]
      norm_num)
    simpa [Matrix.mulVec_single_one] using h3
  · have := h2.1 j
    simpa [Matrix.mulVec_single_one] using this

theorem spMat_key_of_mem_Q2_zero {g : StatedSp 2 K} (hg : g ∈ Q2 K 0) (c : Fin 2 ⊕ Fin 2) :
    spMat g (Sum.inl 0) (Sum.inl 0) * spMat g (Sum.inr 0) c =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) c := by
  have hs := congrFun₂ (mem_statedSp_iff.mp g.2) (Sum.inl 0) c
  have e1 : ∀ x : Fin 2 ⊕ Fin 2, x ≠ Sum.inl 0 → spMat g x (Sum.inl 0) = 0 :=
    spMat_col_zero_of_mem_Q2_zero hg
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.transpose_apply,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply] at hs
  have e2 := e1 (Sum.inl 1) (by simp)
  have e3 := e1 (Sum.inr 0) (by simp)
  have e4 := e1 (Sum.inr 1) (by simp)
  simp only [spMat] at e2 e3 e4 ⊢
  simp [e2, e3, e4] at hs
  simpa using hs

theorem spMat_inl_zero_ne_zero {g : StatedSp 2 K} (hg : g ∈ Q2 K 0) :
    spMat g (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
  intro h
  have := spMat_key_of_mem_Q2_zero hg (Sum.inr 0)
  rw [h, zero_mul] at this
  simp at this

theorem spMat_inr_zero_of_mem_Q2_zero {g : StatedSp 2 K} (hg : g ∈ Q2 K 0)
    {c : Fin 2 ⊕ Fin 2} (hc : c ≠ Sum.inr 0) : spMat g (Sum.inr 0) c = 0 := by
  have h := spMat_key_of_mem_Q2_zero hg c
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) c = 0 := by
    rcases c with j | j
    · simp
    · have : j ≠ 0 := fun h => hc (by rw [h])
      simp [Ne.symm this]
  rw [hJ] at h
  exact (mul_eq_zero.mp h).resolve_left (spMat_inl_zero_ne_zero hg)

end Entries

section Embeddings

variable {K : Type} [Field K]

@[expose] noncomputable def spLevi (j : Fin 2) :
    SpecialLinearGroup (Fin 2) K →* StatedSp 2 K :=
  if j = 0 then lam 1 else leviSp.comp Matrix.SpecialLinearGroup.toGL

theorem spMat_leviSp_one (A : SpecialLinearGroup (Fin 2) K) :
    spMat (spLevi 1 A) =
      fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0
        (((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))ᵀ := by
  have : (spLevi (K := K) 1) = leviSp.comp Matrix.SpecialLinearGroup.toGL := by
    simp [spLevi]
  rw [this]
  show (((leviSp (Matrix.SpecialLinearGroup.toGL A) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
  rw [coe_leviSp, ← map_inv]
  rfl

theorem spMat_lam (A : SpecialLinearGroup (Fin 2) K) :
    spMat (spLevi 0 A) =
      pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (A : Matrix (Fin 2) (Fin 2) K) := by
  have : (spLevi (K := K) 0) = lam 1 := by simp [spLevi]
  rw [this]
  rfl

theorem fin_two_cases (j : Fin 2) : j = 0 ∨ j = 1 := by
  fin_cases j <;> simp

theorem spLevi_mulVec_mem (j : Fin 2) (A : SpecialLinearGroup (Fin 2) K) {v : Fin 2 ⊕ Fin 2 → K}
    (hv : v ∈ flag 2 K ((j : ℕ) + 1)) : spMat (spLevi j A) *ᵥ v ∈ flag 2 K ((j : ℕ) + 1) := by
  rcases fin_two_cases j with rfl | rfl
  ·
    have hv' : v ∈ flag 2 K 1 := hv
    rw [mem_flag_of_le (by norm_num), mem_isoFlag] at hv'
    have hfix : spMat (spLevi 0 A) *ᵥ v = v := by
      rw [spMat_lam]
      ext x
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Sum.inl 0)]
      · rw [pairMat_apply_of_ne' (by simp) (by simp), Matrix.one_apply]
        by_cases hx : x = Sum.inl 0
        · rw [hx]
          simp
        · have hv0 : v x = 0 := by
            rcases x with j | j
            · have hj : j ≠ 0 := fun h => hx (by rw [h])
              exact hv'.2 j (by
                have : j = 1 := by
                  fin_cases j
                  · exact absurd rfl hj
                  · rfl
                rw [this]
                norm_num)
            · exact hv'.1 j
          rw [ite_eq_right hx, zero_mul, hv0]
      · intro y _ hy
        have hvy : v y = 0 := by
          rcases y with j | j
          · have hj : j ≠ 0 := fun h => hy (by rw [h])
            exact hv'.2 j (by
              have : j = 1 := by
                fin_cases j
                · exact absurd rfl hj
                · rfl
              rw [this]
              norm_num)
          · exact hv'.1 j
        rw [hvy, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hfix]
    exact hv
  ·
    have hv' : v ∈ flag 2 K 2 := hv
    rw [mem_flag_of_le (le_refl 2), mem_isoFlag] at hv'
    rw [show ((1 : Fin 2) : ℕ) + 1 = 2 from rfl, mem_flag_of_le (le_refl 2), mem_isoFlag]
    have hvr : (v ∘ Sum.inr : Fin 2 → K) = 0 := funext fun i => hv'.1 i
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · rw [spMat_leviSp_one, fromBlocks_mulVec]
      simp [hvr]
    · have : (i : ℕ) < 2 := i.isLt
      omega

theorem spLevi_mem (j : Fin 2) (A : SpecialLinearGroup (Fin 2) K) : spLevi j A ∈ Q2 K j := by
  refine mem_stabilizer_of_mulVec_mem (fun v hv => spLevi_mulVec_mem j A hv) fun v hv => ?_
  rw [← map_inv]
  exact spLevi_mulVec_mem j A⁻¹ hv

end Embeddings

section Blocks

variable {K : Type} [Field K]

@[expose] noncomputable def blkSp (H : Subgroup (StatedSp 2 K)) {m : ℕ}
    (σ : Fin m → Fin 2 ⊕ Fin 2) (hσ : Function.Injective σ)
    (h : ∀ g ∈ H, ∀ g' ∈ H, ∀ k, k ∉ Set.range σ →
      (∀ i, spMat g (σ i) k = 0) ∨ (∀ j, spMat g' k (σ j) = 0)) :
    ↥H →* Matrix (Fin m) (Fin m) K where
  toFun g := blkIdx σ (spMat g.1)
  map_one' := blkIdx_one hσ
  map_mul' g g' := blkIdx_mul hσ _ _ (h g.1 g.2 g'.1 g'.2)

theorem blkSp_apply (H : Subgroup (StatedSp 2 K)) {m : ℕ} (σ : Fin m → Fin 2 ⊕ Fin 2)
    (hσ : Function.Injective σ)
    (h : ∀ g ∈ H, ∀ g' ∈ H, ∀ k, k ∉ Set.range σ →
      (∀ i, spMat g (σ i) k = 0) ∨ (∀ j, spMat g' k (σ j) = 0)) (g : ↥H) :
    blkSp H σ hσ h g = blkIdx σ (spMat g.1) := rfl

theorem det_blkSp_eq_one (H : Subgroup (StatedSp 2 K)) {m : ℕ} (σ : Fin m → Fin 2 ⊕ Fin 2)
    (hσ : Function.Injective σ)
    (h : ∀ g ∈ H, ∀ g' ∈ H, ∀ k, k ∉ Set.range σ →
      (∀ i, spMat g (σ i) k = 0) ∨ (∀ j, spMat g' k (σ j) = 0))
    {N : Subgroup (StatedSp 2 K)} (hNH : N ≤ H) (hN : Group.IsPerfect ↥N) (g : ↥N) :
    (blkSp H σ hσ h (Subgroup.inclusion hNH g)).det = 1 := by
  let φ : ↥N →* K :=
    (Matrix.detMonoidHom).comp ((blkSp H σ hσ h).comp (Subgroup.inclusion hNH))
  have hker : (φ.toHomUnits).ker = ⊤ := by
    rw [eq_top_iff, ← hN.commutator_eq_top]
    exact Abelianization.commutator_subset_ker _
  have hg : φ.toHomUnits g = 1 := by
    have : g ∈ (φ.toHomUnits).ker := by rw [hker]; exact Subgroup.mem_top g
    exact this
  have := congrArg Units.val hg
  simpa [φ] using this

@[expose] def sigma2 (j : Fin 2) : Fin 2 → Fin 2 ⊕ Fin 2 :=
  if j = 0 then ![Sum.inl 1, Sum.inr 1] else ![Sum.inl 0, Sum.inl 1]

theorem sigma2_injective (j : Fin 2) : Function.Injective (sigma2 j) := by
  rcases fin_two_cases j with rfl | rfl
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [sigma2]
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [sigma2]

theorem sigma2_cond (j : Fin 2) {g g' : StatedSp 2 K} (hg : g ∈ Q2 K j) (hg' : g' ∈ Q2 K j) :
    ∀ k, k ∉ Set.range (sigma2 j) →
      (∀ i, spMat g (sigma2 j i) k = 0) ∨ (∀ i, spMat g' k (sigma2 j i) = 0) := by
  intro k hk
  rcases fin_two_cases j with rfl | rfl
  · rcases k with k | k
    · rcases fin_two_cases k with rfl | rfl
      · left
        intro i
        fin_cases i
        · exact spMat_col_zero_of_mem_Q2_zero hg (Sum.inl 1) (by simp)
        · exact spMat_col_zero_of_mem_Q2_zero hg (Sum.inr 1) (by simp)
      · exact absurd ⟨0, by simp [sigma2]⟩ hk
    · rcases fin_two_cases k with rfl | rfl
      · right
        intro i
        fin_cases i
        · exact spMat_inr_zero_of_mem_Q2_zero hg' (by simp [sigma2])
        · exact spMat_inr_zero_of_mem_Q2_zero hg' (by simp [sigma2])
      · exact absurd ⟨1, by simp [sigma2]⟩ hk
  · rcases k with k | k
    · exact absurd ⟨k, by fin_cases k <;> simp [sigma2]⟩ hk
    · right
      intro i
      fin_cases i
      · exact spMat_inr_inl_of_mem_Q2_one hg' k 0
      · exact spMat_inr_inl_of_mem_Q2_one hg' k 1

@[expose] noncomputable def blkQ (j : Fin 2) : ↥(Q2 K j) →* Matrix (Fin 2) (Fin 2) K :=
  blkSp (Q2 K j) (sigma2 j) (sigma2_injective j) fun _ hg _ hg' => sigma2_cond j hg hg'

theorem blkQ_apply (j : Fin 2) (g : ↥(Q2 K j)) :
    blkQ j g = blkIdx (sigma2 j) (spMat g.1) := rfl

section FiniteBlocks

variable [Finite K]

theorem perfect_perfectCore_Q2 (j : Fin 2) : Group.IsPerfect ↥(perfectCore (Q2 K j)) :=
  Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)

@[expose] noncomputable def blkN (j : Fin 2) :
    ↥(perfectCore (Q2 K j)) →* SpecialLinearGroup (Fin 2) K where
  toFun x := ⟨blkQ j (Subgroup.inclusion (perfectCore_le (Q2 K j)) x),
    det_blkSp_eq_one _ _ _ _ (perfectCore_le (Q2 K j)) (perfect_perfectCore_Q2 j) x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by
    show blkQ j (Subgroup.inclusion (perfectCore_le (Q2 K j)) (g * g')) =
      blkQ j (Subgroup.inclusion (perfectCore_le (Q2 K j)) g) *
        blkQ j (Subgroup.inclusion (perfectCore_le (Q2 K j)) g')
    rw [map_mul, map_mul])

theorem blkN_coe (j : Fin 2) (x : ↥(perfectCore (Q2 K j))) :
    ((blkN j x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blkIdx (sigma2 j) (spMat x.1) := rfl

omit [Finite K] in
theorem blkIdx_spLevi (j : Fin 2) (A : SpecialLinearGroup (Fin 2) K) :
    blkIdx (sigma2 j) (spMat (spLevi j A)) = (A : Matrix (Fin 2) (Fin 2) K) := by
  rcases fin_two_cases j with rfl | rfl
  · rw [spMat_lam]
    obtain ⟨h1, h2, h3, h4⟩ := pairMat_apply_pair (a := (Sum.inl 1 : Fin 2 ⊕ Fin 2))
      (b := Sum.inr 1) Sum.inl_ne_inr (A : Matrix (Fin 2) (Fin 2) K)
    ext i k
    fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, h1, h2, h3, h4]
  · rw [spMat_leviSp_one]
    ext i k
    simp [blkIdx, sigma2]
    fin_cases i <;> fin_cases k <;> simp

omit [Finite K] in
theorem spLevi_range_perfect (hK : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    ⁅(spLevi (K := K) j).range, (spLevi (K := K) j).range⁆ = (spLevi (K := K) j).range := by
  have h : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    Group.isPerfect_def.mp (CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK)
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

omit [Finite K] in
theorem spLevi_mem_perfectCore (hK : ∃ s : Finset K, s.card = 4) (j : Fin 2)
    (A : SpecialLinearGroup (Fin 2) K) : spLevi j A ∈ perfectCore (Q2 K j) :=
  le_perfectCore_of_perfect (K := (spLevi (K := K) j).range) (H := Q2 K j)
    (by rintro _ ⟨B, rfl⟩; exact spLevi_mem j B) (spLevi_range_perfect hK j) ⟨A, rfl⟩

theorem blkN_spLevi (hK : ∃ s : Finset K, s.card = 4) (j : Fin 2)
    (A : SpecialLinearGroup (Fin 2) K) :
    blkN j ⟨spLevi j A, spLevi_mem_perfectCore hK j A⟩ = A :=
  Subtype.ext (blkIdx_spLevi j A)

theorem blkN_surjective (hK : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    Function.Surjective (blkN (K := K) j) :=
  fun A => ⟨⟨spLevi j A, spLevi_mem_perfectCore hK j A⟩, blkN_spLevi hK j A⟩

theorem spMat_inl_zero_eq_one_of_perfectCore {x : StatedSp 2 K} (hx : x ∈ perfectCore (Q2 K 0)) :
    spMat x (Sum.inl 0) (Sum.inl 0) = 1 := by
  let σ : Fin 1 → Fin 2 ⊕ Fin 2 := fun _ => Sum.inl 0
  have hσ : Function.Injective σ := fun a b _ => Subsingleton.elim a b
  have hcond : ∀ g ∈ Q2 K 0, ∀ g' ∈ Q2 K 0, ∀ k, k ∉ Set.range σ →
      (∀ i, spMat g (σ i) k = 0) ∨ (∀ i, spMat g' k (σ i) = 0) := by
    intro g hg g' hg' k hk
    right
    intro i
    exact spMat_col_zero_of_mem_Q2_zero hg' k (fun h => hk ⟨0, h.symm⟩)
  have h := det_blkSp_eq_one (Q2 K 0) σ hσ hcond (N := perfectCore (Q2 K 0))
    (perfectCore_le _) (perfect_perfectCore_Q2 0) ⟨x, hx⟩
  rw [Matrix.det_unique] at h
  exact h

theorem blkN_ker (j : Fin 2) (x : ↥(perfectCore (Q2 K j))) (hx : blkN j x = 1) :
    (x : StatedSp 2 K) ∈ unipotent 2 K := by
  have hblk : ∀ i k : Fin 2, spMat x.1 (sigma2 j i) (sigma2 j k) = (1 : Matrix (Fin 2) (Fin 2) K) i k := by
    intro i k
    have := congrFun₂ (congrArg Subtype.val hx) i k
    exact this
  rcases fin_two_cases j with rfl | rfl
  · have hxQ : (x : StatedSp 2 K) ∈ Q2 K 0 := perfectCore_le _ x.2
    have hlam := spMat_inl_zero_eq_one_of_perfectCore x.2
    have e00 : spMat x.1 (Sum.inl 1) (Sum.inl 1) = 1 := by simpa [sigma2] using hblk 0 0
    have e10 : spMat x.1 (Sum.inr 1) (Sum.inl 1) = 0 := by simpa [sigma2] using hblk 1 0
    have h21 : (spMat x.1).toBlocks₂₁ = 0 := by
      ext i k
      show spMat x.1 (Sum.inr i) (Sum.inl k) = 0
      fin_cases i <;> fin_cases k
      · exact spMat_col_zero_of_mem_Q2_zero hxQ (Sum.inr 0) (by simp)
      · exact spMat_inr_zero_of_mem_Q2_zero hxQ (by simp)
      · exact spMat_col_zero_of_mem_Q2_zero hxQ (Sum.inr 1) (by simp)
      · exact e10
    obtain ⟨-, C, hC, hM⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
    refine ⟨(spMat x.1).toBlocks₁₁, C, ⟨?_, ?_⟩, hC, hM⟩
    · intro i k hik
      fin_cases i <;> fin_cases k <;> simp at hik ⊢
      exact spMat_col_zero_of_mem_Q2_zero hxQ (Sum.inl 1) (by simp)
    · intro i
      fin_cases i
      · exact hlam
      · exact e00
  · have hxQ : (x : StatedSp 2 K) ∈ Q2 K 1 := perfectCore_le _ x.2
    have h21 : (spMat x.1).toBlocks₂₁ = 0 := by
      ext i k
      exact spMat_inr_inl_of_mem_Q2_one hxQ i k
    obtain ⟨-, C, hC, hM⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
    have h11 : (spMat x.1).toBlocks₁₁ = 1 := by
      ext i k
      have := hblk i k
      fin_cases i <;> fin_cases k <;> simpa [sigma2, Matrix.toBlocks₁₁] using this
    exact ⟨1, C, isUnitriangular_one, hC, by rw [← h11]; exact hM⟩

end FiniteBlocks

end Blocks

end CFSG.QuasithinUnique.Vol2Native.A312L
