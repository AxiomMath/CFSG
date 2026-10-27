module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ClassicalGroups.Symplectic

open Matrix CFSG.Assembly.LowTwoRank

variable {n : ℕ} {K : Type} [Field K]

theorem blueprintGram_eq_neg_J :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = -J (Fin n) K := by
  simp [J, fromBlocks_neg]

theorem blueprintGram_iff_mem_symplecticGroup (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Aᵀ * fromBlocks 0 1 (-1) 0 * A = fromBlocks 0 1 (-1) 0 ↔
      A ∈ symplecticGroup (Fin n) K := by
  rw [blueprintGram_eq_neg_J, SymplecticGroup.mem_iff', Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem statedSp_eq_GLSymplectic : StatedSp n K = TauCeti.GLSymplectic (Fin n) K := by
  apply le_antisymm
  · rw [StatedSp, Subgroup.closure_le]
    intro A hA
    exact TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mpr
      ((blueprintGram_iff_mem_symplecticGroup _).mp hA)
  · intro A hA
    exact Subgroup.subset_closure ((blueprintGram_iff_mem_symplecticGroup _).mpr
      (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp hA))

private theorem scalar_mul_mul_scalar_transpose (c : K)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Matrix.scalar (Fin n ⊕ Fin n) c * M * (Matrix.scalar (Fin n ⊕ Fin n) c)ᵀ = (c ^ 2) • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
    smul_smul, pow_two]

theorem scalar_mem_symplecticGroup_iff (hn : 1 ≤ n) (c : K) :
    Matrix.scalar (Fin n ⊕ Fin n) c ∈ symplecticGroup (Fin n) K ↔ c ^ 2 = 1 := by
  rw [SymplecticGroup.mem_iff, scalar_mul_mul_scalar_transpose]
  have hJ : J (Fin n) K (Sum.inr ⟨0, hn⟩) (Sum.inl ⟨0, hn⟩) = 1 := by simp [J]
  constructor
  · intro h
    have := congrFun (congrFun h (Sum.inr ⟨0, hn⟩)) (Sum.inl ⟨0, hn⟩)
    simpa [hJ] using this
  · intro h
    rw [h, one_smul]

noncomputable def upperUnipotent {B : Matrix (Fin n) (Fin n) K} (hB : Bᵀ = B) :
    TauCeti.GLSymplectic (Fin n) K :=
  ⟨TauCeti.GLSymplectic.ofSymplecticGroup (Fin n) K
    ⟨fromBlocks 1 B 0 1, SymplecticGroup.fromBlocks_upper_mem hB⟩,
    TauCeti.GLSymplectic.ofSymplecticGroup_mem _ _ _⟩

noncomputable def lowerUnipotent {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = C) :
    TauCeti.GLSymplectic (Fin n) K :=
  ⟨TauCeti.GLSymplectic.ofSymplecticGroup (Fin n) K
    ⟨fromBlocks 1 0 C 1, SymplecticGroup.fromBlocks_lower_mem hC⟩,
    TauCeti.GLSymplectic.ofSymplecticGroup_mem _ _ _⟩

@[simp] theorem coe_upperUnipotent {B : Matrix (Fin n) (Fin n) K} (hB : Bᵀ = B) :
    (((upperUnipotent hB : TauCeti.GLSymplectic (Fin n) K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = fromBlocks 1 B 0 1 :=
  TauCeti.GLSymplectic.coe_ofSymplecticGroup _ _ _

@[simp] theorem coe_lowerUnipotent {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = C) :
    (((lowerUnipotent hC : TauCeti.GLSymplectic (Fin n) K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = fromBlocks 1 0 C 1 :=
  TauCeti.GLSymplectic.coe_ofSymplecticGroup _ _ _

theorem eq_scalar_of_commute_unipotents (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (hU : ∀ B : Matrix (Fin n) (Fin n) K, Bᵀ = B → G * fromBlocks 1 B 0 1 = fromBlocks 1 B 0 1 * G)
    (hL : ∀ C : Matrix (Fin n) (Fin n) K, Cᵀ = C → G * fromBlocks 1 0 C 1 = fromBlocks 1 0 C 1 * G) :
    ∃ d : K, G = Matrix.scalar (Fin n ⊕ Fin n) d := by
  classical
  rw [← fromBlocks_toBlocks G] at hU hL ⊢
  set P := G.toBlocks₁₁
  set Q := G.toBlocks₁₂
  set R := G.toBlocks₂₁
  set S := G.toBlocks₂₂
  have hU' : ∀ B : Matrix (Fin n) (Fin n) K, Bᵀ = B → B * R = 0 ∧ P * B = B * S := by
    intro B hB
    have h := hU B hB
    simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add] at h
    obtain ⟨h1, h2, -, -⟩ := Matrix.fromBlocks_inj.mp h
    refine ⟨?_, ?_⟩
    · have := congrArg (· - P) h1
      simpa using this.symm
    · have := congrArg (· - Q) h2
      simpa [add_comm] using this
  have hL' : ∀ C : Matrix (Fin n) (Fin n) K, Cᵀ = C → Q * C = 0 ∧ S * C = C * P := by
    intro C hC
    have h := hL C hC
    simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add] at h
    obtain ⟨h1, -, h3, -⟩ := Matrix.fromBlocks_inj.mp h
    refine ⟨?_, ?_⟩
    · have := congrArg (· - P) h1
      simpa using this
    · have := congrArg (· - R) h3
      simpa [add_comm] using this
  have hsym : ∀ i : Fin n, (Matrix.single i i (1 : K))ᵀ = Matrix.single i i 1 := by
    intro i; simp [Matrix.transpose_single]
  have hR : R = 0 := by
    ext i k
    have := congrFun (congrFun (hU' _ (hsym i)).1 i) k
    simpa [Matrix.single_mul_apply_same] using this
  have hQ : Q = 0 := by
    ext k i
    have := congrFun (congrFun (hL' _ (hsym i)).1 k) i
    simpa [Matrix.mul_single_apply_same] using this
  have hPS : P = S := by simpa using (hU' 1 Matrix.transpose_one).2
  have hdiag : ∀ i j : Fin n, i ≠ j → P i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun (hU' _ (hsym j)).2 i) j
    rw [← hPS, Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij,
      mul_one] at h
    exact h
  have hconst : ∀ i j : Fin n, P i i = P j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have hB : (Matrix.single i j (1 : K) + Matrix.single j i 1)ᵀ =
        Matrix.single i j 1 + Matrix.single j i 1 := by
      rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single, add_comm]
    have h := congrFun (congrFun (hU' _ hB).2 i) j
    rw [← hPS, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.add_apply,
      Matrix.mul_single_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ (fun h => hij h.symm),
      Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij] at h
    simpa using h
  have hscalar : ∀ i₀ : Fin n, P = Matrix.scalar (Fin n) (P i₀ i₀) := by
    intro i₀
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, hconst a i₀]
    · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hab, hdiag a b hab]
  rw [hR, hQ, ← hPS]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, ?_⟩
    ext a
    rcases a with a | a <;> exact a.elim0
  · obtain ⟨d, hdP⟩ : ∃ d, P = Matrix.scalar (Fin n) d := ⟨_, hscalar ⟨0, hn⟩⟩
    refine ⟨d, ?_⟩
    rw [hdP, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.fromBlocks_diagonal]
    congr 1
    ext a
    rcases a with a | a <;> rfl

theorem center_GLSymplectic_eq :
    Subgroup.center (TauCeti.GLSymplectic (Fin n) K) =
      (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (TauCeti.GLSymplectic (Fin n) K) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    have hcomm : ∀ h : TauCeti.GLSymplectic (Fin n) K,
        ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
            ((h : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
          ((h : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
            ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
      intro h
      have h1 := Subgroup.mem_center_iff.mp hg h
      have h2 := congrArg (fun x : TauCeti.GLSymplectic (Fin n) K =>
        ((x : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h1
      simpa only [Subgroup.coe_mul, Units.val_mul] using h2.symm
    obtain ⟨d, hd⟩ := eq_scalar_of_commute_unipotents _
      (fun B hB => by simpa only [coe_upperUnipotent] using hcomm (upperUnipotent hB))
      (fun C hC => by simpa only [coe_lowerUnipotent] using hcomm (lowerUnipotent hC))
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨1, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro a
      rcases a with a | a <;> exact a.elim0
    · have hdet : IsUnit (((g : GL (Fin n ⊕ Fin n) K) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).det) :=
        Matrix.isUnit_det_of_invertible _
      rw [hd, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, isUnit_pow_iff
        (Finset.card_ne_zero.mpr ⟨Sum.inl ⟨0, hn⟩, Finset.mem_univ _⟩)] at hdet
      refine ⟨hdet.unit, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro a b
      rw [Matrix.GeneralLinearGroup.coe_scalar, hd]
      rfl
  · intro g hg
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
    obtain ⟨c, hc⟩ := hg
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    simp only [Subgroup.coe_mul, Units.val_mul, ← hc, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem statedScalars_subgroupOf_statedSp :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) =
      (Subgroup.center (TauCeti.GLSymplectic (Fin n) K)).comap
        (Subgroup.inclusion (statedSp_eq_GLSymplectic (n := n) (K := K)).le) := by
  rw [center_GLSymplectic_eq]
  ext g
  simp [Subgroup.mem_subgroupOf]

end CFSG.ClassicalGroups.Symplectic
