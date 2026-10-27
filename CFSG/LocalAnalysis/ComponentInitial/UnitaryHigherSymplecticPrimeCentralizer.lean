module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

section Matrix

variable {n : ℕ} {K : Type} [Field K]

theorem eq_scalar_of_commute_basic_unipotents (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (h1 : G * fromBlocks 1 1 0 1 = fromBlocks 1 1 0 1 * G)
    (hU : ∀ i, G * fromBlocks 1 (single i i 1) 0 1 = fromBlocks 1 (single i i 1) 0 1 * G)
    (hL : ∀ i, G * fromBlocks 1 0 (single i i 1) 1 = fromBlocks 1 0 (single i i 1) 1 * G)
    (hUU : ∀ i j, G * fromBlocks 1 (single i j 1 + single j i 1) 0 1 =
      fromBlocks 1 (single i j 1 + single j i 1) 0 1 * G) :
    ∃ d : K, G = Matrix.scalar (Fin n ⊕ Fin n) d := by
  rw [← fromBlocks_toBlocks G] at h1 hU hL hUU ⊢
  set P := G.toBlocks₁₁
  set Q := G.toBlocks₁₂
  set R := G.toBlocks₂₁
  set S := G.toBlocks₂₂
  have hU' : ∀ B : Matrix (Fin n) (Fin n) K,
      fromBlocks P Q R S * fromBlocks 1 B 0 1 = fromBlocks 1 B 0 1 * fromBlocks P Q R S →
        B * R = 0 ∧ P * B = B * S := by
    intro B h
    simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add] at h
    obtain ⟨h1, h2, -, -⟩ := Matrix.fromBlocks_inj.mp h
    refine ⟨?_, ?_⟩
    · have := congrArg (· - P) h1
      simpa using this.symm
    · have := congrArg (· - Q) h2
      simpa [add_comm] using this
  have hL' : ∀ C : Matrix (Fin n) (Fin n) K,
      fromBlocks P Q R S * fromBlocks 1 0 C 1 = fromBlocks 1 0 C 1 * fromBlocks P Q R S →
        Q * C = 0 ∧ S * C = C * P := by
    intro C h
    simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add] at h
    obtain ⟨h1, -, h3, -⟩ := Matrix.fromBlocks_inj.mp h
    refine ⟨?_, ?_⟩
    · have := congrArg (· - P) h1
      simpa using this
    · have := congrArg (· - R) h3
      simpa [add_comm] using this
  have hR : R = 0 := by
    ext i k
    have := congrFun (congrFun (hU' _ (hU i)).1 i) k
    simpa [Matrix.single_mul_apply_same] using this
  have hQ : Q = 0 := by
    ext k i
    have := congrFun (congrFun (hL' _ (hL i)).1 k) i
    simpa [Matrix.mul_single_apply_same] using this
  have hPS : P = S := by simpa using (hU' 1 h1).2
  have hdiag : ∀ i j : Fin n, i ≠ j → P i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun (hU' _ (hU j)).2 i) j
    rw [← hPS, Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij,
      mul_one] at h
    exact h
  have hconst : ∀ i j : Fin n, P i i = P j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have h := congrFun (congrFun (hU' _ (hUU i j)).2 i) j
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

end Matrix

variable {r : ℕ} {K : Type} [Field K]

variable (r K) in
@[expose] def primeFieldSp : Subgroup (GL (Fin r ⊕ Fin r) K) :=
  (StatedSp r (⊥ : Subfield K)).map (GeneralLinearGroup.map (⊥ : Subfield K).subtype)

theorem formJ_map_ringHom {k : Type} [Field k] (ι : k →+* K) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).map ι =
      fromBlocks 0 1 (-1) 0 := by
  rw [fromBlocks_map, Matrix.map_zero _ (map_zero ι), Matrix.map_neg _ (map_neg ι),
    Matrix.map_one _ (map_zero ι) (map_one ι)]

theorem map_mem_statedSp {k : Type} [Field k] (ι : k →+* K) {g : GL (Fin r ⊕ Fin r) k}
    (hg : g ∈ StatedSp r k) : GeneralLinearGroup.map ι g ∈ StatedSp r K :=
  CFSG.Open.StatedAPI.map_mem_statedSp ι hg

theorem primeFieldSp_le : primeFieldSp r K ≤ StatedSp r K := by
  rintro _ ⟨g, hg, rfl⟩
  exact map_mem_statedSp _ hg

theorem glFieldEquiv_primeFieldSp (σ : K ≃+* K) {g : GL (Fin r ⊕ Fin r) K}
    (hg : g ∈ primeFieldSp r K) : glFieldEquiv (Fin r ⊕ Fin r) σ g = g := by
  obtain ⟨g₀, -, rfl⟩ := hg
  refine GeneralLinearGroup.ext fun i j => ?_
  have hle : (⊥ : Subfield K) ≤ RingHom.eqLocusField σ.toRingHom (RingHom.id K) := bot_le
  exact hle ((g₀ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (⊥ : Subfield K)) i j).2

theorem exists_upper_mem_primeFieldSp {B : Matrix (Fin r) (Fin r) (⊥ : Subfield K)}
    (hB : Bᵀ = B) : ∃ g ∈ primeFieldSp r K, (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks 1 (B.map (⊥ : Subfield K).subtype) 0 1 := by
  refine ⟨_, Subgroup.mem_map_of_mem _ (SymplecticFlag.upperUnipotentSp r _ hB).2, ?_⟩
  change ((SymplecticFlag.upperUnipotentSp r _ hB : GL (Fin r ⊕ Fin r) (⊥ : Subfield K)) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (⊥ : Subfield K)).map (⊥ : Subfield K).subtype = _
  rw [SymplecticFlag.coe_upperUnipotentSp, fromBlocks_map,
    Matrix.map_one _ (map_zero (⊥ : Subfield K).subtype) (map_one (⊥ : Subfield K).subtype),
    Matrix.map_zero _ (map_zero (⊥ : Subfield K).subtype)]

theorem exists_lower_mem_primeFieldSp {C : Matrix (Fin r) (Fin r) (⊥ : Subfield K)}
    (hC : Cᵀ = C) : ∃ g ∈ primeFieldSp r K, (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks 1 0 (C.map (⊥ : Subfield K).subtype) 1 := by
  have hmem : ((CFSG.ClassicalGroups.Symplectic.lowerUnipotent hC :
      TauCeti.GLSymplectic (Fin r) (⊥ : Subfield K)) : GL (Fin r ⊕ Fin r) (⊥ : Subfield K)) ∈
        StatedSp r (⊥ : Subfield K) := by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact (CFSG.ClassicalGroups.Symplectic.lowerUnipotent hC).2
  refine ⟨_, Subgroup.mem_map_of_mem _ hmem, ?_⟩
  change (((CFSG.ClassicalGroups.Symplectic.lowerUnipotent hC :
    TauCeti.GLSymplectic (Fin r) (⊥ : Subfield K)) : GL (Fin r ⊕ Fin r) (⊥ : Subfield K)) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (⊥ : Subfield K)).map (⊥ : Subfield K).subtype = _
  rw [CFSG.ClassicalGroups.Symplectic.coe_lowerUnipotent, fromBlocks_map,
    Matrix.map_one _ (map_zero (⊥ : Subfield K).subtype) (map_one (⊥ : Subfield K).subtype),
    Matrix.map_zero _ (map_zero (⊥ : Subfield K).subtype)]

theorem centralizer_primeFieldSp :
    Subgroup.centralizer (primeFieldSp r K : Set (GL (Fin r ⊕ Fin r) K)) =
      StatedScalars (Fin r ⊕ Fin r) K := by
  apply le_antisymm
  · intro M hM
    have hcomm : ∀ g ∈ primeFieldSp r K, (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * M := by
      intro g hg
      have h1 := congrArg (fun x : GL (Fin r ⊕ Fin r) K =>
        (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) (Subgroup.mem_centralizer_iff.mp hM g hg)
      simpa only [Units.val_mul] using h1.symm
    have hU : ∀ B : Matrix (Fin r) (Fin r) (⊥ : Subfield K), Bᵀ = B →
        (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          fromBlocks 1 (B.map (⊥ : Subfield K).subtype) 0 1 =
            fromBlocks 1 (B.map (⊥ : Subfield K).subtype) 0 1 *
              (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      intro B hB
      obtain ⟨g, hg, hgB⟩ := exists_upper_mem_primeFieldSp hB
      rw [← hgB]
      exact hcomm g hg
    have hL : ∀ C : Matrix (Fin r) (Fin r) (⊥ : Subfield K), Cᵀ = C →
        (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          fromBlocks 1 0 (C.map (⊥ : Subfield K).subtype) 1 =
            fromBlocks 1 0 (C.map (⊥ : Subfield K).subtype) 1 *
              (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      intro C hC
      obtain ⟨g, hg, hgC⟩ := exists_lower_mem_primeFieldSp hC
      rw [← hgC]
      exact hcomm g hg
    have h1 : (1 : Matrix (Fin r) (Fin r) (⊥ : Subfield K)).map (⊥ : Subfield K).subtype = 1 :=
      Matrix.map_one _ (map_zero (⊥ : Subfield K).subtype) (map_one (⊥ : Subfield K).subtype)
    have hs : ∀ i j : Fin r,
        (single i j (1 : (⊥ : Subfield K))).map (⊥ : Subfield K).subtype = single i j 1 :=
      fun i j => by rw [Matrix.map_single, map_one]
    have hsym : ∀ i : Fin r, (single i i (1 : (⊥ : Subfield K)))ᵀ = single i i 1 := fun i => by
      rw [transpose_single]
    obtain ⟨d, hd⟩ := eq_scalar_of_commute_basic_unipotents
      (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      (by simpa only [h1] using hU 1 transpose_one)
      (fun i => by simpa only [hs] using hU _ (hsym i))
      (fun i => by simpa only [hs] using hL _ (hsym i))
      (fun i j => by
        have hB : (single i j (1 : (⊥ : Subfield K)) + single j i 1)ᵀ =
            single i j 1 + single j i 1 := by
          rw [transpose_add, transpose_single, transpose_single, add_comm]
        simpa only [Matrix.map_add _ (map_add (⊥ : Subfield K).subtype), hs] using hU _ hB)
    rw [StatedScalars, MonoidHom.mem_range]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      refine ⟨1, GeneralLinearGroup.ext fun a => ?_⟩
      rcases a with a | a <;> exact a.elim0
    · have hdet : IsUnit (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det :=
        Matrix.isUnit_det_of_invertible _
      rw [hd, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, isUnit_pow_iff
        (Finset.card_ne_zero.mpr ⟨Sum.inl ⟨0, hr⟩, Finset.mem_univ _⟩)] at hdet
      refine ⟨hdet.unit, GeneralLinearGroup.ext fun a b => ?_⟩
      rw [GeneralLinearGroup.coe_scalar, hd]
      rfl
  · intro M hM
    rw [StatedScalars, MonoidHom.mem_range] at hM
    obtain ⟨c, rfl⟩ := hM
    have hc : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈
        Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hc g

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
