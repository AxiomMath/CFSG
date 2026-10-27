module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

theorem eq_one_of_isPerfect_of_comm {G A : Type*} [Group G] [Group.IsPerfect G] [CommGroup A]
    (f : G →* A) (g : G) : f g = 1 := by
  have hg : g ∈ commutator G := Group.IsPerfect.mem_commutator
  have hmap : (commutator G).map f ≤ ⊥ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.commutator_le]
    intro a _ b _
    exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (mul_comm a b))
  exact Subgroup.mem_bot.1 (hmap ⟨g, hg, rfl⟩)

theorem exists_fixed_perfect_even_of_hom {G : Type*} [Group G] [Group.IsPerfect G]
    (ρ : G →* GL (Fin n) K) (α : MulAut (projectiveSL n K))
    (hfix : ∀ (g : G) (hg : (ρ g : Matrix (Fin n) (Fin n) K).det = 1),
      α (proj n K ⟨ρ g, hg⟩) = proj n K ⟨ρ g, hg⟩)
    (x : G) (hx4 : x ^ 4 = 1)
    (hxs : ∀ c : K, (ρ x : Matrix (Fin n) (Fin n) K) ≠ scalar (Fin n) c) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, α s = s := by
  have hdet : ∀ g, (ρ g : Matrix (Fin n) (Fin n) K).det = 1 := fun g => by
    have h := eq_one_of_isPerfect_of_comm (GeneralLinearGroup.det.comp ρ) g
    have := congrArg Units.val h
    simpa using this
  let ρ' : G →* SpecialLinearGroup (Fin n) K :=
    { toFun := fun g => ⟨ρ g, hdet g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by
        change ((ρ (g * h) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (ρ g : Matrix (Fin n) (Fin n) K) * (ρ h : Matrix (Fin n) (Fin n) K)
        rw [map_mul, Units.val_mul]) }
  set θ := (proj n K).comp ρ' with hθ
  refine ⟨θ.range, Group.IsPerfect.range θ, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hne : θ x ≠ 1 := by
      intro h1
      obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h1)
      exact hxs c hc
    have h4 : θ x ^ 4 = 1 := by rw [← map_pow, hx4, map_one]
    have hdvd : orderOf (θ x) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have h2 : 2 ∣ orderOf (θ x) := by
      have hpos : orderOf (θ x) ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
      rcases (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf (θ x) ∣ 2 ^ 2 from hdvd) with
        ⟨k, hk, hk'⟩
      interval_cases k
      · exact absurd (by rw [hk']; rfl) hpos
      · rw [hk']; exact ⟨1, rfl⟩
      · rw [hk']; exact ⟨2, rfl⟩
    have hord : orderOf (⟨θ x, ⟨x, rfl⟩⟩ : θ.range) = orderOf (θ x) :=
      Subgroup.orderOf_mk _ _
    exact even_iff_two_dvd.2 (h2.trans (hord ▸ orderOf_dvd_natCard _))
  · rintro _ ⟨g, rfl⟩
    exact hfix g (hdet g)

theorem exists_fixed_perfect_even_conj {S : Type*} [Group S] {α β γ : MulAut S}
    (hαβ : α = γ * β * γ⁻¹)
    (h : ∃ P : Subgroup S, Group.IsPerfect P ∧ Even (Nat.card P) ∧ ∀ s ∈ P, β s = s) :
    ∃ P : Subgroup S, Group.IsPerfect P ∧ Even (Nat.card P) ∧ ∀ s ∈ P, α s = s := by
  obtain ⟨P, hP, he, hfix⟩ := h
  refine ⟨P.map γ.toMonoidHom, Group.IsPerfect.map γ.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective γ.injective]
    exact he
  · rintro _ ⟨s, hs, rfl⟩
    rw [hαβ, MulAut.mul_apply, MulAut.mul_apply]
    change γ (β (γ⁻¹ (γ s))) = γ s
    rw [MulAut.inv_apply_self, hfix s hs]

variable {k m : ℕ}

variable (K k m) in
@[expose] def blockMonoidHom :
    Matrix (Fin k) (Fin k) K →* Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) K where
  toFun X := fromBlocks X 0 0 1
  map_one' := fromBlocks_one
  map_mul' X Y := by rw [fromBlocks_multiply]; simp

variable (K k m) in
@[expose] noncomputable def blockGL : GL (Fin k) K →* GL (Fin (k + m)) K :=
  (Units.map (MonoidHom.ofClass (reindexAlgEquiv K K finSumFinEquiv))).comp
    (Units.map (blockMonoidHom K k m))

theorem coe_blockGL (X : GL (Fin k) K) :
    (blockGL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K) =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks (X : Matrix (Fin k) (Fin k) K) 0 0 (1 : Matrix (Fin m) (Fin m) K)) :=
  rfl

theorem blockGL_apply_inl (X : GL (Fin k) K) (i j : Fin k) :
    (blockGL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K)
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) =
        (X : Matrix (Fin k) (Fin k) K) i j := by
  rw [coe_blockGL, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, fromBlocks_apply₁₁]

theorem blockGL_apply_inr (X : GL (Fin k) K) (i j : Fin m) :
    (blockGL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K)
      (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) =
        (1 : Matrix (Fin m) (Fin m) K) i j := by
  rw [coe_blockGL, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, fromBlocks_apply₂₂]

theorem scalar_apply_finSumFinEquiv {k m : ℕ} (c : K) (a b : Fin k ⊕ Fin m) :
    (scalar (Fin (k + m)) c) (finSumFinEquiv a) (finSumFinEquiv b) =
      if a = b then c else 0 := by
  rw [scalar_apply, diagonal_apply]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, finSumFinEquiv.injective.ne h]

theorem blockGL_ne_scalar_of_ne_scalar {X : GL (Fin k) K}
    (hX : ∀ c : K, (X : Matrix (Fin k) (Fin k) K) ≠ scalar (Fin k) c) (c : K) :
    (blockGL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K) ≠ scalar (Fin (k + m)) c := by
  intro h
  apply hX c
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) (finSumFinEquiv (Sum.inl j))
  rw [blockGL_apply_inl, scalar_apply_finSumFinEquiv] at this
  rw [this, scalar_apply, diagonal_apply]
  simp

theorem blockGL_ne_scalar_of_ne_one (hm : 1 ≤ m) {X : GL (Fin k) K} (hX : X ≠ 1) (c : K) :
    (blockGL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K) ≠ scalar (Fin (k + m)) c := by
  intro h
  have h0 := congrFun (congrFun h (finSumFinEquiv (Sum.inr ⟨0, by omega⟩)))
    (finSumFinEquiv (Sum.inr ⟨0, by omega⟩))
  rw [blockGL_apply_inr, scalar_apply_finSumFinEquiv, one_apply_eq] at h0
  simp only [ite_true] at h0
  apply hX
  apply Units.ext
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) (finSumFinEquiv (Sum.inl j))
  rw [blockGL_apply_inl, scalar_apply_finSumFinEquiv] at this
  rw [this, Units.val_one, one_apply, ← h0]
  simp

theorem blockGL_mul_diagonal_comm (X : GL (Fin k) K) {d : Fin (k + m) → K}
    (hd : ∀ i j : Fin k, d (finSumFinEquiv (Sum.inl i)) = d (finSumFinEquiv (Sum.inl j))) :
    (blockGL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K) * diagonal d =
      diagonal d * (blockGL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K) := by
  ext a b
  rw [mul_diagonal, diagonal_mul]
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  rw [coe_blockGL, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases a with i | i <;> rcases b with j | j
  · rw [fromBlocks_apply₁₁, hd i j, mul_comm]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, mul_zero]
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul, mul_zero]
  · rw [fromBlocks_apply₂₂]
    by_cases hij : i = j
    · subst hij
      rw [mul_comm]
    · rw [one_apply_ne hij, zero_mul, mul_zero]

theorem exists_gl_inv_mul_mul_eq_toMatrix (b : Basis (Fin n) K (Fin n → K)) (A : GL (Fin n) K) :
    ∃ P D : GL (Fin n) K, P⁻¹ * A * P = D ∧
      (D : Matrix (Fin n) (Fin n) K) =
        LinearMap.toMatrix b b (toLin' (A : Matrix (Fin n) (Fin n) K)) := by
  set P : GL (Fin n) K := ⟨(Pi.basisFun K (Fin n)).toMatrix b, b.toMatrix (Pi.basisFun K (Fin n)),
    Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _⟩ with hP
  refine ⟨P, P⁻¹ * A * P, rfl, ?_⟩
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b (Pi.basisFun K (Fin n)) b
    (Pi.basisFun K (Fin n)) (toLin' (A : Matrix (Fin n) (Fin n) K))
  rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h
  rw [← h, Units.val_mul, Units.val_mul]
  rfl

theorem det_blockGL (X : GL (Fin k) K) :
    (blockGL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K).det =
      (X : Matrix (Fin k) (Fin k) K).det := by
  rw [coe_blockGL, det_reindex_self, det_fromBlocks_zero₁₂, det_one, mul_one]

variable (K k m) in
@[expose] noncomputable def blockSL :
    SpecialLinearGroup (Fin k) K →* SpecialLinearGroup (Fin (k + m)) K where
  toFun X := ⟨blockGL K k m (SpecialLinearGroup.toGL X), by
    rw [det_blockGL, SpecialLinearGroup.coe_GL_coe_matrix, X.2]⟩
  map_one' := Subtype.ext (by
    change ((blockGL K k m (SpecialLinearGroup.toGL 1) : GL (Fin (k + m)) K) :
      Matrix (Fin (k + m)) (Fin (k + m)) K) = 1
    rw [map_one, map_one, Units.val_one])
  map_mul' X Y := Subtype.ext (by
    change ((blockGL K k m (SpecialLinearGroup.toGL (X * Y)) : GL (Fin (k + m)) K) :
      Matrix (Fin (k + m)) (Fin (k + m)) K) =
      (blockGL K k m (SpecialLinearGroup.toGL X) : Matrix (Fin (k + m)) (Fin (k + m)) K) *
        (blockGL K k m (SpecialLinearGroup.toGL Y) : Matrix (Fin (k + m)) (Fin (k + m)) K)
    rw [map_mul, map_mul, Units.val_mul])

theorem coe_blockSL (X : SpecialLinearGroup (Fin k) K) :
    (blockSL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K) =
      blockGL K k m (SpecialLinearGroup.toGL X) :=
  rfl

@[expose] def diagBlock (X : Matrix (Fin k) (Fin k) K) (Y : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin (k + m)) (Fin (k + m)) K :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks X 0 0 Y)

theorem coe_blockGL_eq_diagBlock (X : GL (Fin k) K) :
    (blockGL K k m X : Matrix (Fin (k + m)) (Fin (k + m)) K) =
      diagBlock (X : Matrix (Fin k) (Fin k) K) 1 :=
  rfl

theorem diagBlock_mul (X X' : Matrix (Fin k) (Fin k) K) (Y Y' : Matrix (Fin m) (Fin m) K) :
    diagBlock X Y * diagBlock X' Y' = diagBlock (X * X') (Y * Y') := by
  rw [diagBlock, diagBlock, diagBlock, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem diagBlock_transpose (X : Matrix (Fin k) (Fin k) K) (Y : Matrix (Fin m) (Fin m) K) :
    (diagBlock X Y)ᵀ = diagBlock Xᵀ Yᵀ := by
  rw [diagBlock, diagBlock, reindex_apply, reindex_apply, transpose_submatrix,
    fromBlocks_transpose, transpose_zero, transpose_zero]

theorem diagBlock_map (τ : K →+* K) (X : Matrix (Fin k) (Fin k) K)
    (Y : Matrix (Fin m) (Fin m) K) :
    (diagBlock X Y).map τ = diagBlock (X.map τ) (Y.map τ) := by
  rw [diagBlock, diagBlock, reindex_apply, reindex_apply, ← submatrix_map, fromBlocks_map,
    Matrix.map_zero _ (map_zero τ), Matrix.map_zero _ (map_zero τ)]

theorem diagBlock_one :
    diagBlock (1 : Matrix (Fin k) (Fin k) K) (1 : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [diagBlock, fromBlocks_one, reindex_apply, submatrix_one_equiv]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
