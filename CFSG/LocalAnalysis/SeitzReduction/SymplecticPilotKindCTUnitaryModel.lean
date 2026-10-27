module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr mem_SU)
open scoped MatrixGroups

@[expose] def ctuCoordFun (N ε : ℕ) : (Fin N ⊕ Fin N) ⊕ Fin ε → Fin (2 * N + ε) :=
  Sum.elim (Sum.elim (fun p => ⟨p.1, by have := p.2; omega⟩)
    (fun p => ⟨2 * N + ε - 1 - p.1, by have := p.2; omega⟩)) (fun i => ⟨N + i.1, by
      have := i.2; omega⟩)

theorem ctuCoordFun_injective (N ε : ℕ) : Function.Injective (ctuCoordFun N ε) := by
  intro w w' h
  have hv := congrArg Fin.val h
  rcases w with (p | p) | i <;> rcases w' with (p' | p') | i' <;>
    simp only [ctuCoordFun, Sum.elim_inl, Sum.elim_inr] at hv <;>
    first
    | (have := p.2; have := p'.2; omega)
    | (have := p.2; have := i'.2; omega)
    | (have := i.2; have := p'.2; omega)
    | (congr 2; ext; omega)

@[expose] noncomputable def ctuCoord (N ε : ℕ) : (Fin N ⊕ Fin N) ⊕ Fin ε ≃ Fin (2 * N + ε) :=
  Equiv.ofBijective (ctuCoordFun N ε) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨ctuCoordFun_injective N ε, by simp only [Fintype.card_sum, Fintype.card_fin]; ring⟩)

variable {N ε : ℕ}

@[simp] theorem ctuCoord_inl_inl (p : Fin N) :
    ((ctuCoord N ε (Sum.inl (Sum.inl p))) : ℕ) = p.1 := rfl

@[simp] theorem ctuCoord_inl_inr (p : Fin N) :
    ((ctuCoord N ε (Sum.inl (Sum.inr p))) : ℕ) = 2 * N + ε - 1 - p.1 := rfl

@[simp] theorem ctuCoord_inr (i : Fin ε) :
    ((ctuCoord N ε (Sum.inr i)) : ℕ) = N + i.1 := rfl

@[expose] def ctuPar : (Fin N ⊕ Fin N) ⊕ Fin ε → (Fin N ⊕ Fin N) ⊕ Fin ε := Sum.map par id

@[simp] theorem ctuPar_inl (u : Fin N ⊕ Fin N) :
    ctuPar (ε := ε) (Sum.inl u) = Sum.inl (par u) := rfl

@[simp] theorem ctuPar_inr (i : Fin ε) : ctuPar (N := N) (Sum.inr i) = Sum.inr i := rfl

theorem ctuCoord_rev (hε : ε ≤ 1) (w : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    Fin.rev (ctuCoord N ε w) = ctuCoord N ε (ctuPar w) := by
  apply Fin.ext
  rcases w with (p | p) | i
  · simp only [Fin.val_rev, ctuCoord_inl_inl, ctuPar_inl, par_inl, ctuCoord_inl_inr]
    omega
  · simp only [Fin.val_rev, ctuCoord_inl_inr, ctuPar_inl, par_inr, ctuCoord_inl_inl]
    have := p.2
    omega
  · simp only [Fin.val_rev, ctuCoord_inr, ctuPar_inr]
    have := i.2
    omega

theorem antidiag_ctuCoord {F : Type*} [Field F] (hε : ε ≤ 1) (w w' : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    (antidiag (2 * N + ε) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε w)
      (ctuCoord N ε w') = if w' = ctuPar w then 1 else 0 := by
  simp only [antidiag, of_apply, ctuCoord_rev hε]
  exact if_congr (ctuCoord N ε).injective.eq_iff rfl rfl

@[expose] noncomputable def ctuPlanes (ε : ℕ) (R : Finset (Fin N)) : Finset (Fin (2 * N + ε)) :=
  Finset.univ.filter fun a => InPlanes R ((ctuCoord N ε).symm a)

theorem ctuCoord_mem_ctuPlanes {R : Finset (Fin N)} {w : (Fin N ⊕ Fin N) ⊕ Fin ε} :
    ctuCoord N ε w ∈ ctuPlanes ε R ↔ InPlanes R w := by
  simp [ctuPlanes]

theorem ctuPlanes_mono {R R' : Finset (Fin N)} (h : R ⊆ R') :
    ctuPlanes ε R ⊆ ctuPlanes ε R' := by
  intro a ha
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  rw [ctuCoord_mem_ctuPlanes] at ha ⊢
  rcases w with u | i
  · exact h ha
  · exact ha.elim

theorem ctuPlanes_union (R R' : Finset (Fin N)) :
    ctuPlanes ε (R ∪ R') = ctuPlanes ε R ∪ ctuPlanes ε R' := by
  ext a
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  rw [Finset.mem_union, ctuCoord_mem_ctuPlanes, ctuCoord_mem_ctuPlanes, ctuCoord_mem_ctuPlanes]
  rcases w with u | i
  · simp
  · simp

theorem rev_mem_ctuPlanes_iff (hε : ε ≤ 1) {R : Finset (Fin N)} {a : Fin (2 * N + ε)} :
    Fin.rev a ∈ ctuPlanes ε R ↔ a ∈ ctuPlanes ε R := by
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  rw [ctuCoord_rev hε, ctuCoord_mem_ctuPlanes, ctuCoord_mem_ctuPlanes]
  rcases w with u | i
  · rcases u with p | p <;> simp
  · simp

section Embed

variable {K F : Type} [Field K] [Field F]

@[expose] noncomputable def ctuEmbedMat (ε : ℕ) (ι : K →+* F)
    (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F :=
  reindex (ctuCoord N ε) (ctuCoord N ε) (fromBlocks (y.map ι) 0 0 1)

theorem ctuEmbedMat_apply (ι : K →+* F) (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K)
    (w w' : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    ctuEmbedMat ε ι y (ctuCoord N ε w) (ctuCoord N ε w') = fromBlocks (y.map ι) 0 0 1 w w' := by
  simp [ctuEmbedMat]

theorem ctuEmbedMat_mul (ι : K →+* F) (y z : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) :
    ctuEmbedMat ε ι (y * z) = ctuEmbedMat ε ι y * ctuEmbedMat ε ι z := by
  simp only [ctuEmbedMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply, Matrix.map_mul]
  simp

theorem ctuEmbedMat_one (ι : K →+* F) :
    ctuEmbedMat ε ι (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) = 1 := by
  rw [ctuEmbedMat, Matrix.map_one _ (map_zero ι) (map_one ι), fromBlocks_one, reindex_apply,
    submatrix_one_equiv]

theorem ctuEmbedMat_transpose (ι : K →+* F) (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) :
    (ctuEmbedMat ε ι y)ᵀ = ctuEmbedMat ε ι yᵀ := by
  rw [ctuEmbedMat, ctuEmbedMat, transpose_reindex, fromBlocks_transpose]
  simp [Matrix.transpose_map]

theorem det_ctuEmbedMat (ι : K →+* F) (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) :
    (ctuEmbedMat ε ι y).det = ι y.det := by
  rw [ctuEmbedMat, det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one,
    RingHom.map_det]
  rfl

theorem ctuEmbedMat_map (σ : F ≃+* F) {ι : K →+* F} (hι : ∀ c, σ (ι c) = ι c)
    (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) :
    (ctuEmbedMat ε ι y).map σ = ctuEmbedMat ε ι y := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [map_apply, ctuEmbedMat_apply]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, map_apply, hι]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
  · rw [fromBlocks_apply₂₂]
    by_cases h : i = j
    · subst h
      rw [one_apply_eq, map_one]
    · rw [one_apply_ne h, map_zero]

theorem antidiag_eq_ctuEmbedMat_gram [CharP K 2] (hε : ε ≤ 1) (ι : K →+* F) :
    (antidiag (2 * N + ε) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
      ctuEmbedMat ε ι (gram K N) := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [antidiag_ctuCoord hε, ctuEmbedMat_apply]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, map_apply,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
    have hsgn : sgn K u = 1 := by
      rcases u with u | u
      · rfl
      · simp [sgn, CharTwo.neg_eq]
    simp only [ctuPar_inl, Sum.inl.injEq, hsgn]
    split_ifs <;> simp
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₂, ctuPar_inr, Matrix.one_apply]
    simp only [Sum.inr.injEq, eq_comm]

theorem ctuEmbedMat_isometry [CharP K 2] (hε : ε ≤ 1) (σ : F ≃+* F) {ι : K →+* F}
    (hι : ∀ c, σ (ι c) = ι c) (y : StatedSp N K) :
    conjTr σ (ctuEmbedMat ε ι (mat N K y)) * antidiag (2 * N + ε) * ctuEmbedMat ε ι (mat N K y) =
      antidiag (2 * N + ε) := by
  rw [conjTr, ctuEmbedMat_map σ hι, ctuEmbedMat_transpose, antidiag_eq_ctuEmbedMat_gram hε ι,
    ← ctuEmbedMat_mul, ← ctuEmbedMat_mul, mat_transpose_mul_gram_mul]

variable (ε) in
@[expose] noncomputable def ctuEmbed [CharP K 2] (hε : ε ≤ 1) (σ : F ≃+* F) (ι : K →+* F)
    (hι : ∀ c, σ (ι c) = ι c) : StatedSp N K →* SU σ (2 * N + ε) where
  toFun y := ⟨⟨ctuEmbedMat ε ι (mat N K y), ctuEmbedMat ε ι (mat N K y⁻¹),
      by rw [← ctuEmbedMat_mul, ← map_mul, mul_inv_cancel, map_one, ctuEmbedMat_one],
      by rw [← ctuEmbedMat_mul, ← map_mul, inv_mul_cancel, map_one, ctuEmbedMat_one]⟩,
    by
      change (ctuEmbedMat ε ι (mat N K y)).det = 1
      rw [det_ctuEmbedMat, det_mat_statedSp_of_charTwo, map_one],
    ctuEmbedMat_isometry hε σ hι y⟩
  map_one' := Subtype.ext (Units.ext (by
    change ctuEmbedMat ε ι (mat N K 1) = 1
    rw [map_one, ctuEmbedMat_one]))
  map_mul' y z := Subtype.ext (Units.ext (by
    change ctuEmbedMat ε ι (mat N K (y * z)) =
      ctuEmbedMat ε ι (mat N K y) * ctuEmbedMat ε ι (mat N K z)
    rw [map_mul, ctuEmbedMat_mul]))

variable [CharP K 2] {hε : ε ≤ 1} {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

theorem coe_ctuEmbed (y : StatedSp N K) :
    (((ctuEmbed ε hε σ ι hι y : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) = ctuEmbedMat ε ι (mat N K y) := rfl

theorem ctuEmbed_apply_ctuCoord (y : StatedSp N K) (w w' : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    (((ctuEmbed ε hε σ ι hι y : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε w) (ctuCoord N ε w') =
        fromBlocks ((mat N K y).map ι) 0 0 1 w w' := by
  rw [coe_ctuEmbed, ctuEmbedMat_apply]

theorem ctuEmbed_injective : Function.Injective (ctuEmbed (N := N) ε hε σ ι hι) := by
  intro y z h
  apply mat_injective
  ext u v
  have := congrArg (fun A : SU σ (2 * N + ε) =>
    ((A : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)
      (ctuCoord N ε (Sum.inl u)) (ctuCoord N ε (Sum.inl v))) h
  simp only [ctuEmbed_apply_ctuCoord, fromBlocks_apply₁₁, map_apply] at this
  exact ι.injective this

end Embed

section Blocks

variable {F : Type} [Field F]

variable (σ : F ≃+* F) (n : ℕ) in
@[expose] def ctuToSL : SU σ n →* SpecialLinearGroup (Fin n) F where
  toFun x := ⟨((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), x.2.1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem coe_ctuToSL {σ : F ≃+* F} {n : ℕ} (x : SU σ n) :
    ((ctuToSL σ n x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl

theorem ctuToSL_injective {σ : F ≃+* F} {n : ℕ} : Function.Injective (ctuToSL σ n) :=
  fun _ _ h => Subtype.ext (Units.ext (congrArg Subtype.val h))

variable (σ : F ≃+* F) (ε : ℕ) in
@[expose] noncomputable def ctuBlock (R : Finset (Fin N)) : Subgroup (SU σ (2 * N + ε)) :=
  (blockSpecialLinear (ctuPlanes ε R)ᶜ).comap (ctuToSL σ (2 * N + ε))

variable {σ : F ≃+* F}

theorem mem_ctuBlock {R : Finset (Fin N)} {x : SU σ (2 * N + ε)} :
    x ∈ ctuBlock σ ε R ↔ ∀ a b, (a ∈ ctuPlanes ε R ∨ b ∈ ctuPlanes ε R) →
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b =
        (1 : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b := by
  rw [ctuBlock, mem_comap, mem_blockSpecialLinear]
  simp only [Finset.mem_compl, not_not, coe_ctuToSL]

theorem ctuBlock_anti {R R' : Finset (Fin N)} (h : R ⊆ R') :
    ctuBlock σ ε R' ≤ ctuBlock σ ε R :=
  comap_mono (LinearPilot.blockSpecialLinear_mono (Finset.compl_subset_compl.2 (ctuPlanes_mono h)))

theorem mem_ctuBlock_union {R R' : Finset (Fin N)} {x : SU σ (2 * N + ε)}
    (hx : x ∈ ctuBlock σ ε R) (hx' : x ∈ ctuBlock σ ε R') : x ∈ ctuBlock σ ε (R ∪ R') := by
  rw [mem_ctuBlock] at hx hx' ⊢
  intro a b hab
  rw [ctuPlanes_union, Finset.mem_union, Finset.mem_union] at hab
  rcases hab with (h | h) | (h | h)
  · exact hx a b (Or.inl h)
  · exact hx' a b (Or.inl h)
  · exact hx a b (Or.inr h)
  · exact hx' a b (Or.inr h)

end Blocks

section EmbedBlocks

variable {K F : Type} [Field K] [Field F] [CharP K 2] {hε : ε ≤ 1} {σ : F ≃+* F}
  {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

theorem ctuEmbed_mem_ctuBlock_iff {R : Finset (Fin N)} {y : StatedSp N K} :
    ctuEmbed ε hε σ ι hι y ∈ ctuBlock σ ε R ↔ y ∈ spBlock K Rᶜ := by
  rw [mem_ctuBlock, mem_spBlock]
  constructor
  · intro h u v huv
    have h1 := h (ctuCoord N ε (Sum.inl u)) (ctuCoord N ε (Sum.inl v)) (by
      simp only [ctuCoord_mem_ctuPlanes, inPlanes_inl]
      by_contra hc
      push Not at hc
      exact huv ⟨by simpa [mem_planeCoords] using hc.1, by simpa [mem_planeCoords] using hc.2⟩)
    rw [ctuEmbed_apply_ctuCoord, fromBlocks_apply₁₁, map_apply, Matrix.one_apply] at h1
    simp only [(ctuCoord N ε).injective.eq_iff, Sum.inl.injEq] at h1
    apply ι.injective
    rw [h1, Matrix.one_apply]
    split_ifs <;> simp
  · intro h a b hab
    obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
    obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
    rw [ctuEmbed_apply_ctuCoord, Matrix.one_apply]
    simp only [(ctuCoord N ε).injective.eq_iff]
    simp only [ctuCoord_mem_ctuPlanes] at hab
    rcases w with u | i <;> rcases w' with v | j
    · have hu : ¬(u ∈ planeCoords Rᶜ ∧ v ∈ planeCoords Rᶜ) := by
        simp only [mem_planeCoords, Finset.mem_compl]
        rcases hab with h1 | h1
        · exact fun h2 => h2.1 h1
        · exact fun h2 => h2.2 h1
      rw [fromBlocks_apply₁₁, map_apply, h u v hu, Matrix.one_apply]
      simp only [Sum.inl.injEq]
      split_ifs <;> simp
    · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
      simp
    · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
      simp
    · simp at hab

theorem ctuToSL_ctuEmbed_mem_blockSpecialLinear {R : Finset (Fin N)} {y : StatedSp N K}
    (hy : y ∈ spBlock K R) :
    ctuToSL σ (2 * N + ε) (ctuEmbed ε hε σ ι hι y) ∈ blockSpecialLinear (ctuPlanes ε R) := by
  rw [mem_blockSpecialLinear]
  intro a b hab
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [coe_ctuToSL, ctuEmbed_apply_ctuCoord, Matrix.one_apply]
  simp only [(ctuCoord N ε).injective.eq_iff]
  simp only [ctuCoord_mem_ctuPlanes] at hab
  rcases w with u | i <;> rcases w' with v | j
  · have hu : ¬(u ∈ planeCoords R ∧ v ∈ planeCoords R) := by
      simp only [mem_planeCoords]
      simp only [inPlanes_inl] at hab
      rintro ⟨h1, h2⟩
      rcases hab with h | h
      · exact h h1
      · exact h h2
    rw [fromBlocks_apply₁₁, map_apply, mem_spBlock.1 hy u v hu, Matrix.one_apply]
    simp only [Sum.inl.injEq]
    split_ifs <;> simp
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₂, Matrix.one_apply]
    simp only [Sum.inr.injEq]

theorem commute_ctuBlock_ctuEmbed {R : Finset (Fin N)} {x : SU σ (2 * N + ε)}
    (hx : x ∈ ctuBlock σ ε R) {y : StatedSp N K} (hy : y ∈ spBlock K R) :
    x * ctuEmbed ε hε σ ι hι y = ctuEmbed ε hε σ ι hι y * x := by
  apply ctuToSL_injective
  rw [map_mul, map_mul]
  exact (LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_left hx
    (ctuToSL_ctuEmbed_mem_blockSpecialLinear hy)).eq

end EmbedBlocks

section Center

open CFSG.LieType.BorelTits (unitaryInvolution)

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}

theorem exists_scalar_of_mem_center_SU (hF : Nat.card F = (p ^ f) ^ 2) (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) {z : SU (unitaryInvolution F p f) n}
    (hz : z ∈ center (SU (unitaryInvolution F p f) n)) :
    ∃ c : Fˣ, (z : GL (Fin n) F) = GeneralLinearGroup.scalar (Fin n) c := by
  set P := (CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n).choose with hP
  set φ := (CFSG.LieType.Universal.Unitary.conjEquiv P
    (CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n).choose_spec).trans
      (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n)) with hφ
  have h1 : φ z ∈ center (StatedSU n (p ^ f) F) := by
    rw [mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y', rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hz y']
  rw [(CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF hn hnq).2,
    mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨c, ?_⟩
  have h2 : ((φ z : StatedSU n (p ^ f) F) : GL (Fin n) F) = P * (z : GL (Fin n) F) * P⁻¹ := rfl
  have hcen : GeneralLinearGroup.scalar (Fin n) c ∈ center (GL (Fin n) F) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have h3 : (z : GL (Fin n) F) = P⁻¹ * GeneralLinearGroup.scalar (Fin n) c * P := by
    rw [hc, h2]
    group
  rw [h3, mul_assoc, ← (mem_center_iff.1 hcen P), ← mul_assoc, inv_mul_cancel, one_mul]

theorem eq_one_of_mem_center_of_mem_ctuBlock {N ε : ℕ} (hF : Nat.card F = (p ^ f) ^ 2)
    (hn : 3 ≤ 2 * N + ε) (hnq : (2 * N + ε, p ^ f) ≠ (3, 2)) {R : Finset (Fin N)} {k : Fin N}
    (hk : k ∈ R) {z : SU (unitaryInvolution F p f) (2 * N + ε)}
    (hz : z ∈ center (SU (unitaryInvolution F p f) (2 * N + ε)))
    (hzR : z ∈ ctuBlock (unitaryInvolution F p f) ε R) : z = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_SU hF hn hnq hz
  have h1 := mem_ctuBlock.1 hzR (ctuCoord N ε (Sum.inl (Sum.inl k)))
    (ctuCoord N ε (Sum.inl (Sum.inl k))) (Or.inl (by
      rw [ctuCoord_mem_ctuPlanes, inPlanes_inl, planeOf_inl]
      exact hk))
  rw [hc, GeneralLinearGroup.coe_scalar, Matrix.one_apply_eq, scalar_apply, diagonal_apply_eq]
    at h1
  have hc1 : c = 1 := Units.ext h1
  apply Subtype.ext
  rw [hc, hc1, map_one]
  rfl

theorem injOn_ctuBlock_of_ker_le_center {N ε : ℕ} (hF : Nat.card F = (p ^ f) ^ 2)
    (hn : 3 ≤ 2 * N + ε) (hnq : (2 * N + ε, p ^ f) ≠ (3, 2)) {G : Type*} [Group G]
    {ψ : SU (unitaryInvolution F p f) (2 * N + ε) →* G}
    (hker : ψ.ker ≤ center (SU (unitaryInvolution F p f) (2 * N + ε))) {R : Finset (Fin N)}
    {k : Fin N} (hk : k ∈ R) {x y : SU (unitaryInvolution F p f) (2 * N + ε)}
    (hx : x ∈ ctuBlock (unitaryInvolution F p f) ε R)
    (hy : y ∈ ctuBlock (unitaryInvolution F p f) ε R) (hxy : ψ x = ψ y) : x = y := by
  have hm : x * y⁻¹ ∈ ctuBlock (unitaryInvolution F p f) ε R := mul_mem hx (inv_mem hy)
  have hkm : x * y⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  exact mul_inv_eq_one.1 (eq_one_of_mem_center_of_mem_ctuBlock hF hn hnq hk (hker hkm) hm)

end Center

end CFSG.SeitzReduction.SymplecticPilot
