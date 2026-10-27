module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryModel
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.Steinberg (IsBlkOn submatrix_mul_of_isBlkOn det_submatrix_of_isBlkOn
  conjTr_mul_antidiag_mul_apply unitaryBlockHom mat_unitaryBlockHom unitaryBlockHom_injective)

section Ext

variable {F : Type*} [Field F] {r n : ℕ} {e : Fin r → Fin n}

@[expose] noncomputable def blockExt (he : Function.Injective e) (M : Matrix (Fin r) (Fin r) F) :
    Matrix (Fin n) (Fin n) F := fun a b =>
  if h : a ∈ Set.range e ∧ b ∈ Set.range e then
    M ((Equiv.ofInjective e he).symm ⟨a, h.1⟩) ((Equiv.ofInjective e he).symm ⟨b, h.2⟩)
  else (1 : Matrix (Fin n) (Fin n) F) a b

theorem blockExt_apply_apply (he : Function.Injective e) (M : Matrix (Fin r) (Fin r) F)
    (i j : Fin r) : blockExt he M (e i) (e j) = M i j := by
  rw [blockExt, dite_eq_left ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩]
  congr 1 <;> exact (Equiv.ofInjective_symm_apply he _)

theorem isBlkOn_blockExt (he : Function.Injective e) (M : Matrix (Fin r) (Fin r) F) :
    IsBlkOn e (blockExt he M) := by
  intro a b hab
  have hn : ¬(a ∈ Set.range e ∧ b ∈ Set.range e) := by
    rintro ⟨ha, hb⟩
    rcases hab with h | h
    · exact h ha
    · exact h hb
  rw [blockExt, dite_eq_right hn]

theorem submatrix_blockExt (he : Function.Injective e) (M : Matrix (Fin r) (Fin r) F) :
    (blockExt he M).submatrix e e = M := by
  ext i j
  rw [submatrix_apply, blockExt_apply_apply]

theorem eq_of_isBlkOn_of_submatrix_eq {M M' : Matrix (Fin n) (Fin n) F} (hM : IsBlkOn e M)
    (hM' : IsBlkOn e M') (h : M.submatrix e e = M'.submatrix e e) : M = M' := by
  ext a b
  by_cases hab : a ∈ Set.range e ∧ b ∈ Set.range e
  · obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hab
    exact congrFun (congrFun h i) j
  · rw [not_and_or] at hab
    rw [hM a b hab, hM' a b hab]

theorem isBlkOn_mul {M M' : Matrix (Fin n) (Fin n) F} (hM : IsBlkOn e M) (hM' : IsBlkOn e M') :
    IsBlkOn e (M * M') := by
  intro a b hab
  rw [Matrix.mul_apply]
  rcases hab with ha | hb
  · rw [Finset.sum_eq_single a (fun c _ hca => by
      rw [hM a c (Or.inl ha), one_apply_ne (Ne.symm hca), zero_mul]) (by simp),
      hM a a (Or.inl ha), one_apply_eq, one_mul, hM' a b (Or.inl ha)]
  · rw [Finset.sum_eq_single b (fun c _ hcb => by
      rw [hM' c b (Or.inr hb), one_apply_ne hcb, mul_zero]) (by simp),
      hM' b b (Or.inr hb), one_apply_eq, mul_one, hM a b (Or.inr hb)]

theorem blockExt_mul (he : Function.Injective e) (M M' : Matrix (Fin r) (Fin r) F) :
    blockExt he (M * M') = blockExt he M * blockExt he M' := by
  refine eq_of_isBlkOn_of_submatrix_eq (isBlkOn_blockExt he _)
    (isBlkOn_mul (isBlkOn_blockExt he M) (isBlkOn_blockExt he M')) ?_
  rw [submatrix_blockExt, submatrix_mul_of_isBlkOn he (isBlkOn_blockExt he M), submatrix_blockExt,
    submatrix_blockExt]

theorem blockExt_one (he : Function.Injective e) :
    blockExt he (1 : Matrix (Fin r) (Fin r) F) = 1 := by
  refine eq_of_isBlkOn_of_submatrix_eq (isBlkOn_blockExt he _) (fun _ _ _ => rfl) ?_
  rw [submatrix_blockExt, submatrix_one _ he]

theorem det_blockExt (he : Function.Injective e) (M : Matrix (Fin r) (Fin r) F) :
    (blockExt he M).det = M.det := by
  rw [← det_submatrix_of_isBlkOn he (isBlkOn_blockExt he M), submatrix_blockExt]

theorem blockExt_isometry (σ : F ≃+* F) (he : Function.Injective e)
    (hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i)) {M : Matrix (Fin r) (Fin r) F}
    (hM : conjTr σ M * antidiag r * M = antidiag r) :
    conjTr σ (blockExt he M) * antidiag n * blockExt he M = antidiag n := by
  have hR : ∀ a : Fin n, Fin.rev a ∈ Set.range e ↔ a ∈ Set.range e := by
    intro a
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fin.rev i, by rw [hrev, hi, Fin.rev_rev]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.rev i, hrev i⟩
  have hB := isBlkOn_blockExt (F := F) he M
  ext a b
  rw [conjTr_mul_antidiag_mul_apply]
  by_cases ha : a ∈ Set.range e
  · by_cases hb : b ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      have h := congrFun (congrFun hM i) j
      rw [conjTr_mul_antidiag_mul_apply] at h
      rw [← Fintype.sum_of_injective e he _ (fun t => σ (blockExt he M t (e i)) *
        blockExt he M (Fin.rev t) (e j))
        (fun t ht => by rw [hB t (e i) (Or.inl ht), one_apply_ne (fun h' => ht ⟨i, h'.symm⟩),
          map_zero, zero_mul]) fun t => rfl]
      simp only [← hrev, blockExt_apply_apply]
      rw [h]
      simp only [antidiag, of_apply, ← hrev, he.eq_iff]
    · rw [Finset.sum_eq_single (Fin.rev b)]
      · rw [Fin.rev_rev, hB (Fin.rev b) a (Or.inl (fun h' => hb ((hR b).1 h'))),
          hB b b (Or.inl hb), one_apply_eq, mul_one, antidiag, of_apply, one_apply]
        by_cases h1 : Fin.rev b = a
        · rw [ite_eq_left h1, ite_eq_left (by rw [← h1, Fin.rev_rev]), map_one]
        · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (by rw [h2, Fin.rev_rev])), map_zero]
      · intro t _ ht
        rw [hB (Fin.rev t) b (Or.inr hb), one_apply_ne (fun h' => ht (by rw [← h', Fin.rev_rev])),
          mul_zero]
      · simp
  · rw [Finset.sum_eq_single a]
    · rw [hB a a (Or.inl ha), one_apply_eq, map_one, one_mul,
        hB (Fin.rev a) b (Or.inl (fun h' => ha ((hR a).1 h'))), antidiag, of_apply, one_apply]
      by_cases h1 : Fin.rev a = b
      · rw [ite_eq_left h1, ite_eq_left h1.symm]
      · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 h2.symm)]
    · intro t _ hta
      rw [hB t a (Or.inr ha), one_apply_ne hta, map_zero, zero_mul]
    · simp

variable (σ : F ≃+* F) in
@[expose] noncomputable def blockExtHom (he : Function.Injective e)
    (hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i)) : SU σ r →* SU σ n where
  toFun y := ⟨⟨blockExt he (mat σ r y), blockExt he (mat σ r y⁻¹),
      by rw [← blockExt_mul, ← map_mul, mul_inv_cancel, map_one, blockExt_one],
      by rw [← blockExt_mul, ← map_mul, inv_mul_cancel, map_one, blockExt_one]⟩,
    by
      change (blockExt he (mat σ r y)).det = 1
      rw [det_blockExt]
      exact y.2.1,
    blockExt_isometry σ he hrev y.2.2⟩
  map_one' := Subtype.ext (Units.ext (by
    change blockExt he (mat σ r 1) = 1
    rw [map_one, blockExt_one]))
  map_mul' y z := Subtype.ext (Units.ext (by
    change blockExt he (mat σ r (y * z)) = blockExt he (mat σ r y) * blockExt he (mat σ r z)
    rw [map_mul, blockExt_mul]))

theorem mat_blockExtHom (σ : F ≃+* F) (he : Function.Injective e)
    (hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i)) (y : SU σ r) :
    mat σ n (blockExtHom σ he hrev y) = blockExt he (mat σ r y) := rfl

end Ext

section CtuBlock

variable {m ε : ℕ}

abbrev ctuSkip (m ε : ℕ) (k : Fin (m + 1)) :
    (Fin m ⊕ Fin m) ⊕ Fin ε → (Fin (m + 1) ⊕ Fin (m + 1)) ⊕ Fin ε :=
  Sum.map (Sum.map k.succAbove k.succAbove) id

theorem ctuSkip_injective (k : Fin (m + 1)) : Function.Injective (ctuSkip m ε k) :=
  Sum.map_injective.2 ⟨Sum.map_injective.2 ⟨Fin.succAbove_right_injective,
    Fin.succAbove_right_injective⟩, Function.injective_id⟩

@[expose] noncomputable def ctuBlockIdx (m ε : ℕ) (k : Fin (m + 1)) (a : Fin (2 * m + ε)) :
    Fin (2 * (m + 1) + ε) :=
  ctuCoord (m + 1) ε (ctuSkip m ε k ((ctuCoord m ε).symm a))

theorem ctuBlockIdx_ctuCoord (k : Fin (m + 1)) (w : (Fin m ⊕ Fin m) ⊕ Fin ε) :
    ctuBlockIdx m ε k (ctuCoord m ε w) = ctuCoord (m + 1) ε (ctuSkip m ε k w) := by
  simp [ctuBlockIdx]

theorem ctuBlockIdx_injective (k : Fin (m + 1)) : Function.Injective (ctuBlockIdx m ε k) := by
  intro a b h
  obtain ⟨w, rfl⟩ := (ctuCoord m ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord m ε).surjective b
  rw [ctuBlockIdx_ctuCoord, ctuBlockIdx_ctuCoord] at h
  rw [ctuSkip_injective k ((ctuCoord (m + 1) ε).injective h)]

theorem ctuBlockIdx_rev (hε : ε ≤ 1) (k : Fin (m + 1)) (a : Fin (2 * m + ε)) :
    ctuBlockIdx m ε k (Fin.rev a) = Fin.rev (ctuBlockIdx m ε k a) := by
  obtain ⟨w, rfl⟩ := (ctuCoord m ε).surjective a
  rw [ctuCoord_rev hε, ctuBlockIdx_ctuCoord, ctuBlockIdx_ctuCoord, ctuCoord_rev hε]
  congr 1
  rcases w with (p | p) | i <;> rfl

theorem mem_range_ctuBlockIdx_iff (k : Fin (m + 1)) (b : Fin (2 * (m + 1) + ε)) :
    b ∈ Set.range (ctuBlockIdx m ε k) ↔ b ∉ ctuPlanes ε ({k} : Finset (Fin (m + 1))) := by
  obtain ⟨w, rfl⟩ := (ctuCoord (m + 1) ε).surjective b
  rw [ctuCoord_mem_ctuPlanes]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨v, rfl⟩ := (ctuCoord m ε).surjective a
    rw [ctuBlockIdx_ctuCoord] at ha
    rw [← (ctuCoord (m + 1) ε).injective ha]
    rcases v with (p | p) | i
    · simp [Fin.succAbove_ne]
    · simp [Fin.succAbove_ne]
    · exact id
  · intro h
    rcases w with (p | p) | i
    · have hp : p ≠ k := by simpa using h
      obtain ⟨p', rfl⟩ := Fin.exists_succAbove_eq hp
      exact ⟨ctuCoord m ε (Sum.inl (Sum.inl p')), by rw [ctuBlockIdx_ctuCoord]; rfl⟩
    · have hp : p ≠ k := by simpa using h
      obtain ⟨p', rfl⟩ := Fin.exists_succAbove_eq hp
      exact ⟨ctuCoord m ε (Sum.inl (Sum.inr p')), by rw [ctuBlockIdx_ctuCoord]; rfl⟩
    · exact ⟨ctuCoord m ε (Sum.inr i), by rw [ctuBlockIdx_ctuCoord]; rfl⟩

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem isBlkOn_of_mem_ctuBlock {k : Fin (m + 1)} {x : SU σ (2 * (m + 1) + ε)}
    (hx : x ∈ ctuBlock σ ε ({k} : Finset (Fin (m + 1)))) :
    IsBlkOn (ctuBlockIdx m ε k) (mat σ (2 * (m + 1) + ε) x) := by
  intro a b hab
  apply mem_ctuBlock.1 hx a b
  rcases hab with ha | hb
  · left
    by_contra h
    exact ha ((mem_range_ctuBlockIdx_iff k a).2 h)
  · right
    by_contra h
    exact hb ((mem_range_ctuBlockIdx_iff k b).2 h)

theorem blockExtHom_mem_ctuBlock (hε : ε ≤ 1) (k : Fin (m + 1)) (y : SU σ (2 * m + ε)) :
    blockExtHom σ (ctuBlockIdx_injective k) (ctuBlockIdx_rev hε k) y ∈
      ctuBlock σ ε ({k} : Finset (Fin (m + 1))) := by
  rw [mem_ctuBlock]
  intro a b hab
  apply isBlkOn_blockExt
  rcases hab with ha | hb
  · left
    rwa [mem_range_ctuBlockIdx_iff, not_not]
  · right
    rwa [mem_range_ctuBlockIdx_iff, not_not]

variable (σ) in
@[expose] noncomputable def ctuBlockEquiv (hε : ε ≤ 1) (k : Fin (m + 1)) :
    ctuBlock σ ε ({k} : Finset (Fin (m + 1))) ≃* SU σ (2 * m + ε) :=
  MulEquiv.ofBijective (unitaryBlockHom σ (ctuBlockIdx_injective k) (ctuBlockIdx_rev hε k) _
    fun _ hg => isBlkOn_of_mem_ctuBlock hg)
    ⟨unitaryBlockHom_injective, fun y => ⟨⟨_, blockExtHom_mem_ctuBlock hε k y⟩, by
      apply mat_injective
      rw [mat_unitaryBlockHom]
      exact submatrix_blockExt _ _⟩⟩

theorem mat_ctuBlockEquiv (hε : ε ≤ 1) (k : Fin (m + 1))
    (x : ctuBlock σ ε ({k} : Finset (Fin (m + 1)))) :
    mat σ (2 * m + ε) (ctuBlockEquiv σ hε k x) =
      (mat σ (2 * (m + 1) + ε) x).submatrix (ctuBlockIdx m ε k) (ctuBlockIdx m ε k) := rfl

theorem ctuBlockEquiv_ctuEmbed {K : Type} [Field K] [CharP K 2] (hε : ε ≤ 1) {ι : K →+* F}
    (hι : ∀ c, σ (ι c) = ι c) (k : Fin (m + 1)) (y : StatedSp m K)
    (hy : ctuEmbed ε hε σ ι hι ((complSpEquiv k y : complSp K k) : StatedSp (m + 1) K) ∈
      ctuBlock σ ε ({k} : Finset (Fin (m + 1)))) :
    ctuBlockEquiv σ hε k ⟨_, hy⟩ = ctuEmbed ε hε σ ι hι y := by
  apply mat_injective
  rw [mat_ctuBlockEquiv]
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord m ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord m ε).surjective b
  rw [submatrix_apply, ctuBlockIdx_ctuCoord, ctuBlockIdx_ctuCoord]
  change ctuEmbedMat ε ι (CFSG.LieType.Universal.Symplectic.SpExtras.mat (m + 1) K
      ((complSpEquiv k y : complSp K k) : StatedSp (m + 1) K)) _ _ =
    ctuEmbedMat ε ι (CFSG.LieType.Universal.Symplectic.SpExtras.mat m K y) _ _
  rw [ctuEmbedMat_apply, ctuEmbedMat_apply, coe_complSpEquiv_apply]
  rcases w with u | i <;> rcases w' with v | j
  · simp only [ctuSkip, Sum.map_inl, fromBlocks_apply₁₁, map_apply]
    rw [mat_spEmbed, spEmbedMat_apply_image Fin.succAbove_right_injective]
  · simp
  · simp
  · simp

end CtuBlock

end CFSG.SeitzReduction.SymplecticPilot
