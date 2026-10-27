module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryBlock
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignAut

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.Steinberg (IsBlkOn submatrix_mul_of_isBlkOn unitaryBlockHom mat_unitaryBlockHom
  unitaryBlockHom_injective)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Idx

variable {N ε : ℕ}

noncomputable abbrev ctuaSkip (R : Finset (Fin N)) (ε : ℕ) :
    (Fin Rᶜ.card ⊕ Fin Rᶜ.card) ⊕ Fin ε → (Fin N ⊕ Fin N) ⊕ Fin ε :=
  Sum.map (Sum.map (planeEnum Rᶜ) (planeEnum Rᶜ)) id

theorem ctuaSkip_injective (R : Finset (Fin N)) : Function.Injective (ctuaSkip R ε) :=
  Sum.map_injective.2 ⟨Sum.map_injective.2 ⟨planeEnum_injective _, planeEnum_injective _⟩,
    Function.injective_id⟩

@[expose] noncomputable def ctuaIdx (R : Finset (Fin N)) (ε : ℕ) (a : Fin (2 * Rᶜ.card + ε)) :
    Fin (2 * N + ε) :=
  ctuCoord N ε (ctuaSkip R ε ((ctuCoord Rᶜ.card ε).symm a))

theorem ctuaIdx_ctuCoord (R : Finset (Fin N)) (w : (Fin Rᶜ.card ⊕ Fin Rᶜ.card) ⊕ Fin ε) :
    ctuaIdx R ε (ctuCoord Rᶜ.card ε w) = ctuCoord N ε (ctuaSkip R ε w) := by
  simp [ctuaIdx]

theorem ctuaIdx_injective (R : Finset (Fin N)) : Function.Injective (ctuaIdx R ε) := by
  intro a b h
  obtain ⟨w, rfl⟩ := (ctuCoord Rᶜ.card ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord Rᶜ.card ε).surjective b
  rw [ctuaIdx_ctuCoord, ctuaIdx_ctuCoord] at h
  rw [ctuaSkip_injective R ((ctuCoord N ε).injective h)]

theorem ctuaIdx_rev (hε : ε ≤ 1) (R : Finset (Fin N)) (a : Fin (2 * Rᶜ.card + ε)) :
    ctuaIdx R ε (Fin.rev a) = Fin.rev (ctuaIdx R ε a) := by
  obtain ⟨w, rfl⟩ := (ctuCoord Rᶜ.card ε).surjective a
  rw [ctuCoord_rev hε, ctuaIdx_ctuCoord, ctuaIdx_ctuCoord, ctuCoord_rev hε]
  congr 1
  rcases w with (p | p) | i <;> rfl

theorem mem_range_ctuaIdx_iff (R : Finset (Fin N)) (b : Fin (2 * N + ε)) :
    b ∈ Set.range (ctuaIdx R ε) ↔ b ∉ ctuPlanes ε R := by
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective b
  rw [ctuCoord_mem_ctuPlanes]
  have hR : ∀ p : Fin N, p ∈ Set.range (planeEnum Rᶜ) ↔ p ∉ R := by
    intro p
    rw [range_planeEnum, Finset.mem_coe, Finset.mem_compl]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨v, rfl⟩ := (ctuCoord Rᶜ.card ε).surjective a
    rw [ctuaIdx_ctuCoord] at ha
    rw [← (ctuCoord N ε).injective ha]
    rcases v with (p | p) | i
    · exact (hR _).1 ⟨p, rfl⟩
    · exact (hR _).1 ⟨p, rfl⟩
    · exact id
  · intro h
    rcases w with (p | p) | i
    · obtain ⟨p', rfl⟩ := (hR p).2 (by simpa using h)
      exact ⟨ctuCoord Rᶜ.card ε (Sum.inl (Sum.inl p')), by rw [ctuaIdx_ctuCoord]; rfl⟩
    · obtain ⟨p', rfl⟩ := (hR p).2 (by simpa using h)
      exact ⟨ctuCoord Rᶜ.card ε (Sum.inl (Sum.inr p')), by rw [ctuaIdx_ctuCoord]; rfl⟩
    · exact ⟨ctuCoord Rᶜ.card ε (Sum.inr i), by rw [ctuaIdx_ctuCoord]; rfl⟩

end Idx

section BlockEquiv

variable {N ε : ℕ} {F : Type} [Field F] {σ : F ≃+* F}

theorem isBlkOn_of_mem_ctuBlock_ctua {R : Finset (Fin N)} {x : SU σ (2 * N + ε)}
    (hx : x ∈ ctuBlock σ ε R) : IsBlkOn (ctuaIdx R ε) (mat σ (2 * N + ε) x) := by
  intro a b hab
  apply mem_ctuBlock.1 hx a b
  rcases hab with ha | hb
  · left
    by_contra h
    exact ha ((mem_range_ctuaIdx_iff R a).2 h)
  · right
    by_contra h
    exact hb ((mem_range_ctuaIdx_iff R b).2 h)

theorem blockExtHom_mem_ctuBlock_ctua (hε : ε ≤ 1) (R : Finset (Fin N))
    (y : SU σ (2 * Rᶜ.card + ε)) :
    blockExtHom σ (ctuaIdx_injective R) (ctuaIdx_rev hε R) y ∈ ctuBlock σ ε R := by
  rw [mem_ctuBlock]
  intro a b hab
  apply isBlkOn_blockExt
  rcases hab with ha | hb
  · left
    rwa [mem_range_ctuaIdx_iff, not_not]
  · right
    rwa [mem_range_ctuaIdx_iff, not_not]

variable (σ) in
@[expose] noncomputable def ctuaBlockEquiv (hε : ε ≤ 1) (R : Finset (Fin N)) :
    ctuBlock σ ε R ≃* SU σ (2 * Rᶜ.card + ε) :=
  MulEquiv.ofBijective (unitaryBlockHom σ (ctuaIdx_injective R) (ctuaIdx_rev hε R) _
    fun _ hg => isBlkOn_of_mem_ctuBlock_ctua hg)
    ⟨unitaryBlockHom_injective, fun y => ⟨⟨_, blockExtHom_mem_ctuBlock_ctua hε R y⟩, by
      apply mat_injective
      rw [mat_unitaryBlockHom]
      exact submatrix_blockExt _ _⟩⟩

theorem mat_ctuaBlockEquiv (hε : ε ≤ 1) (R : Finset (Fin N)) (x : ctuBlock σ ε R) :
    mat σ (2 * Rᶜ.card + ε) (ctuaBlockEquiv σ hε R x) =
      (mat σ (2 * N + ε) x).submatrix (ctuaIdx R ε) (ctuaIdx R ε) := rfl

end BlockEquiv

section Ext

variable {F : Type} [Field F] {r n : ℕ} {e : Fin r → Fin n}

@[expose] noncomputable def ctuaBlockGL (he : Function.Injective e) (A : GL (Fin r) F) :
    GL (Fin n) F :=
  ⟨blockExt he (A : Matrix (Fin r) (Fin r) F), blockExt he ((A⁻¹ : GL (Fin r) F) :
    Matrix (Fin r) (Fin r) F),
    by rw [← blockExt_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockExt_one],
    by rw [← blockExt_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blockExt_one]⟩

theorem isBlkOn_map_ctua {M : Matrix (Fin n) (Fin n) F} (hM : IsBlkOn e M) (φ : F ≃+* F) :
    IsBlkOn e (M.map φ) := by
  intro a b hab
  rw [map_apply, hM a b hab]
  by_cases h : a = b
  · subst h
    rw [one_apply_eq, map_one]
  · rw [one_apply_ne h, map_zero]

end Ext

section BlockAut

variable {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem exists_conj_glAut_of_mulAut_ctuBlock (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hε : ε ≤ 1) {R : Finset (Fin N)} (hR : 2 ≤ Rᶜ.card)
    (α : MulAut (ctuBlock (unitaryInvolution F 2 f) ε R)) :
    ∃ (A : GL (Fin (2 * N + ε)) F) (φ : F ≃+* F),
      IsBlkOn (ctuaIdx R ε) (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) ∧
      conjTr (unitaryInvolution F 2 f) (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) *
        antidiag (2 * N + ε) * (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
          antidiag (2 * N + ε) ∧
      ∀ x : ctuBlock (unitaryInvolution F 2 f) ε R,
        ((α x : SU (unitaryInvolution F 2 f) (2 * N + ε)) : GL (Fin (2 * N + ε)) F) =
          A * glAut φ (x : GL (Fin (2 * N + ε)) F) * A⁻¹ := by
  set B := ctuaBlockEquiv (unitaryInvolution F 2 f) hε R with hB
  set α' : MulAut (SU (unitaryInvolution F 2 f) (2 * Rᶜ.card + ε)) := (B.symm.trans α).trans B
    with hα'def
  obtain ⟨A, φ, hA, hα'⟩ := exists_conj_glAut_of_mulAut_SU hF hf (r := 2 * Rᶜ.card + ε)
    (by omega) (by omega) α'
  have he := ctuaIdx_injective (ε := ε) R
  refine ⟨ctuaBlockGL he A, φ, isBlkOn_blockExt he _,
    blockExt_isometry _ he (ctuaIdx_rev hε R) hA, fun x => ?_⟩
  apply Units.ext
  have hx := isBlkOn_of_mem_ctuBlock_ctua x.2
  have hαx := isBlkOn_of_mem_ctuBlock_ctua (α x).2
  have hP : IsBlkOn (ctuaIdx R ε) (blockExt he (A : Matrix (Fin (2 * Rᶜ.card + ε))
      (Fin (2 * Rᶜ.card + ε)) F) * (mat (unitaryInvolution F 2 f) (2 * N + ε) x).map φ) :=
    isBlkOn_mul (isBlkOn_blockExt he _) (isBlkOn_map_ctua hx φ)
  change mat (unitaryInvolution F 2 f) (2 * N + ε) (α x) = blockExt he
    (A : Matrix (Fin (2 * Rᶜ.card + ε)) (Fin (2 * Rᶜ.card + ε)) F) *
      (mat (unitaryInvolution F 2 f) (2 * N + ε) x).map φ * blockExt he
        ((A⁻¹ : GL (Fin (2 * Rᶜ.card + ε)) F) :
          Matrix (Fin (2 * Rᶜ.card + ε)) (Fin (2 * Rᶜ.card + ε)) F)
  refine eq_of_isBlkOn_of_submatrix_eq hαx (isBlkOn_mul hP (isBlkOn_blockExt he _)) ?_
  rw [submatrix_mul_of_isBlkOn he hP, submatrix_mul_of_isBlkOn he (isBlkOn_blockExt he _),
    submatrix_blockExt, submatrix_blockExt, submatrix_map]
  have h1 : B (α x) = α' (B x) := by
    rw [hα'def, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have h2 := congrArg (mat (unitaryInvolution F 2 f) (2 * Rᶜ.card + ε)) h1
  rw [mat_ctuaBlockEquiv] at h2
  rw [h2, mat_apply, hα' (B x), Units.val_mul, Units.val_mul, coe_glAut]
  rfl

end BlockAut

end CFSG.SeitzReduction.SymplecticPilot
