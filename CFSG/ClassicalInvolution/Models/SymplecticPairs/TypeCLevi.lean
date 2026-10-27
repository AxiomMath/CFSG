module

public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (mem_closure_sl2)
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_equiv_leviHom)
open CFSG.ClassicalInvolution.WeakCT (B12 B23 blockSL coe_blockSL LinearBlockStandardPair)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

section Levi

variable (K n) in
@[expose] noncomputable def leviEmbedGL : GL (Fin n) K →* StatedSp n K :=
  (equivStatedSp n K).toMonoidHom.comp TauCeti.GLSymplecticFin.leviHom

theorem mat_leviEmbedGL (A : GL (Fin n) K) :
    mat n K (leviEmbedGL K n A) = fromBlocks (A : Matrix (Fin n) (Fin n) K) 0 0
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ :=
  mat_equiv_leviHom A

variable (K n) in
@[expose] noncomputable def leviEmbedSL : SL(n, K) →* StatedSp n K :=
  (leviEmbedGL K n).comp Matrix.SpecialLinearGroup.toGL

theorem mat_leviEmbedSL (A : SL(n, K)) :
    mat n K (leviEmbedSL K n A) = fromBlocks (A : Matrix (Fin n) (Fin n) K) 0 0
      ((A⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K)ᵀ := by
  rw [leviEmbedSL, MonoidHom.comp_apply, mat_leviEmbedGL]
  rfl

theorem leviEmbedSL_injective : Function.Injective (leviEmbedSL K n) := by
  intro A B h
  have := congrArg (mat n K) h
  rw [mat_leviEmbedSL, mat_leviEmbedSL, Matrix.fromBlocks_inj] at this
  exact Subtype.ext this.1

theorem leviEmbedSL_comp_blockSL_zero :
    (leviEmbedSL K 3).comp (blockSL K 3 2 0 (by omega)) =
      shortBlock K (show (0 : Fin 3) ≠ 1 by decide) := by
  refine MonoidHom.ext fun A => mat_injective ?_
  rw [MonoidHom.comp_apply, mat_leviEmbedSL, mat_shortBlock]
  have h1 : ((blockSL K 3 2 0 (by omega) A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      CFSG.LieType.Steinberg.Sp.blockMat (0 : Fin 3) 1 (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [coe_blockSL]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [CFSG.ClassicalInvolution.Phan.blockMat_apply, CFSG.LieType.Steinberg.Sp.blockMat]
  have h2 : ((blockSL K 3 2 0 (by omega) A⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      CFSG.LieType.Steinberg.Sp.blockMat (0 : Fin 3) 1
        ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
    rw [coe_blockSL]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [CFSG.ClassicalInvolution.Phan.blockMat_apply, CFSG.LieType.Steinberg.Sp.blockMat]
  rw [← h1, ← h2, ← map_inv]

theorem leviEmbedSL_comp_blockSL_one :
    (leviEmbedSL K 3).comp (blockSL K 3 2 1 (by omega)) =
      shortBlock K (show (1 : Fin 3) ≠ 2 by decide) := by
  refine MonoidHom.ext fun A => mat_injective ?_
  rw [MonoidHom.comp_apply, mat_leviEmbedSL, mat_shortBlock]
  have h1 : ((blockSL K 3 2 1 (by omega) A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      CFSG.LieType.Steinberg.Sp.blockMat (1 : Fin 3) 2 (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [coe_blockSL]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [CFSG.ClassicalInvolution.Phan.blockMat_apply, CFSG.LieType.Steinberg.Sp.blockMat]
  have h2 : ((blockSL K 3 2 1 (by omega) A⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      CFSG.LieType.Steinberg.Sp.blockMat (1 : Fin 3) 2
        ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
    rw [coe_blockSL]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [CFSG.ClassicalInvolution.Phan.blockMat_apply, CFSG.LieType.Steinberg.Sp.blockMat]
  rw [← h1, ← h2, ← map_inv]

end Levi

section Embed

theorem spEmbed_comp_shortBlock_of_injective {m : ℕ} {σ : Fin m → Fin n}
    (hσ : Function.Injective σ) {a b : Fin m} (hab : a ≠ b) :
    (spEmbed σ hσ).comp (shortBlock K hab) = shortBlock K (fun h => hab (hσ h)) := by
  refine MonoidHom.ext fun A => ?_
  have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
      MonoidHom.eqLocus ((spEmbed σ hσ).comp (shortBlock K hab))
        (shortBlock K (fun h => hab (hσ h))) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show (spEmbed σ hσ).comp (shortBlock K hab) (sl2Upper c) =
        shortBlock K (fun h => hab (hσ h)) (sl2Upper c)
      rw [MonoidHom.comp_apply, shortBlock_sl2Upper, shortBlock_sl2Upper, spEmbed_elt_difference]
    · show (spEmbed σ hσ).comp (shortBlock K hab) (sl2Lower c) =
        shortBlock K (fun h => hab (hσ h)) (sl2Lower c)
      rw [MonoidHom.comp_apply, shortBlock_sl2Lower, shortBlock_sl2Lower, spEmbed_elt_difference]
  exact hle (mem_closure_sl2 A)

end Embed

section Triple

variable {i j k : Fin n}

@[expose] def tripleMap (i j k : Fin n) : Fin 3 → Fin n := ![i, j, k]

theorem tripleMap_injective (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Function.Injective (tripleMap i j k) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [tripleMap]

variable (K) in
@[expose] noncomputable def leviSL3 (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    SL(3, K) →* StatedSp n K :=
  (spEmbed (tripleMap i j k) (tripleMap_injective hij hjk hik)).comp (leviEmbedSL K 3)

theorem leviSL3_injective (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Function.Injective (leviSL3 K hij hjk hik) :=
  (spEmbed_injective (tripleMap_injective hij hjk hik)).comp leviEmbedSL_injective

theorem leviSL3_comp_blockSL_zero (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (leviSL3 K hij hjk hik).comp (blockSL K 3 2 0 (by omega)) = shortBlock K hij := by
  rw [leviSL3, MonoidHom.comp_assoc, leviEmbedSL_comp_blockSL_zero]
  exact spEmbed_comp_shortBlock_of_injective (tripleMap_injective hij hjk hik) _

theorem leviSL3_comp_blockSL_one (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (leviSL3 K hij hjk hik).comp (blockSL K 3 2 1 (by omega)) = shortBlock K hjk := by
  rw [leviSL3, MonoidHom.comp_assoc, leviEmbedSL_comp_blockSL_one]
  exact spEmbed_comp_shortBlock_of_injective (tripleMap_injective hij hjk hik) _

theorem linearBlockStandardPair_shortBlock (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    LinearBlockStandardPair K (leviSL3 K hij hjk hik).range (shortBlock K hij).range
      (shortBlock K hjk).range := by
  refine ⟨leviSL3 K hij hjk hik, 1, rfl, ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).2 (leviSL3_injective hij hjk hik)]
    exact bot_le
  · rw [map_conj_one, B12, ← MonoidHom.range_comp, leviSL3_comp_blockSL_zero]
  · rw [map_conj_one, B23, ← MonoidHom.range_comp, leviSL3_comp_blockSL_one]

end Triple

end CFSG.ClassicalInvolution.Models.SymplecticPairs
