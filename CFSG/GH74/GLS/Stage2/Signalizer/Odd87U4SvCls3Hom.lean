module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowHom
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open scoped MatrixGroups

section Hom

variable {p f : ℕ} {K : Type} [Field K]

structure U4Frame (h : UnitaryFieldData p f K) (A : GL (HypIndex 2 0) K)
    (E : Matrix (HypIndex 2 0) (Fin 4) K) (d : Fin 4 → h.fixedField) : Prop where
  ne : ∀ i, d i ≠ 0
  gram : (E.map h.bar)ᵀ * hypGram 2 0 K * E = Matrix.diagonal fun i => (d i : K)
  fixed : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ (fun a => h.bar (E a i)) =
    fun a => E a i

variable {h : UnitaryFieldData p f K} {A : GL (HypIndex 2 0) K}
  {E : Matrix (HypIndex 2 0) (Fin 4) K} {d : Fin 4 → h.fixedField}

@[expose] noncomputable def U4Frame.gi (h : UnitaryFieldData p f K) (d : Fin 4 → h.fixedField) :
    Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal fun i => ((d i : h.fixedField) : K)⁻¹

@[expose] noncomputable def U4Frame.fm (h : UnitaryFieldData p f K) (E : Matrix (HypIndex 2 0) (Fin 4) K)
    (d : Fin 4 → h.fixedField) : Matrix (Fin 4) (HypIndex 2 0) K :=
  U4Frame.gi h d * (E.map h.bar)ᵀ * hypGram 2 0 K

theorem U4Frame.gi_mul_gram (fr : U4Frame h A E d) :
    U4Frame.gi h d * ((E.map h.bar)ᵀ * hypGram 2 0 K * E) = 1 := by
  rw [fr.gram, U4Frame.gi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (fun h0 => fr.ne i (Subtype.ext h0))

theorem U4Frame.gram_mul_gi (fr : U4Frame h A E d) :
    ((E.map h.bar)ᵀ * hypGram 2 0 K * E) * U4Frame.gi h d = 1 := by
  rw [fr.gram, U4Frame.gi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (fun h0 => fr.ne i (Subtype.ext h0))

theorem U4Frame.fm_mul_E (fr : U4Frame h A E d) : U4Frame.fm h E d * E = 1 := by
  rw [U4Frame.fm, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (E.map h.bar)ᵀ,
    ← Matrix.mul_assoc (U4Frame.gi h d)]
  simpa [Matrix.mul_assoc] using fr.gi_mul_gram

theorem U4Frame.E_mul_fm (fr : U4Frame h A E d) : E * U4Frame.fm h E d = 1 := by
  have hcard : Fintype.card (HypIndex 2 0) = Fintype.card (Fin 4) := by
    simp [HypIndex]
  exact (Matrix.mul_eq_one_comm_of_card_eq (HypIndex 2 0) (Fin 4) K hcard).mpr fr.fm_mul_E

theorem hypGram_map_bar (h : UnitaryFieldData p f K) :
    (hypGram 2 0 K).map h.bar = hypGram 2 0 K := by
  ext a b
  rw [Matrix.map_apply, hypGram_apply]
  split_ifs <;> simp

theorem U4Frame.A_mul_conj_E (fr : U4Frame h A E d) :
    (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * E.map h.bar = E := by
  ext a i
  have := congrFun (fr.fixed i) a
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply] using this

theorem U4Frame.map_fm (_fr : U4Frame h A E d) :
    (U4Frame.fm h E d).map h.bar = U4Frame.gi h d * Eᵀ * hypGram 2 0 K := by
  have hgi : (U4Frame.gi h d).map h.bar = U4Frame.gi h d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [U4Frame.gi, h.mem_fixedField.mp (d i).2, map_inv₀]
    · simp [U4Frame.gi, hij]
  rw [U4Frame.fm, Matrix.map_mul, Matrix.map_mul, hgi, Matrix.transpose_map,
    OddUnitaryInvolutionSylow.map_map_of_involutive h.bar_bar, hypGram_map_bar]

theorem U4Frame.fm_mul_A (fr : U4Frame h A E d) (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1) :
    U4Frame.fm h E d * (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      U4Frame.gi h d * Eᵀ * hypGram 2 0 K := by
  have hAA' : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (HypIndex 2 0) (HypIndex 2 0) K rfl).mp hAA
  have hE : E.map h.bar = (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar * E := by
    calc E.map h.bar = ((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar *
          (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) * E.map h.bar := by
            rw [hAA', Matrix.one_mul]
      _ = (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar * E := by
          rw [Matrix.mul_assoc, fr.A_mul_conj_E]
  have hU := mem_hypUnitary.mp hA
  calc U4Frame.fm h E d * (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      = U4Frame.gi h d * (E.map h.bar)ᵀ * hypGram 2 0 K *
          (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := rfl
    _ = U4Frame.gi h d * ((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar * E)ᵀ *
          hypGram 2 0 K * (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by rw [hE]
    _ = U4Frame.gi h d * Eᵀ * (((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar)ᵀ *
          hypGram 2 0 K * (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = U4Frame.gi h d * Eᵀ * hypGram 2 0 K := by rw [hU]

theorem U4Frame.suppMat_eq (fr : U4Frame h A E d) (Y : Matrix (Fin 4) (Fin 4) K) :
    suppMat E (U4Frame.fm h E d) Y = E * Y * U4Frame.fm h E d := by
  have hEF := fr.E_mul_fm
  rw [suppMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hEF]
  abel

theorem U4Frame.exists_hom_of_emb (fr : U4Frame h A E d) (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1)
    {emb : Matrix (Fin 3) (Fin 3) K → Matrix (Fin 4) (Fin 4) K}
    (hmul : ∀ M N, emb (M * N) = emb M * emb N) (hone : emb 1 = 1)
    (hdet : ∀ M, (emb M).det = M.det) (hbar : ∀ M, (emb M).map h.bar = emb (M.map h.bar))
    (e : Fin 3 → K)
    (hiso : ∀ M : Matrix (Fin 3) (Fin 3) K,
      Mᵀ * Matrix.diagonal e * M = Matrix.diagonal e →
      (emb M)ᵀ * Matrix.diagonal (fun i => ((d i : h.fixedField) : K)) * emb M =
        Matrix.diagonal (fun i => ((d i : h.fixedField) : K)))
    {H : Type} [Group H] (Y3 : H →* Matrix (Fin 3) (Fin 3) K)
    (hY3bar : ∀ S, (Y3 S).map h.bar = Y3 S) (hY3det : ∀ S, (Y3 S).det = 1)
    (hY3iso : ∀ S, (Y3 S)ᵀ * Matrix.diagonal e * Y3 S = Matrix.diagonal e) :
    ∃ ψ : H →* ↥(hypSU h 2 0),
      (∀ S, ((ψ S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        E * emb (Y3 S) * U4Frame.fm h E d) ∧
      (∀ S, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((ψ S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
          ((ψ S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
  classical
  let Y : H →* Matrix (Fin 4) (Fin 4) K :=
    { toFun := fun S => emb (Y3 S)
      map_one' := by rw [map_one, hone]
      map_mul' := fun S T => by rw [map_mul, hmul] }
  have hYbar : ∀ S, (Y S).map h.bar = Y S := by
    intro S
    show (emb _).map h.bar = emb _
    rw [hbar, hY3bar]
  have hY : ∀ S, ((Y S).map h.bar)ᵀ * ((E.map h.bar)ᵀ * hypGram 2 0 K * E) * Y S =
      (E.map h.bar)ᵀ * hypGram 2 0 K * E := by
    intro S
    rw [hYbar, fr.gram]
    exact hiso _ (hY3iso S)
  have hYd : ∀ S, (Y S).det = 1 := by
    intro S
    show (emb _).det = 1
    rw [hdet, hY3det]
  obtain ⟨ψ, hψ⟩ := exists_hypSU_hom h fr.gi_mul_gram fr.gram_mul_gi Y hY hYd
  have hψ' : ∀ S, ((ψ S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      E * Y S * U4Frame.fm h E d := fun S => by
    rw [hψ S]
    exact fr.suppMat_eq (Y S)
  refine ⟨ψ, fun S => hψ' S, fun S => ?_⟩
  have hbarψ : ((ψ S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
      suppMat (E.map h.bar) (U4Frame.gi h d * Eᵀ * hypGram 2 0 K) (Y S) := by
    rw [hψ S, suppMat_map, ← fr.map_fm, hYbar]
    rfl
  rw [hbarψ, hψ S]
  exact mul_suppMat (E := E) (F := U4Frame.fm h E d) (D := 1) (M := Y S) (M' := Y S)
    (by rw [Matrix.mul_one]; exact fr.A_mul_conj_E) (by rw [Matrix.one_mul]; exact fr.fm_mul_A hA hAA)
    (by rw [Matrix.one_mul, Matrix.mul_one])

end Hom

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
