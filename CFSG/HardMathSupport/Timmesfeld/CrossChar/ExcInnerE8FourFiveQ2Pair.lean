module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyStep

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false



section Field4

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem exists_subfield_four :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra K L), Nat.card K = 4 ∧
      ∀ c : L, c ∈ Set.range (algebraMap K L) ↔ c ^ 4 = c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfin, hcard⟩ := ncard_pow_eq_self (L := L) 2 2 (by norm_num)
  let K : Subfield L := (iterateFrobenius L 2 2).eqLocusField (RingHom.id L)
  have hset : (K : Set L) = {c : L | c ^ (2 ^ 2) = c} := by
    ext c
    change iterateFrobenius L 2 2 c = c ↔ _
    rw [iterateFrobenius_def]
    rfl
  have hfinK : Finite K := by
    have h1 : (K : Set L).Finite := by rw [hset]; exact hfin
    exact h1.to_subtype
  refine ⟨K, inferInstance, hfinK, inferInstance, ?_, fun c => ?_⟩
  · have h1 : Nat.card K = (K : Set L).ncard := Nat.card_coe_set_eq (K : Set L)
    rw [h1, hset, hcard]
    norm_num
  · constructor
    · rintro ⟨x, rfl⟩
      have hx : (x : L) ∈ (K : Set L) := x.2
      rw [hset] at hx
      exact hx
    · intro h
      have hc : c ∈ (K : Set L) := by rw [hset]; exact h
      exact ⟨⟨c, hc⟩, rfl⟩

end Field4


section PMat

variable {L : Type} [Field L] [CharP L 2]

theorem two_eq_zero_L : (2 : L) = 0 := CharTwo.two_eq_zero

theorem det_Pmat_ne_zero {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (h1 : ζ ≠ 1) :
    (!![1, (ζ : L) ^ 4; 1, (ζ : L)] : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  intro h
  have h5' : (ζ : L) ^ 5 = 1 := by simpa using congrArg Units.val h5
  have hne : (ζ : L) ≠ 0 := ζ.ne_zero
  have h2 : (2 : L) = 0 := two_eq_zero_L
  have h3 : (ζ : L) ^ 3 = 1 := by
    have : (ζ : L) * ((ζ : L) ^ 3 - 1) = 0 := by linear_combination (-1 : L) * h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hne
    · exact sub_eq_zero.1 h0
  have hz2 : (ζ : L) ^ 2 = 1 := by
    have : (ζ : L) ^ 5 = (ζ : L) ^ 3 * (ζ : L) ^ 2 := by ring
    rw [h5', h3, one_mul] at this
    exact this.symm
  have : ((ζ : L) - 1) * ((ζ : L) - 1) = 0 := by linear_combination hz2 + (1 - (ζ : L)) * h2
  exact h1 (Units.ext (sub_eq_zero.1 (mul_self_eq_zero.1 this)))

@[expose] noncomputable def Pmat {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (h1 : ζ ≠ 1) : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, (ζ : L) ^ 4; 1, (ζ : L)] (det_Pmat_ne_zero h5 h1)

theorem coe_Pmat {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (h1 : ζ ≠ 1) :
    ((Pmat h5 h1 : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, (ζ : L) ^ 4; 1, (ζ : L)] :=
  rfl

theorem swap_mul_glMap_Pmat {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (h1 : ζ ≠ 1) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ 2) :
    (swapGL : GL (Fin 2) L) * Matrix.GeneralLinearGroup.map (Fr.comp Fr) (Pmat h5 h1) =
      Pmat h5 h1 := by
  have h5' : (ζ : L) ^ 5 = 1 := by simpa using congrArg Units.val h5
  have hFF : ∀ c, (Fr.comp Fr) c = c ^ 4 := fun c => by
    simp only [RingHom.comp_apply, hFr, ← pow_mul]
  apply Units.ext
  rw [Units.val_mul, coe_swapGL, coe_Pmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, Matrix.mul_apply, Fin.sum_univ_two, coe_Pmat]
  · rw [hFr, hFr]; ring
  · rw [hFr, hFr]
    have : (((ζ : L) ^ 2) ^ 2) ^ 4 = ((ζ : L) ^ 5) ^ 3 * (ζ : L) := by ring
    rw [this, h5']; simp

end PMat


section HSLmem

variable {L : Type} [Field L] [CharP L 2]

@[expose] noncomputable def Cmat (ζ : Lˣ) : SL2 L :=
  ⟨!![(ζ : L) + (ζ : L) ^ 4, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : L) * (two_eq_zero_L (L := L))⟩

theorem coe_Cmat (ζ : Lˣ) :
    ((Cmat ζ : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![(ζ : L) + (ζ : L) ^ 4, 1; 1, 0] := rfl

theorem conjSL_Pmat_Cmat {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (h1 : ζ ≠ 1) :
    conjSL (Pmat h5 h1) (Cmat ζ) = HSL ζ := by
  have h5' : (ζ : L) ^ 5 = 1 := by simpa using congrArg Units.val h5
  have hinv : ((ζ⁻¹ : Lˣ) : L) = (ζ : L) ^ 4 := by
    have : ζ⁻¹ = ζ ^ 4 := by
      rw [inv_eq_iff_eq_inv]
      refine (inv_eq_of_mul_eq_one_right ?_).symm
      rw [← pow_succ, h5]
    rw [this]; simp
  have h2 : (2 : L) = 0 := two_eq_zero_L
  apply conjSL_eq_of
  rw [coe_Pmat, coe_Cmat, coe_HSL, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination ((ζ : L) ^ 4) * h2
  · linear_combination (-1 : L) * h5'
  · linear_combination (ζ : L) * h2
  · linear_combination (-1 : L) * h5'

theorem Cmat_pow_four (ζ : Lˣ) (h5 : (ζ : L) ^ 5 = 1) :
    ((ζ : L) + (ζ : L) ^ 4) ^ 4 = (ζ : L) + (ζ : L) ^ 4 := by
  have h2 : (2 : L) = 0 := two_eq_zero_L
  linear_combination ((ζ : L) * ((ζ : L) ^ 10 + (ζ : L) ^ 5 + 1)) * h5 +
    (2 * (ζ : L) ^ 7 + 3 * (ζ : L) ^ 10 + 2 * (ζ : L) ^ 13) * h2

end HSLmem


section HSLmem2

variable {L : Type} [Field L] [CharP L 2] {K₂ : Type} [Field K₂] [Algebra K₂ L]

theorem HSL_mem_conj_range
    (hK : ∀ c : L, c ∈ Set.range (algebraMap K₂ L) ↔ c ^ 4 = c) {ζ : Lˣ} (h5 : ζ ^ 5 = 1)
    (h1 : ζ ≠ 1) :
    HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₂ L)).range.map (conjSL (Pmat h5 h1)) := by
  have h5' : (ζ : L) ^ 5 = 1 := by simpa using congrArg Units.val h5
  obtain ⟨t, ht⟩ := (hK _).2 (Cmat_pow_four ζ h5')
  have h2K : (2 : K₂) = 0 := by
    have h2L : (2 : L) = 0 := two_eq_zero_L
    refine (algebraMap K₂ L).injective ?_
    rw [map_zero, map_ofNat]
    exact h2L
  let B : SL2 K₂ := ⟨!![t, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : K₂) * h2K⟩
  refine ⟨Cmat ζ, ⟨B, ?_⟩, conjSL_Pmat_Cmat h5 h1⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_Cmat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B, ht]

end HSLmem2

end CFSG.HardMathSupport.Timmesfeld.CrossChar
