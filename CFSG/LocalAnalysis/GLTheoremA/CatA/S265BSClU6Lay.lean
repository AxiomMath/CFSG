module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
open CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (IsGood)
open Matrix
open CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

private theorem exists_perm_four_five {k k' : Fin 6} (hk : k ≠ k') :
    ∃ σ : Equiv.Perm (Fin 6), σ 4 = k ∧ σ 5 = k' := by
  obtain ⟨u, hu⟩ : ∃ u, u = Equiv.swap 4 k k' := ⟨_, rfl⟩
  have hu4 : u ≠ 4 := by
    intro h4
    apply hk
    have e := congrArg (Equiv.swap 4 k) h4
    rw [hu, Equiv.swap_apply_self, Equiv.swap_apply_left] at e
    exact e.symm
  refine ⟨Equiv.swap 4 k * Equiv.swap 5 u, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hu4.symm,
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hu, Equiv.swap_apply_self]

private theorem unitaryPermGL_mem_six {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)
    (π : Equiv.Perm (Fin 6)) :
    (CFSG.RankThree.Classical.unitaryPermGL π : GL (Fin 6) K) ∈
      primeFormUnitary h (idGram K 6) := by
  have hmap : (π.permMatrix K).map h.bar = π.permMatrix K := Matrix.ext fun a b => by
    rw [Matrix.map_apply, CFSG.RankThree.Classical.permMatrix_apply']
    split_ifs <;> simp
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  rw [CFSG.RankThree.Classical.coe_unitaryPermGL, hmap, Matrix.transpose_permMatrix,
    ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

private theorem permMatrix_conj_diag_six {K : Type} [Field K] (σ : Equiv.Perm (Fin 6))
    (t : Fin 6 → K) : σ.permMatrix K * diagonal t * (σ⁻¹).permMatrix K = diagonal (t ∘ σ) := by
  rw [Equiv.Perm.inv_def]
  simp only [Equiv.Perm.permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm,
    Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp,
    Matrix.submatrix_diagonal_equiv]

variable {K : Type} [Field K] [CharP K 2] [Finite K]

private theorem glaPLayer_ne_bot_of_frame_six (h : UnitaryFieldData 2 1 K) {ζ ω : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hω : ω ^ 2 + ω + 1 = 0) {D X : primeFormUnitary h (idGram K 6)}
    (hD : ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, ζ, 1])
    (hX : ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, 1, ω]) :
    GLAPLayer 3 (fixSubgroup (primeFormConjHom h (idGram K 6) D) ⊓
      fixSubgroup (primeFormConjHom h (idGram K 6) X)) ≠ ⊥ := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ω ^ m = ζ := by
    have e : (ζ - ω) * (ζ - ω ^ 2) = 0 := by linear_combination hζ + (ω - 1 - ζ) * hω
    rcases mul_eq_zero.1 e with e | e
    · exact ⟨1, by rw [pow_one]; exact (sub_eq_zero.1 e).symm⟩
    · exact ⟨2, (sub_eq_zero.1 e).symm⟩
  have hX₀ : (((D * X ^ m : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, ζ, ζ] := by
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hD, hX,
      Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [hm]
  have he₁ : ∀ i : Fin 6, (i : ℕ) < 4 → (![1, 1, 1, 1, ζ, 1] : Fin 6 → K) i = 1 := by
    intro i hi
    fin_cases i
    all_goals first | rfl | exact absurd hi (by decide)
  have he₂ : ∀ i : Fin 6, (i : ℕ) < 4 → (![1, 1, 1, 1, 1, ω] : Fin 6 → K) i = 1 := by
    intro i hi
    fin_cases i
    all_goals first | rfl | exact absurd hi (by decide)
  refine glaPLayer_ne_bot_six h hζ hX₀ ?_ ?_
  · intro p hp
    obtain ⟨hp₁, hp₂⟩ := Subgroup.mem_inf.1 hp
    have hs : primeFormConjHom h (idGram K 6) D * primeFormConjHom h (idGram K 6) X ^ m ∈
        MulAction.stabilizer (MulAut (primeFormP h (idGram K 6))) p :=
      mul_mem (MulAction.mem_stabilizer_iff.2 (mem_fixSubgroup.1 hp₁))
        (pow_mem (MulAction.mem_stabilizer_iff.2 (mem_fixSubgroup.1 hp₂)) m)
    rw [mem_fixSubgroup, map_mul, map_pow]
    exact MulAction.mem_stabilizer_iff.1 hs
  · intro g hg
    exact Subgroup.mem_inf.2 ⟨mk_mem_fixSubgroup_of_block h hD he₁ g hg,
      mk_mem_fixSubgroup_of_block h hX he₂ g hg⟩

theorem glaPLayer_ne_bot_of_diag_pair_six (h : UnitaryFieldData 2 1 K) {ζ ω : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hω : ω ^ 2 + ω + 1 = 0) {D X Q : primeFormUnitary h (idGram K 6)}
    {k k' : Fin 6} (hkk' : k ≠ k')
    (hD : (((Q⁻¹ * D * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal fun i => if i = k then ζ else 1)
    (hX : (((Q⁻¹ * X * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal fun i => if i = k' then ω else 1) :
    GLAPLayer 3 (fixSubgroup (primeFormConjHom h (idGram K 6) D) ⊓
      fixSubgroup (primeFormConjHom h (idGram K 6) X)) ≠ ⊥ := by
  classical
  obtain ⟨σ, hσ4, hσ5⟩ := exists_perm_four_five hkk'
  obtain ⟨P, hP, hPi⟩ : ∃ P : primeFormUnitary h (idGram K 6),
      ((P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = (σ⁻¹).permMatrix K ∧
      (((P⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        σ.permMatrix K :=
    ⟨⟨_, unitaryPermGL_mem_six h σ⁻¹⟩, rfl, by
      show ((σ⁻¹)⁻¹).permMatrix K = σ.permMatrix K
      rw [inv_inv]⟩
  have hconj : ∀ (M : primeFormUnitary h (idGram K 6)) (t : Fin 6 → K),
      ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal t →
      (((P⁻¹ * M * P : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal (t ∘ σ) := fun M t hM => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hM, hP, hPi]
    exact permMatrix_conj_diag_six σ t
  have hpat : ∀ (j k₀ : Fin 6) (c : K), σ j = k₀ →
      ((fun i => if i = k₀ then c else 1) ∘ σ) = fun i => if i = j then c else 1 := by
    intro j k₀ c hj
    subst hj
    funext i
    simp only [Function.comp_apply, σ.injective.eq_iff]
  have h4 : (fun i : Fin 6 => if i = 4 then ζ else 1) = ![1, 1, 1, 1, ζ, 1] := by
    funext i
    fin_cases i <;> simp
  have h5 : (fun i : Fin 6 => if i = 5 then ω else 1) = ![1, 1, 1, 1, 1, ω] := by
    funext i
    fin_cases i <;> simp
  have hD' : ((((Q * P)⁻¹ * D * (Q * P) : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, ζ, 1] := by
    rw [show (Q * P)⁻¹ * D * (Q * P) = P⁻¹ * (Q⁻¹ * D * Q) * P by group, hconj _ _ hD,
      hpat 4 k ζ hσ4, h4]
  have hX' : ((((Q * P)⁻¹ * X * (Q * P) : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, 1, ω] := by
    rw [show (Q * P)⁻¹ * X * (Q * P) = P⁻¹ * (Q⁻¹ * X * Q) * P by group, hconj _ _ hX,
      hpat 5 k' ω hσ5, h5]
  have hc : ∀ Z : primeFormUnitary h (idGram K 6),
      primeFormConjHom h (idGram K 6) (Q * P)⁻¹ * primeFormConjHom h (idGram K 6) Z *
        (primeFormConjHom h (idGram K 6) (Q * P)⁻¹)⁻¹ =
          primeFormConjHom h (idGram K 6) ((Q * P)⁻¹ * Z * (Q * P)) := fun Z => by
    rw [map_mul, map_mul, map_inv, inv_inv]
  refine HDescLinRes.glaPLayer_ne_bot_of_conj Nat.prime_three
    (primeFormConjHom h (idGram K 6) (Q * P)⁻¹) _ _ ?_
  rw [hc, hc]
  exact glaPLayer_ne_bot_of_frame_six h hζ hω hD' hX'

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
