module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PMono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6POmegaAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}


theorem ff6p_detSpinor_signChange_some (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (i : Fin 5) :
    detSpinorNorm hQ (fr.signChange {some i}) =
      ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
  haveI : Invertible (Q (fr.b (some i))) :=
    invertibleOfNonzero (by rw [fr.norm (some i)]; simp only [ffC]; decide)
  rw [ffOutFF6POmega_signChange_single_eq_reflection fr (some i),
    detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q (fr.b (some i))) = 1 :=
    Units.ext (by rw [val_unitOfInvertible, fr.norm (some i)]; rfl)
  rw [hunit, map_one]

theorem ff6p_detSpinor_signChange_none (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    detSpinorNorm hQ (fr.signChange {none}) =
      ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  haveI : Invertible (Q (fr.b none)) :=
    invertibleOfNonzero (by rw [fr.norm none]; decide)
  rw [ffOutFF6POmega_signChange_single_eq_reflection fr none, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q (fr.b none)) = (-1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, fr.norm none]; rfl)
  rw [hunit, squareClassHom_apply]

theorem ff6p_detSpinor_signChange (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    (K : Finset (Option (Fin 5))) :
    detSpinorNorm hQ (fr.signChange K) =
      (((-1 : (ZMod 3)ˣ) ^ K.card),
        if none ∈ K then Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ)) else 1) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    simp [fr.signChange_empty]
    rfl
  | insert i K hi ih =>
    have hsym : symmDiff {i} K = insert i K := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [Finset.mem_symmDiff, hi]
      · simp [Finset.mem_symmDiff, Finset.mem_singleton, hji, hi]
    have hprod : fr.signChange (insert i K) = fr.signChange {i} * fr.signChange K := by
      rw [← hsym, ← fr.signChange_mul]
    rw [hprod, map_mul, ih]
    cases i with
    | none =>
      rw [ff6p_detSpinor_signChange_none hQ fr, Prod.mk_mul_mk,
        Finset.card_insert_of_notMem hi, pow_succ,
        if_pos (Finset.mem_insert_self none K), if_neg hi, mul_one]
      refine Prod.ext ?_ ?_
      · exact mul_comm _ _
      · rfl
    | some j =>
      rw [ff6p_detSpinor_signChange_some hQ fr j, Prod.mk_mul_mk,
        Finset.card_insert_of_notMem hi, pow_succ]
      have hmem : none ∈ insert (some j) K ↔ none ∈ K := by
        rw [Finset.mem_insert]
        exact ⟨fun h => h.resolve_left (fun h' => by cases h'), Or.inr⟩
      refine Prod.ext ?_ ?_
      · exact mul_comm _ _
      · by_cases hK : none ∈ K
        · rw [if_pos hK, if_pos (hmem.mpr hK), one_mul]
        · rw [if_neg hK, if_neg (fun h => hK (hmem.mp h)), one_mul]

theorem ff6p_detSpinor_swap (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {i j : Fin 5} (hij : i ≠ j) :
    detSpinorNorm hQ (fr.pOrth (Equiv.swap i j)) =
      ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  haveI : Invertible (Q (fr.b (some i) - fr.b (some j))) :=
    invertibleOfNonzero (by rw [ffOutFF6POmega_Q_sub fr hij]; exact neg_ne_zero.mpr one_ne_zero)
  rw [ffOutFF6POmega_swap_eq_reflection fr hij, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q (fr.b (some i) - fr.b (some j))) = (-1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, ffOutFF6POmega_Q_sub fr hij]; rfl)
  rw [hunit, squareClassHom_apply]

theorem ff6p_detSpinor_pOrth (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) :
    detSpinorNorm hQ (fr.pOrth σ) =
      if Equiv.Perm.sign σ = 1 then 1
      else ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    rw [fr.pOrth_one, map_one, Equiv.Perm.sign_one]
    simp
  | swap_mul τ a b hab ih =>
    rw [fr.pOrth_mul, map_mul, ff6p_detSpinor_swap hQ fr hab, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hab]
    by_cases hs : Equiv.Perm.sign τ = 1
    · rw [ih, hs, if_pos rfl,
        if_neg (by decide : (-1 : ℤˣ) * (1 : ℤˣ) ≠ 1), mul_one]
    · have hs' : Equiv.Perm.sign τ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
        · exact absurd h hs
        · exact h
      rw [ih, hs', if_neg (by decide : (-1 : ℤˣ) ≠ 1),
        if_pos (by decide : (-1 : ℤˣ) * (-1) = 1), ffOutFF6POmega_prod_mul_self]

theorem ff6p_mem_omega_iff (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) (K : Finset (Option (Fin 5))) :
    fr.pOrth σ * fr.signChange K ∈ omegaGroup hQ ↔
      (none ∈ K ↔ Equiv.Perm.sign σ = -1) ∧ Even (K.erase none).card := by
  rw [mem_omegaGroup_iff hQ, map_mul, ff6p_detSpinor_pOrth hQ fr,
    ff6p_detSpinor_signChange hQ fr]
  set s : Multiplicative (SquareClassGroup (ZMod 3)) :=
    Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ)) with hs_def
  have hs1 : s ≠ 1 := by
    rw [hs_def]
    exact fun h => aux_squareClass_neg_one_ne_zero (Multiplicative.ofAdd.injective h)
  have hsq : s * s = 1 := (Prod.ext_iff.mp (ffOutFF6POmega_prod_mul_self ((1 : (ZMod 3)ˣ), s))).2
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [if_pos hs, hs, one_mul]
    by_cases hn : none ∈ K
    · rw [if_pos hn]
      constructor
      · intro h
        exact absurd (Prod.ext_iff.mp h).2 hs1
      · intro h
        exact absurd (h.1.mp hn) (by decide)
    · rw [if_neg hn, Finset.erase_eq_of_notMem hn]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · exact iff_of_false hn (by decide)
        · exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)).mp
            (Prod.ext_iff.mp h).1
      · rintro ⟨-, hEven⟩
        rw [Prod.ext_iff]
        exact ⟨(neg_one_pow_eq_one_iff_even (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)).mpr hEven,
          rfl⟩
  · have hsne : Equiv.Perm.sign σ ≠ 1 := by rw [hs]; decide
    rw [if_neg hsne, hs]
    by_cases hn : none ∈ K
    · rw [if_pos hn]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · exact iff_of_true hn rfl
        · have h1 : (-1 : (ZMod 3)ˣ) * (-1) ^ K.card = 1 := (Prod.ext_iff.mp h).1
          rw [← Finset.card_erase_add_one hn, ffOutFF6POmega_neg_one_mul_pow_succ] at h1
          exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)).mp h1
      · rintro ⟨-, hEven⟩
        rw [Prod.ext_iff]
        refine ⟨?_, hsq⟩
        show (-1 : (ZMod 3)ˣ) * (-1) ^ K.card = 1
        rw [← Finset.card_erase_add_one hn, ffOutFF6POmega_neg_one_mul_pow_succ]
        exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)).mpr hEven
    · rw [if_neg hn]
      constructor
      · intro h
        exact absurd (by simpa using (Prod.ext_iff.mp h).2) hs1
      · rintro ⟨hiff, -⟩
        exact absurd (hiff.mpr rfl) hn

@[expose] noncomputable def ffHat (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) : OGroup Q :=
  fr.pOrth σ * fr.signChange (if Equiv.Perm.sign σ = 1 then ∅ else {none})

theorem ffHat_mem_omega (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) : ffHat fr σ ∈ omegaGroup hQ := by
  rw [ffHat, ff6p_mem_omega_iff hQ fr σ, ffOutFF6POmega_eps_erase σ]
  constructor
  · by_cases hs : Equiv.Perm.sign σ = 1
    · rw [if_pos hs, hs]
      exact iff_of_false (Finset.notMem_empty none) (by decide)
    · have hs' : Equiv.Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd h hs
        · exact h
      rw [if_neg hs, hs']
      exact iff_of_true (Finset.mem_singleton_self none) rfl
  · simp

theorem ffHat_mul (fr : PFrame Q (Option (Fin 5)) ffC) (σ τ : Equiv.Perm (Fin 5)) :
    ffHat fr σ * ffHat fr τ = ffHat fr (σ * τ) := by
  rw [ffHat, ffHat, ffHat, ffMonoP_mul fr σ τ, ffOutFF6POmega_eps_map σ τ⁻¹, mul_left_cancel_iff,
    fr.signChange_injective.eq_iff]
  exact ffOutFF6POmega_symmDiff_eps σ τ

theorem ffHat_one (fr : PFrame Q (Option (Fin 5)) ffC) : ffHat fr 1 = 1 := by
  rw [ffHat, fr.pOrth_one, Equiv.Perm.sign_one, if_pos rfl, fr.signChange_empty, one_mul]

theorem ffHat_conj_signChange (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5))
    (K : Finset (Option (Fin 5))) :
    ffHat fr σ * fr.signChange K * (ffHat fr σ)⁻¹ =
      fr.signChange (K.map (Equiv.optionCongr σ).toEmbedding) := by
  rw [ffHat]
  exact ffMonoP_conj_signChange fr σ _ K

end CFSG.OddStandard.SmallF3.Omega
