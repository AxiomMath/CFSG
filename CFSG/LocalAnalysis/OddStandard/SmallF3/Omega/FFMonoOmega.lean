module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Mono1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ffMono_commSp_signChange {ι : Type} [Fintype ι] [DecidableEq ι] {c : ZMod 3}
    (fr : NFrame Q ι c) (J : Finset ι) :
    commSp (fr.signChange J) = Submodule.span (ZMod 3) (fr.b '' (J : Set ι)) := by
  ext v
  rw [mem_commSp_iff (fr.signChange_mul_self J), Module.Basis.mem_span_image]
  constructor
  · intro hv i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    by_contra hiJ
    have h1 : fr.b.repr (((fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) v) i =
        fr.b.repr (-v) i := by rw [hv]
    rw [fr.repr_signChange J v i, map_neg, Finsupp.neg_apply,
      if_neg (by simpa only [Finset.mem_coe] using hiJ)] at h1
    have h2 : (2 : ZMod 3) * fr.b.repr v i = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp h1
    exact hi ((mul_eq_zero.mp h2).resolve_left (by decide))
  · intro hsupp
    apply fr.b.repr.injective
    ext i
    rw [fr.repr_signChange J v i, map_neg, Finsupp.neg_apply]
    by_cases hiJ : i ∈ J
    · simp [hiJ]
    · have h0 : fr.b.repr v i = 0 := by
        by_contra hne
        have hmem : i ∈ ↑(fr.b.repr v).support :=
          Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne)
        exact hiJ (by simpa only [Finset.mem_coe] using hsupp hmem)
      simp [hiJ, h0]

private theorem ffMono_finrank_span_frame {ι : Type} [Fintype ι] [DecidableEq ι] {c : ZMod 3}
    (fr : NFrame Q ι c) (J : Finset ι) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (fr.b '' (J : Set ι))) = J.card := by
  have hli : LinearIndependent (ZMod 3) (fun i : J => fr.b (i : ι)) :=
    fr.b.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun i : J => fr.b (i : ι)) = fr.b '' (J : Set ι) := by
    rw [show Set.range (fun i : J => fr.b (i : ι)) = Set.range (fr.b ∘ Subtype.val) from rfl,
      Set.range_comp, Subtype.range_coe]
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_coe]

theorem ffMono_invDim_signChange {c : ZMod 3} (fr : NFrame Q (Fin 6) c) (K : Finset (Fin 6)) :
    invDim (fr.signChange K) = K.card := by
  simp only [invDim]
  rw [ffMono_commSp_signChange fr K]
  exact ffMono_finrank_span_frame fr K

private theorem ffMono_signChange_single_eq_reflection (fr : NFrame Q (Fin 6) 1) (i : Fin 6)
    [Invertible (Q (fr.b i))] :
    fr.signChange {i} = TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.b i) := by
  apply Subtype.ext
  apply fr.b.ext'
  intro j
  rw [fr.signChange_basis {i} j, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  by_cases hji : j = i
  · subst hji
    rw [TauCeti.QuadraticMap.reflection_apply_self]
    simp
  · rw [if_neg (by simpa [Finset.mem_singleton] using hji),
      TauCeti.QuadraticMap.reflection_apply, fr.orth i j (Ne.symm hji), mul_zero, zero_smul,
      sub_zero]

theorem ffMono_detSpinor_signChange_single (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (i : Fin 6) :
    detSpinorNorm hQ (fr.signChange {i}) =
      ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
  haveI : Invertible (Q (fr.b i)) := invertibleOfNonzero (by rw [fr.norm i]; exact one_ne_zero)
  rw [ffMono_signChange_single_eq_reflection fr i, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q (fr.b i)) = 1 :=
    Units.ext (by rw [val_unitOfInvertible, fr.norm i]; rfl)
  rw [hunit, map_one]

theorem ffMono_detSpinor_signChange (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (K : Finset (Fin 6)) :
    detSpinorNorm hQ (fr.signChange K) =
      (((-1 : (ZMod 3)ˣ) ^ K.card), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    rw [fr.signChange_empty, map_one, Finset.card_empty, pow_zero]
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
    rw [hprod, map_mul, ffMono_detSpinor_signChange_single hQ fr i, ih,
      Finset.card_insert_of_notMem hi, pow_succ', Prod.mk_mul_mk]
    simp

private lemma ffMono_Q_sub (fr : NFrame Q (Fin 6) 1) {a b : Fin 6} (hab : a ≠ b) :
    Q (fr.b a - fr.b b) = -1 := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
    QuadraticMap.polar_neg_right, fr.norm a, fr.norm b, fr.orth a b hab, neg_zero, add_zero]
  decide

private lemma ffMono_polar_sub_left (fr : NFrame Q (Fin 6) 1) {a b : Fin 6} (hab : a ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b a) = -1 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self,
    QuadraticMap.polar_comm Q (fr.b b) (fr.b a), fr.norm a, fr.orth a b hab]
  decide

private lemma ffMono_polar_sub_right (fr : NFrame Q (Fin 6) 1) {a b : Fin 6} (hab : a ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b b) = 1 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self, fr.norm b, fr.orth a b hab]
  decide

private lemma ffMono_polar_sub_of_ne (fr : NFrame Q (Fin 6) 1) {a b c : Fin 6}
    (hca : c ≠ a) (hcb : c ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b c) = 0 := by
  rw [QuadraticMap.polar_sub_left, fr.orth a c hca.symm, fr.orth b c hcb.symm]
  decide

private theorem ffMono_swap_eq_reflection (fr : NFrame Q (Fin 6) 1) {a b : Fin 6} (hab : a ≠ b)
    [Invertible (Q (fr.b a - fr.b b))] :
    fr.permOrth (Equiv.swap a b) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.b a - fr.b b) := by
  have hQv := ffMono_Q_sub fr hab
  apply Subtype.ext
  apply fr.b.ext'
  intro c
  rw [fr.permOrth_basis (Equiv.swap a b) c, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    TauCeti.QuadraticMap.reflection_apply_eq_sub_div, hQv]
  by_cases hca : c = a
  · subst hca
    rw [Equiv.swap_apply_left, ffMono_polar_sub_left fr hab]
    have hcoeff : (-1 : ZMod 3) / (-1) = 1 := by
      rw [div_eq_mul_inv, inv_neg, inv_one, mul_neg, mul_one, neg_neg]
    rw [hcoeff, one_smul]
    abel
  · by_cases hcb : c = b
    · subst hcb
      rw [Equiv.swap_apply_right, ffMono_polar_sub_right fr hab]
      have hcoeff : (1 : ZMod 3) / (-1) = -1 := by
        rw [div_eq_mul_inv, inv_neg, inv_one, mul_neg, mul_one]
      rw [hcoeff, neg_one_smul]
      abel
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb, ffMono_polar_sub_of_ne fr hca hcb,
        zero_div, zero_smul, sub_zero]

theorem ffMono_detSpinor_swap (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) {i j : Fin 6}
    (hij : i ≠ j) :
    detSpinorNorm hQ (fr.permOrth (Equiv.swap i j)) =
      ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  haveI : Invertible (Q (fr.b i - fr.b j)) :=
    invertibleOfNonzero (by rw [ffMono_Q_sub fr hij]; exact neg_ne_zero.mpr one_ne_zero)
  rw [ffMono_swap_eq_reflection fr hij, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q (fr.b i - fr.b j)) = (-1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, ffMono_Q_sub fr hij]; rfl)
  rw [hunit, squareClassHom_apply]

private theorem ffMono_prod_mul_self
    (a : (ZMod 3)ˣ × Multiplicative (SquareClassGroup (ZMod 3))) : a * a = 1 := by
  obtain ⟨u, b⟩ := a
  refine Prod.ext ?_ ?_
  · show u * u = 1
    rcases aux_units_zmod3 u with h | h <;> rw [h] <;> decide
  · show b * b = 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    have h : (2 : ℕ) • Multiplicative.toAdd b = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 (Multiplicative.toAdd b),
        CharP.cast_eq_zero (ZMod 2) 2, zero_smul]
    simpa [two_nsmul] using h

theorem ffMono_detSpinor_permOrth (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : Equiv.Perm (Fin 6)) :
    detSpinorNorm hQ (fr.permOrth σ) =
      if Equiv.Perm.sign σ = 1 then 1
      else ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    rw [fr.permOrth_one, map_one, Equiv.Perm.sign_one]
    simp
  | swap_mul τ a b hab ih =>
    rw [fr.permOrth_mul, map_mul, ffMono_detSpinor_swap hQ fr hab, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hab]
    by_cases hs : Equiv.Perm.sign τ = 1
    · rw [ih, hs, if_pos rfl,
        if_neg (by decide : (-1 : ℤˣ) * (1 : ℤˣ) ≠ 1), mul_one]
    · have hs' : Equiv.Perm.sign τ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
        · exact absurd h hs
        · exact h
      rw [ih, hs', if_neg (by decide : (-1 : ℤˣ) ≠ 1),
        if_pos (by decide : (-1 : ℤˣ) * (-1) = 1), ffMono_prod_mul_self]

theorem ffMono_mem_omega_iff (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)) :
    fr.permOrth σ * fr.signChange K ∈ omegaGroup hQ ↔
      σ ∈ alternatingGroup (Fin 6) ∧ Even K.card := by
  rw [mem_omegaGroup_iff hQ, map_mul, ffMono_detSpinor_permOrth hQ fr σ,
    ffMono_detSpinor_signChange hQ fr K, Equiv.Perm.mem_alternatingGroup]
  by_cases hs : Equiv.Perm.sign σ = 1
  · rw [if_pos hs, one_mul, hs]
    simp only [eq_self_iff_true, true_and]
    constructor
    · intro h
      exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)).mp
        (Prod.ext_iff.mp h).1
    · intro hK
      rw [Prod.ext_iff]
      exact ⟨(neg_one_pow_eq_one_iff_even (by decide)).mpr hK, rfl⟩
  · rw [if_neg hs]
    constructor
    · intro h
      have h2 : Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ)) = 1 := by
        have := (Prod.ext_iff.mp h).2
        simpa using this
      exact absurd h2 aux_squareClass_neg_one_ne_zero
    · rintro ⟨hs', -⟩
      exact absurd hs' hs

end CFSG.OddStandard.SmallF3.Omega
