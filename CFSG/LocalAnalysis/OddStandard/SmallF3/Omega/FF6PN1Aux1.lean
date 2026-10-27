module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffOutFF6PN1_symmDiff_erase (K : Finset (Option (Fin 5)))
    (σ : Equiv.Perm (Fin 5)) (h : none ∈ K ↔ Equiv.Perm.sign σ = -1) :
    symmDiff (if Equiv.Perm.sign σ = 1 then (∅ : Finset (Option (Fin 5))) else {none})
      (K.erase none) = K := by
  by_cases hn : none ∈ K
  · have hs : Equiv.Perm.sign σ = -1 := h.mp hn
    rw [if_neg (by rw [hs]; decide)]
    ext x
    by_cases hx : x = none
    · subst hx; simp [Finset.mem_symmDiff, hn]
    · simp [Finset.mem_symmDiff, Finset.mem_erase, hx]
  · have hs : Equiv.Perm.sign σ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · exact h1
      · exact absurd (h.mpr h1) hn
    rw [if_pos hs, ← Finset.bot_eq_empty, bot_symmDiff, Finset.erase_eq_of_notMem hn]

theorem ffOutFF6PN1_hat_inv (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) : (ffHat fr σ)⁻¹ = ffHat fr σ⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [ffHat_mul, mul_inv_cancel, ffHat_one])

theorem ffOutFF6PN1_hat_mem_B0_eq_one (fr : PFrame Q (Option (Fin 5)) ffC)
    {σ : Equiv.Perm (Fin 5)} (h : ffHat fr σ ∈ ffB0p fr) : σ = 1 := by
  obtain ⟨J, -, -, hJ⟩ := (mem_ffB0p_iff fr).mp h
  have h2 : fr.pOrth σ * fr.signChange
      (if Equiv.Perm.sign σ = 1 then ∅ else {none}) = fr.pOrth 1 * fr.signChange J := by
    rw [fr.pOrth_one, one_mul, ← hJ, ffHat]
  exact (ffMonoP_unique fr h2).1

theorem ffOutFF6PN1_conj_mem_B0 (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) {b x : OGroup Q} (hb : b ∈ ffB0p fr) (hx : x ∈ ffB0p fr) :
    (ffHat fr σ * b) * x * (ffHat fr σ * b)⁻¹ ∈ ffB0p fr := by
  obtain ⟨J, hJe, hxJ⟩ := (mem_ffB0p_iff_ffOpt fr).mp hx
  obtain ⟨K, -, -, hbK⟩ := (mem_ffB0p_iff fr).mp hb
  have hb2 : b * b = 1 := by rw [hbK, fr.signChange_mul_self]
  have hinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hcomm : b * fr.signChange (ffOpt J) = fr.signChange (ffOpt J) * b := by
    rw [hbK, fr.signChange_comm]
  have hbconj : b * fr.signChange (ffOpt J) * b⁻¹ = fr.signChange (ffOpt J) := by
    rw [hinv, hcomm, mul_assoc, hb2, mul_one]
  have hconj : (ffHat fr σ * b) * fr.signChange (ffOpt J) * (ffHat fr σ * b)⁻¹ =
      fr.signChange (ffOpt (ffAct σ J)) := by
    calc (ffHat fr σ * b) * fr.signChange (ffOpt J) * (ffHat fr σ * b)⁻¹
        = ffHat fr σ * (b * fr.signChange (ffOpt J) * b⁻¹) * (ffHat fr σ)⁻¹ := by group
      _ = ffHat fr σ * fr.signChange (ffOpt J) * (ffHat fr σ)⁻¹ := by rw [hbconj]
      _ = fr.signChange (ffOpt (ffAct σ J)) := ffHat_conj_signChange_ffOpt fr σ J
  rw [hxJ, hconj]
  exact (mem_ffB0p_iff_ffOpt fr).mpr ⟨ffAct σ J, by rw [ffAct_card]; exact hJe, rfl⟩

theorem ffOutFF6PN1_inv_hat_mul (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) (J : Finset (Fin 5)) :
    (ffHat fr σ * fr.signChange (ffOpt J))⁻¹ =
      ffHat fr σ⁻¹ * fr.signChange (ffOpt (ffAct σ J)) := by
  have h1 : (fr.signChange (ffOpt J))⁻¹ = fr.signChange (ffOpt J) :=
    inv_eq_of_mul_eq_one_right (fr.signChange_mul_self (ffOpt J))
  rw [mul_inv_rev, h1, ← ffOutFF6PN1_hat_inv, ← ffHat_conj_signChange_ffOpt fr σ J]
  group

@[expose] def ffOutFF6PN1_supp (v : Fin 5 → ZMod 2) : Finset (Fin 5) :=
  Finset.univ.filter fun i => v i ≠ 0

theorem ffOutFF6PN1_eq_of_supp_eq {v w : Fin 5 → ZMod 2}
    (h : ffOutFF6PN1_supp v = ffOutFF6PN1_supp w) : v = w := by
  funext i
  have hmem : (v i ≠ 0) ↔ (w i ≠ 0) := by
    have h' := congrArg (fun s : Finset (Fin 5) => i ∈ s) h
    simpa [ffOutFF6PN1_supp] using h'
  exact (by decide : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b) (v i) (w i) hmem

theorem ffOutFF6PN1_supp_add (v w : Fin 5 → ZMod 2) :
    ffOutFF6PN1_supp (v + w) = symmDiff (ffOutFF6PN1_supp v) (ffOutFF6PN1_supp w) := by
  ext i
  rw [Finset.mem_symmDiff]
  simp only [ffOutFF6PN1_supp, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
  exact (by decide : ∀ a b : ZMod 2,
    (a + b ≠ 0) ↔ ((a ≠ 0 ∧ ¬ b ≠ 0) ∨ (b ≠ 0 ∧ ¬ a ≠ 0))) (v i) (w i)

lemma ffOutFF6PN1_zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

theorem ffOutFF6PN1_isEvenVec_iff_even_supp (v : Fin 5 → ZMod 2) :
    IsEvenVec v ↔ Even (ffOutFF6PN1_supp v).card := by
  unfold IsEvenVec ffOutFF6PN1_supp
  have h1 : (∑ i, v i) = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), v i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : v i = 0 <;> simp [h]
  rw [h1]
  have h2 : (∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), v i)
      = ∑ _i ∈ Finset.univ.filter (fun i => v i ≠ 0), (1 : ZMod 2) :=
    Finset.sum_congr rfl fun i hi =>
      ffOutFF6PN1_zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hi).2
  rw [h2, Finset.sum_const, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff_even]

theorem ffOutFF6PN1_supp_indicator (J : Finset (Fin 5)) :
    ffOutFF6PN1_supp (fun i => if i ∈ J then (1 : ZMod 2) else 0) = J := by
  ext i
  simp only [ffOutFF6PN1_supp, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i ∈ J <;> simp [hi]

theorem ffOutFF6PN1_supp_permVec (σ : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 2) :
    ffOutFF6PN1_supp (permVec σ v) = ffAct σ (ffOutFF6PN1_supp v) := by
  ext i
  rw [ffAct, Finset.mem_map]
  constructor
  · intro hi
    exact ⟨σ.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa [permVec, Function.comp_apply] using (Finset.mem_filter.mp hi).2⟩,
      Equiv.apply_symm_apply σ i⟩
  · rintro ⟨j, hj, hji⟩
    have hsymm : σ.symm i = j := (Equiv.symm_apply_eq σ).mpr hji.symm
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [permVec, Function.comp_apply, hsymm]
    exact (Finset.mem_filter.mp hj).2

end CFSG.OddStandard.SmallF3.Omega
