module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteNaming
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseVanishing

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatRelative

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.FlatComplete

variable {m M : ℕ}

theorem x_row_eq (hm : m = 2 * M) {X : ZMod m → ℂ} (f : ℕ → ℂ)
    (hodd : ∀ h ∈ (Finset.Ico 1 m).filter Odd, X h = f h)
    (heven : ∀ r ∈ Finset.Ico 1 M, X (-(2 * (r : ZMod m))) = f (m - 2 * r)) :
    ∀ j ∈ Finset.Ico 1 m, X j = f j := by
  intro j hj
  rcases Nat.even_or_odd j with ⟨t, ht⟩ | ho
  · have hj' := Finset.mem_Ico.mp hj
    have h := heven (M - t) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    rw [neg_two_mul_eq hm (by omega), show m - 2 * (M - t) = j by omega] at h
    exact h
  · exact hodd j (Finset.mem_filter.mpr ⟨hj, ho⟩)

theorem sum_antidiag_off_zero [NeZero m] (κ : ℂ) (l : ZMod m) :
    ∑ i : ZMod m, (if ((i, l - i) : ZMod m × ZMod m) = (0, 0) then 0 else κ) =
      m * κ - if l = 0 then κ else 0 := by
  have h : ∀ i : ZMod m, (if ((i, l - i) : ZMod m × ZMod m) = (0, 0) then 0 else κ) =
      κ - if i = 0 then (if l = 0 then κ else 0) else 0 := by
    intro i
    by_cases hi : i = 0
    · subst hi
      by_cases hl : l = 0
      · subst hl
        simp
      · simp [hl]
    · have hne : ((i, l - i) : ZMod m × ZMod m) ≠ (0, 0) := fun h' => hi (Prod.ext_iff.mp h').1
      rw [ite_eq_right hne, ite_eq_right hi, sub_zero]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul, Finset.sum_ite_eq' Finset.univ (0 : ZMod m),
    ite_eq_left (Finset.mem_univ _)]

theorem diag_mem_orbit_diag_iff {ρ ρ' : ZMod m} :
    (ρ', ρ') ∈ MulAction.orbit (dualGroup m) (ρ, ρ) ↔ ρ' = ρ := by
  constructor
  · intro h
    rw [mem_orbit_dualGroup_iff, mem_dualSix_iff] at h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> exact h
  · rintro rfl
    exact MulAction.mem_orbit_self _

theorem not_mem_orbit_diag_of_six {I : ZMod m × ZMod m}
    (h6 : (MulAction.orbit (dualGroup m) I).ncard = 6) (ρ : ZMod m) :
    I ∉ MulAction.orbit (dualGroup m) (ρ, ρ) := by
  intro hI
  rw [MulAction.orbit_eq_iff.mpr hI, ncard_orbit_eq_six_iff, nodup_dualSix_iff] at h6
  exact h6.1 rfl

theorem orbit_indicator_inv (R : ZMod m × ZMod m) (κ : ℂ) {I I' : ZMod m × ZMod m}
    (h : I' ∈ MulAction.orbit (dualGroup m) I) :
    (if I' ∈ MulAction.orbit (dualGroup m) R then κ else 0) =
      if I ∈ MulAction.orbit (dualGroup m) R then κ else 0 := by
  have hiff : I' ∈ MulAction.orbit (dualGroup m) R ↔ I ∈ MulAction.orbit (dualGroup m) R := by
    rw [← MulAction.orbit_eq_iff, ← MulAction.orbit_eq_iff, MulAction.orbit_eq_iff.mpr h]
  by_cases hI : I ∈ MulAction.orbit (dualGroup m) R
  · rw [ite_eq_left (hiff.mpr hI), ite_eq_left hI]
  · rw [ite_eq_right fun h' => hI (hiff.mp h'), ite_eq_right hI]

theorem off_zero_inv (κ : ℂ) {I I' : ZMod m × ZMod m}
    (h : I' ∈ MulAction.orbit (dualGroup m) I) :
    (if I' = (0, 0) then 0 else κ) = if I = (0, 0) then 0 else κ := by
  have hiff : I' = (0, 0) ↔ I = (0, 0) := by
    constructor
    · rintro rfl
      have hI : I ∈ MulAction.orbit (dualGroup m) ((0, 0) : ZMod m × ZMod m) := by
        rw [MulAction.orbit_eq_iff.mpr h]
        exact MulAction.mem_orbit_self _
      rwa [orbit_zero, Set.mem_singleton_iff] at hI
    · rintro rfl
      rwa [orbit_zero, Set.mem_singleton_iff] at h
  by_cases hI : I = (0, 0)
  · rw [ite_eq_left (hiff.mpr hI), ite_eq_left hI]
  · rw [ite_eq_right fun h' => hI (hiff.mp h'), ite_eq_right hI]

theorem pair_eq_of_reps {V : Finset (ZMod m × ZMod m)} {f g : ZMod m × ZMod m → ℂ}
    (hf : ∀ I I', I' ∈ MulAction.orbit (dualGroup m) I → f I' = f I)
    (hg : ∀ I I', I' ∈ MulAction.orbit (dualGroup m) I → g I' = g I)
    (hcov : ∀ I : ZMod m × ZMod m, I = (0, 0) ∨
      I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∨
      (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∨
        I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m) + M, (r : ZMod m) + M)) ∨
      ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I')
    (h0 : f (0, 0) = g (0, 0)) (hMM : f (M, M) = g (M, M))
    (hr : ∀ r ∈ Finset.Ico 1 M, f (r, r) = g (r, r))
    (hr' : ∀ r ∈ Finset.Ico 1 M,
      f ((r : ZMod m) + M, (r : ZMod m) + M) = g ((r : ZMod m) + M, (r : ZMod m) + M))
    (hV : ∀ I ∈ V, f I = g I) (I : ZMod m × ZMod m) : f I = g I := by
  rcases hcov I with rfl | h | ⟨r, hr₁, h | h⟩ | ⟨I', hI', h⟩
  · exact h0
  · rw [hf _ _ h, hg _ _ h, hMM]
  · rw [hf _ _ h, hg _ _ h, hr r hr₁]
  · rw [hf _ _ h, hg _ _ h, hr' r hr₁]
  · rw [hf _ _ h, hg _ _ h, hV I' hI']

theorem add_half_ne_zero (hm : m = 2 * M) {r : ℕ} (hr : r ∈ Finset.Ico 1 M) :
    (r : ZMod m) + M ≠ 0 := by
  rw [Finset.mem_Ico] at hr
  rw [← Nat.cast_add]
  exact natCast_ne_zero_of_lt (by omega) (by omega)

theorem pair_row_const (hm : m = 2 * M) (hM : 0 < M) {V : Finset (ZMod m × ZMod m)}
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6)
    {f : ZMod m × ZMod m → ℂ}
    (hf : ∀ I I', I' ∈ MulAction.orbit (dualGroup m) I → f I' = f I)
    (hcov : ∀ I : ZMod m × ZMod m, I = (0, 0) ∨
      I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∨
      (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∨
        I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m) + M, (r : ZMod m) + M)) ∨
      ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I')
    (κ : ℂ) (h0 : f (0, 0) = 0) (hMM : f (M, M) = κ) (hr : ∀ r ∈ Finset.Ico 1 M, f (r, r) = κ)
    (hr' : ∀ r ∈ Finset.Ico 1 M, f ((r : ZMod m) + M, (r : ZMod m) + M) = κ)
    (hV : ∀ I ∈ V, f I = κ) (I : ZMod m × ZMod m) :
    f I = if I = (0, 0) then 0 else κ := by
  have hM0 := ConditionalCompleteBase.natCast_half_ne_zero hm hM
  refine pair_eq_of_reps hf (fun I I' h => off_zero_inv κ h) hcov ?_ ?_ (fun r hr₁ => ?_)
    (fun r hr₁ => ?_) (fun I hI => ?_) I
  · rw [h0, ite_eq_left rfl]
  · rw [hMM, ite_eq_right fun h => hM0 (Prod.ext_iff.mp h).1]
  · rw [hr r hr₁, ite_eq_right fun h => natCast_ne_zero_of_lt (Finset.mem_Ico.mp hr₁).1
      (by have := (Finset.mem_Ico.mp hr₁).2; omega) (Prod.ext_iff.mp h).1]
  · rw [hr' r hr₁, ite_eq_right fun h => add_half_ne_zero hm hr₁ (Prod.ext_iff.mp h).1]
  · have hI0 : I ≠ (0, 0) := by
      rintro rfl
      have h6 := hV6 _ hI
      rw [orbit_zero, Set.ncard_singleton] at h6
      omega
    rw [hV I hI, ite_eq_right hI0]

theorem pair_row_diag {V : Finset (ZMod m × ZMod m)}
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6)
    {f : ZMod m × ZMod m → ℂ}
    (hf : ∀ I I', I' ∈ MulAction.orbit (dualGroup m) I → f I' = f I)
    (hcov : ∀ I : ZMod m × ZMod m, I = (0, 0) ∨
      I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∨
      (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∨
        I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m) + M, (r : ZMod m) + M)) ∨
      ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I')
    (ρ : ZMod m) (κ : ℂ) (h0 : f (0, 0) = if (0 : ZMod m) = ρ then κ else 0)
    (hMM : f (M, M) = if (M : ZMod m) = ρ then κ else 0)
    (hr : ∀ r ∈ Finset.Ico 1 M, f (r, r) = if (r : ZMod m) = ρ then κ else 0)
    (hr' : ∀ r ∈ Finset.Ico 1 M,
      f ((r : ZMod m) + M, (r : ZMod m) + M) = if (r : ZMod m) + M = ρ then κ else 0)
    (hV : ∀ I ∈ V, f I = 0) (I : ZMod m × ZMod m) :
    f I = if I ∈ MulAction.orbit (dualGroup m) (ρ, ρ) then κ else 0 := by
  have hdiag : ∀ ρ' : ZMod m, (if ((ρ', ρ') : ZMod m × ZMod m) ∈
      MulAction.orbit (dualGroup m) (ρ, ρ) then κ else 0) = if ρ' = ρ then κ else 0 := by
    intro ρ'
    by_cases h : ρ' = ρ
    · rw [ite_eq_left (diag_mem_orbit_diag_iff.mpr h), ite_eq_left h]
    · rw [ite_eq_right fun h' => h (diag_mem_orbit_diag_iff.mp h'), ite_eq_right h]
  refine pair_eq_of_reps hf (fun I I' h => orbit_indicator_inv (ρ, ρ) κ h) hcov ?_ ?_
    (fun r hr₁ => ?_) (fun r hr₁ => ?_) (fun I hI => ?_) I
  · rw [h0, hdiag]
  · rw [hMM, hdiag]
  · rw [hr r hr₁, hdiag]
  · rw [hr' r hr₁, hdiag]
  · rw [hV I hI, ite_eq_right (not_mem_orbit_diag_of_six (hV6 I hI) ρ)]

theorem add_half_ne_natCast (hm : m = 2 * M) {r r' : ℕ} (hr : r ∈ Finset.Ico 1 M)
    (hr' : r' ∈ Finset.Ico 1 M) : (r : ZMod m) + M ≠ r' := by
  rw [Finset.mem_Ico] at hr hr'
  rw [← Nat.cast_add]
  intro h
  have := natCast_inj_of_lt (by omega) (by omega) h
  omega

theorem diagRep_eq_iff (hm : m = 2 * M) (er : ℕ → Fin 2) {r r' : ℕ}
    (hr : r ∈ Finset.Ico 1 M) (hr' : r' ∈ Finset.Ico 1 M) (e e' : Fin 2) :
    ((if e' = er r' then (r' : ZMod m) else (r' : ZMod m) + M) =
      if e = er r then (r : ZMod m) else (r : ZMod m) + M) ↔ r' = r ∧ e' = e := by
  have hr₁ := Finset.mem_Ico.mp hr
  have hr₁' := Finset.mem_Ico.mp hr'
  by_cases he' : e' = er r' <;> by_cases he : e = er r
  · rw [ite_eq_left he', ite_eq_left he]
    constructor
    · intro h
      have hrr := natCast_inj_of_lt (by omega) (by omega) h
      subst hrr
      exact ⟨rfl, he'.trans he.symm⟩
    · rintro ⟨rfl, -⟩
      rfl
  · rw [ite_eq_left he', ite_eq_right he]
    constructor
    · intro h
      exact absurd h.symm (add_half_ne_natCast hm hr hr')
    · rintro ⟨rfl, rfl⟩
      exact absurd he' he
  · rw [ite_eq_right he', ite_eq_left he]
    constructor
    · intro h
      exact absurd h (add_half_ne_natCast hm hr' hr)
    · rintro ⟨rfl, rfl⟩
      exact absurd he he'
  · rw [ite_eq_right he', ite_eq_right he]
    constructor
    · intro h
      have h' : (r' : ZMod m) = r := add_right_cancel h
      have hrr := natCast_inj_of_lt (by omega) (by omega) h'
      subst hrr
      exact ⟨rfl, (eq_one_sub_of_ne he').trans (eq_one_sub_of_ne he).symm⟩
    · rintro ⟨rfl, -⟩
      rfl

theorem diagRep_ne_zero (hm : m = 2 * M) (er : ℕ → Fin 2) {r : ℕ} (hr : r ∈ Finset.Ico 1 M)
    (e : Fin 2) : (if e = er r then (r : ZMod m) else (r : ZMod m) + M) ≠ 0 := by
  have hr₁ := Finset.mem_Ico.mp hr
  by_cases he : e = er r
  · rw [ite_eq_left he]
    exact natCast_ne_zero_of_lt (by omega) (by omega)
  · rw [ite_eq_right he]
    exact add_half_ne_zero hm hr

theorem diagRep_ne_half (hm : m = 2 * M) (er : ℕ → Fin 2) {r : ℕ} (hr : r ∈ Finset.Ico 1 M)
    (e : Fin 2) : (if e = er r then (r : ZMod m) else (r : ZMod m) + M) ≠ M := by
  have hr₁ := Finset.mem_Ico.mp hr
  by_cases he : e = er r
  · rw [ite_eq_left he]
    intro h
    have := natCast_inj_of_lt (by omega) (by omega) h
    omega
  · rw [ite_eq_right he]
    intro h
    rw [← Nat.cast_add] at h
    have := natCast_inj_of_lt (by omega) (by omega) h
    omega

theorem pair_row_single (hm : m = 2 * M) {V : Finset (ZMod m × ZMod m)}
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6)
    {f : ZMod m × ZMod m → ℂ}
    (hf : ∀ I I', I' ∈ MulAction.orbit (dualGroup m) I → f I' = f I)
    (hcov : ∀ I : ZMod m × ZMod m, I = (0, 0) ∨
      I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∨
      (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∨
        I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m) + M, (r : ZMod m) + M)) ∨
      ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I')
    (er : ℕ → Fin 2) {r : ℕ} (hr : r ∈ Finset.Ico 1 M) (e : Fin 2) (κ : ℂ) (h0 : f (0, 0) = 0)
    (hMM : f (M, M) = 0)
    (hdiag : ∀ r' ∈ Finset.Ico 1 M, ∀ e' : Fin 2,
      f (if e' = er r' then (r' : ZMod m) else (r' : ZMod m) + M,
        if e' = er r' then (r' : ZMod m) else (r' : ZMod m) + M) =
        if r' = r ∧ e' = e then κ else 0)
    (hV : ∀ I ∈ V, f I = 0) (I : ZMod m × ZMod m) :
    f I = if I ∈ MulAction.orbit (dualGroup m)
      (if e = er r then (r : ZMod m) else (r : ZMod m) + M,
        if e = er r then (r : ZMod m) else (r : ZMod m) + M) then κ else 0 := by
  have hcond : ∀ r' ∈ Finset.Ico 1 M, ∀ e' : Fin 2,
      (if r' = r ∧ e' = e then κ else 0) =
        if (if e' = er r' then (r' : ZMod m) else (r' : ZMod m) + M) =
          (if e = er r then (r : ZMod m) else (r : ZMod m) + M) then κ else 0 := by
    intro r' hr' e'
    have hiff := diagRep_eq_iff hm er hr hr' e e'
    by_cases h : r' = r ∧ e' = e
    · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (hiff.mp h')]
  refine pair_row_diag hV6 hf hcov _ κ ?_ ?_ (fun r' hr' => ?_) (fun r' hr' => ?_) hV I
  · rw [h0, ite_eq_right fun h => diagRep_ne_zero hm er hr e h.symm]
  · rw [hMM, ite_eq_right fun h => diagRep_ne_half hm er hr e h.symm]
  · have h := hdiag r' hr' (er r')
    rw [ite_eq_left rfl] at h
    rw [h, hcond r' hr' (er r'), ite_eq_left rfl]
  · have hne : 1 - er r' ≠ er r' := one_sub_ne (er r')
    have h := hdiag r' hr' (1 - er r')
    rw [ite_eq_right hne] at h
    rw [h, hcond r' hr' (1 - er r'), ite_eq_right hne]

end CFSG.Wreathed.FlatRelative
