module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClU6Lft
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClU6Cf
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoKey
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Supp
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Timmesfeld.CrossChar (scalarU conjHom_scalarU)
open CFSG.HardMathSupport.Dickson.Sec6.I923
  (pow_three_eq_one_of_commute_order_eleven exists_diag_form)
open CFSG.LocalAnalysis.GLTheoremA.S265BU8 (exists_perm_of_support eq_of_mul_diagonal_eq)

variable {K : Type} [Field K]

private theorem units_pow_three' (h : UnitaryFieldData 2 1 K) (u : Kˣ) : u ^ 3 = 1 := by
  haveI := h.finite
  have hc : Nat.card Kˣ = 3 := by
    have := Nat.card_units K
    rw [h.card] at this
    simpa using this
  rw [← hc]
  exact pow_card_eq_one'

private theorem diag_pair_of_frames (h : UnitaryFieldData 2 1 K) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {D Y X₁ X₂ T D₀ Q : primeFormUnitary h (idGram K 6)}
    (hY11 : Y ^ 11 = 1) (hY1 : Y ≠ 1) (hDY : D * Y = Y * D) (hD3 : D ^ 3 = 1)
    {i₀ : Fin 6} {ν μ : K} (hνμ : ν ≠ μ)
    (hDT : D = T * D₀ * T⁻¹)
    (hD₀ : ((D₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal fun i => if i = i₀ then μ else ν)
    {δ : Fin 6 → K} {k₁ k₂ : Fin 6} (hk₁₂ : k₁ ≠ k₂)
    (hQD : (((Q⁻¹ * D * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal δ)
    (hQ₁ : (((Q⁻¹ * X₁ * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = (diagonal fun i => if i = k₁ then ω else 1))
    (hQ₂ : (((Q⁻¹ * X₂ * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal fun i => if i = k₂ then ω else 1) :
    ∃ X ∈ ({X₁, X₂} : Set (primeFormUnitary h (idGram K 6))),
      primeFormConjHom h (idGram K 6) X * primeFormConjHom h (idGram K 6) Y ≠
        primeFormConjHom h (idGram K 6) Y * primeFormConjHom h (idGram K 6) X ∧
      ∃ (D' Q' : primeFormUnitary h (idGram K 6)) (k k' : Fin 6) (ζ : K),
        primeFormConjHom h (idGram K 6) D' = primeFormConjHom h (idGram K 6) D ∧ k ≠ k' ∧
        ζ ^ 2 + ζ + 1 = 0 ∧
        (((Q'⁻¹ * D' * Q' : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = (diagonal fun i => if i = k then ζ else 1) ∧
        (((Q'⁻¹ * X * Q' : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = diagonal fun i => if i = k' then ω else 1 := by
  classical
  have hK : Nat.card K = 4 := h.card.trans (by norm_num)
  have hne : ¬(6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  have hM : (((T⁻¹ * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) * diagonal δ = (diagonal fun i => if i = i₀ then μ else ν) *
        (((T⁻¹ * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) := by
    have e : (T⁻¹ * Q) * (Q⁻¹ * D * Q) = D₀ * (T⁻¹ * Q) := by rw [hDT]; group
    rw [← hQD, ← hD₀]
    exact congrArg (fun g : primeFormUnitary h (idGram K 6) =>
      ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) e
  obtain ⟨π, hπ⟩ := exists_perm_of_support (Matrix.GeneralLinearGroup.det
    ((T⁻¹ * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K)).ne_zero
    fun l j hlj => eq_of_mul_diagonal_eq hM hlj
  set k := π.symm i₀ with hkdef
  have hδ : ∀ j, δ j = if j = k then μ else ν := fun j => by
    rw [← hπ j, hkdef]
    exact if_congr (Equiv.apply_eq_iff_eq_symm_apply π) rfl rfl
  have hc3 : (Q⁻¹ * D * Q) ^ 3 = 1 := by
    have e := conj_pow (a := Q⁻¹) (b := D) (i := 3)
    rw [inv_inv] at e
    rw [e, hD3, mul_one, inv_mul_cancel]
  have hδ3 : ∀ j, δ j ^ 3 = 1 := fun j => by
    have e := congrArg (fun g : primeFormUnitary h (idGram K 6) =>
      ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) j j) hc3
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hQD, diagonal_pow, Subgroup.coe_one,
      Units.val_one, diagonal_apply_eq, one_apply_eq, Pi.pow_apply] at e
    exact e
  obtain ⟨j₀, hj₀⟩ := exists_ne k
  have hν3 : ν ^ 3 = 1 := by simpa [hδ j₀, if_neg hj₀] using hδ3 j₀
  have hμ3 : μ ^ 3 = 1 := by simpa [hδ k] using hδ3 k
  have hν0 : ν ≠ 0 := fun h0 => by simp [h0] at hν3
  have hω1 : ω ≠ 1 := fun h1 => by
    rw [h1] at hω
    have h2 : (2 : K) = 0 := by
      haveI := h.charP
      exact_mod_cast CharP.cast_eq_zero K 2
    exact one_ne_zero (α := K) (by linear_combination hω - h2)
  obtain ⟨X, hX, k', hkk', hQX⟩ : ∃ X ∈ ({X₁, X₂} : Set (primeFormUnitary h (idGram K 6))),
      ∃ k' : Fin 6, k ≠ k' ∧
        (((Q⁻¹ * X * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = (diagonal fun i => if i = k' then ω else 1) := by
    by_cases hk : k = k₁
    · exact ⟨X₂, Set.mem_insert_of_mem _ rfl, k₂, hk ▸ hk₁₂, hQ₂⟩
    · exact ⟨X₁, Set.mem_insert _ _, k₁, hk, hQ₁⟩
  refine ⟨X, hX, fun hXY => hY1 ?_, ?_⟩
  ·
    have hXY' : X * Y = Y * X := commute_of_conjHom_commute_of_pow_eleven h hXY hY11
    have hmat : ∀ {Z : primeFormUnitary h (idGram K 6)} {a : Fin 6 → K}, Z * Y = Y * Z →
        (((Q⁻¹ * Z * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = diagonal a →
        (((Q⁻¹ * Y * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) * diagonal a = diagonal a *
            (((Q⁻¹ * Y * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
              Matrix (Fin 6) (Fin 6) K) := fun {Z a} hZY hZ => by
      have e : (Q⁻¹ * Y * Q) * (Q⁻¹ * Z * Q) = (Q⁻¹ * Z * Q) * (Q⁻¹ * Y * Q) := by
        calc (Q⁻¹ * Y * Q) * (Q⁻¹ * Z * Q) = Q⁻¹ * (Y * Z) * Q := by group
          _ = Q⁻¹ * (Z * Y) * Q := by rw [hZY]
          _ = (Q⁻¹ * Z * Q) * (Q⁻¹ * Y * Q) := by group
      rw [← hZ]
      exact congrArg (fun g : primeFormUnitary h (idGram K 6) =>
        ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) e
    have hY'11 : (Q⁻¹ * Y * Q) ^ 11 = 1 := by
      have e := conj_pow (a := Q⁻¹) (b := Y) (i := 11)
      rw [inv_inv] at e
      rw [e, hY11, mul_one, inv_mul_cancel]
    have h1 := eq_one_of_commute_diagonal_pair_six hK
      (by rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hY'11, Subgroup.coe_one,
        Units.val_one]) (hmat hDY hQD) (hmat hXY' hQX) hkk'
      (fun i hi => by rw [hδ i, hδ k, if_neg hi, if_pos rfl]; exact hνμ)
      (fun i hi => by rw [if_neg hi, if_pos rfl]; exact hω1.symm)
    have h2 : Q⁻¹ * Y * Q = 1 := Subtype.ext (Units.ext h1)
    calc Y = Q * (Q⁻¹ * Y * Q) * Q⁻¹ := by group
      _ = 1 := by rw [h2, mul_one, mul_inv_cancel]
  ·
    set u : Kˣ := Units.mk0 ν⁻¹ (inv_ne_zero hν0) with hu_def
    have hu : h.norm (u : K) = 1 := (pow_succ_eq_one_iff_norm h u).mp
      (units_pow_three' h u)
    refine ⟨scalarU h 6 u hu * D, Q, k, k', μ * ν⁻¹, ?_, hkk', ?_, ?_, hQX⟩
    · rw [map_mul, conjHom_scalarU (by norm_num) hne u hu, one_mul]
    · have hζ3 : (μ * ν⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hμ3, hν3, inv_one, one_mul]
      have hζ1 : μ * ν⁻¹ ≠ 1 := fun e => hνμ ((mul_inv_eq_one₀ hν0).1 e).symm
      have e : (μ * ν⁻¹ - 1) * ((μ * ν⁻¹) ^ 2 + μ * ν⁻¹ + 1) = 0 := by
        linear_combination hζ3
      exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 hζ1)
    · have hs : Q⁻¹ * (scalarU h 6 u hu * D) * Q = scalarU h 6 u hu * (Q⁻¹ * D * Q) := by
        rw [← mul_assoc Q⁻¹,
          ← (CFSG.HardMathSupport.Timmesfeld.CrossChar.commute_scalarU (by norm_num) hne u hu
            Q⁻¹).eq]
        group
      rw [hs, Subgroup.coe_mul, Units.val_mul, hQD,
        CFSG.HardMathSupport.Timmesfeld.CrossChar.coe_scalarU, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, diagonal_mul_diagonal]
      congr 1
      funext i
      rw [hδ i, hu_def, Units.val_mk0]
      split_ifs
      · exact mul_comm _ _
      · exact inv_mul_cancel₀ hν0

theorem exists_diag_pair_of_frame_six [CharP K 2] (h : UnitaryFieldData 2 1 K) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {d y : MulAut (primeFormP h (idGram K 6))}
    {X₁ X₂ R : primeFormUnitary h (idGram K 6)} (hdD : d ∈ primeFormD h (idGram K 6))
    (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) (hyD : y ∈ primeFormD h (idGram K 6)) (hy : y ^ 11 = 1)
    (hy1 : y ≠ 1) (hdy : d * y = y * d)
    (hd₁ : d * primeFormConjHom h (idGram K 6) X₁ = primeFormConjHom h (idGram K 6) X₁ * d)
    (hd₂ : d * primeFormConjHom h (idGram K 6) X₂ = primeFormConjHom h (idGram K 6) X₂ * d)
    (hR₁ : (((R * X₁ * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, ω, 1])
    (hR₂ : (((R * X₂ * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, 1, ω]) :
    ∃ X ∈ ({X₁, X₂} : Set (primeFormUnitary h (idGram K 6))),
      primeFormConjHom h (idGram K 6) X * y ≠ y * primeFormConjHom h (idGram K 6) X ∧
      ∃ (D Q : primeFormUnitary h (idGram K 6)) (k k' : Fin 6) (ζ : K),
        primeFormConjHom h (idGram K 6) D = d ∧ k ≠ k' ∧ ζ ^ 2 + ζ + 1 = 0 ∧
        (((Q⁻¹ * D * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = (diagonal fun i => if i = k then ζ else 1) ∧
        (((Q⁻¹ * X * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = diagonal fun i => if i = k' then ω else 1 := by
  classical
  have hne : ¬(6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  obtain ⟨D, rfl⟩ := hdD
  obtain ⟨Y, rfl, hY11⟩ := exists_lift_pow_eleven_six h hyD hy
  have hY1 : Y ≠ 1 := fun h1 => hy1 (by rw [h1, map_one])
  have hDY : D * Y = Y * D := commute_of_conjHom_commute_of_pow_eleven h hdy hY11
  obtain ⟨c₀, -, hc₀⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne (D ^ 3)).1
    (by rw [map_pow]; exact hd3)
  have hM3 : (D : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c₀ := by
    rw [← Subgroup.coe_pow, hc₀]
  have hD3 : D ^ 3 = 1 :=
    pow_three_eq_one_of_commute_order_eleven (by norm_num) hDY.symm hY11 hY1 hM3
  have hMs : ∀ c : Kˣ, (D : GL (Fin 6) K) ≠ GeneralLinearGroup.scalar (Fin 6) c := fun c hc =>
    hd1 ((primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne D).2 ⟨c, units_pow_three' h c, hc⟩)
  obtain ⟨T, D₀, i₀, ν, μ, hνμ, hDT, hD₀⟩ :=
    exists_diag_form (by norm_num) hDY.symm hY11 hY1 hM3 hMs
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hω0 : ω ≠ 0 := fun h0 => by simp [h0] at hω
  have htr : ∀ (X : primeFormUnitary h (idGram K 6)) (v : Fin 6 → K),
      (((R * X * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal v → ∑ i, v i = ω ^ 2 →
      trace ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ≠ 0 := by
    intro X v hX hv
    have e : trace ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        trace (((R * X * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) := by
      show _ = trace (((R : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          (((R : GL (Fin 6) K)⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
      rw [trace_mul_cycle, Units.inv_mul, Matrix.one_mul]
    rw [e, hX, trace_diagonal, hv]
    exact pow_ne_zero 2 hω0
  have hsum : (1 : K) + 1 + 1 + 1 + 1 + ω = ω ^ 2 := by
    linear_combination (-1 : K) * hω + (3 + ω) * h2
  have hDX₁ : D * X₁ = X₁ * D := commute_of_conjHom_commute_of_trace h hd₁
    (htr X₁ _ hR₁ (by simp [Fin.sum_univ_six]; linear_combination hsum))
  have hDX₂ : D * X₂ = X₂ * D := commute_of_conjHom_commute_of_trace h hd₂
    (htr X₂ _ hR₂ (by simp [Fin.sum_univ_six]; linear_combination hsum))
  obtain ⟨Q, δ, k₁, k₂, hk₁₂, hQD, hQ₁, hQ₂⟩ := exists_common_frame_six h hω hD3 hDX₁ hDX₂ hR₁ hR₂
  exact diag_pair_of_frames h hω hY11 hY1 hDY hD3 hνμ hDT hD₀ hk₁₂ hQD hQ₁ hQ₂

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
