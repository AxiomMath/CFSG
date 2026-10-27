module

public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthRat
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap CFSG.SignalizerFunctorTheorem.NonLocal.Orth

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem submodule_eq_bot_or_top_of_elementaryGroup_invariant
    (hQ : (polarBilin Q).Nondegenerate)
    (hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j))
    (W : Submodule K V) (hW : ∀ g ∈ elementaryGroup Q, ∀ x ∈ W, g x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨P, hPorth⟩ := hP
  have hWe : ∀ u w : V, ∀ x ∈ W, eichler Q u w x ∈ W :=
    fun u w x hx => hW _ (eichler_mem_elementaryGroup Q u w) x hx
  have htwo : ∀ i : Fin 2, ∃ j : Fin 2, j ≠ i := by
    intro i
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  have hsing : ∃ u : V, u ≠ 0 ∧ Q u = 0 ∧ u ∈ W := by
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    by_cases hA : ∃ i : Fin 2, polar Q x (P i).e ≠ 0
    · obtain ⟨i, hi⟩ := hA
      obtain ⟨j, hji⟩ := htwo i
      exact ⟨(P i).e, (P i).e_ne_zero, (P i).Q_e,
        exchange_mem (P i) (P j) (hPorth i j (Ne.symm hji)) W (hWe _ _) (hWe _ _) hxW hi⟩
    by_cases hB : ∃ i : Fin 2, polar Q x (P i).f ≠ 0
    · obtain ⟨i, hi⟩ := hB
      obtain ⟨j, hji⟩ := htwo i
      exact ⟨(P i).f, (P i).f_ne_zero, (P i).Q_f,
        exchange_mem (swapPair (P i)) (P j) (orth_swapPair_left (hPorth i j (Ne.symm hji))) W
          (hWe _ _) (hWe _ _) hxW hi⟩
    push Not at hA hB
    obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hx0
    set w : V := y - (polar Q y (P 0).f) • (P 0).e - (polar Q y (P 0).e) • (P 0).f with hw
    have hwe : polar Q (P 0).e w = 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q y (P 0).e, polar_self_eq_zero (P 0).Q_e, (P 0).polar_ef]
      ring
    have hwf : polar Q (P 0).f w = 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q y (P 0).f, (P 0).polar_fe, polar_self_eq_zero (P 0).Q_f]
      ring
    have hxw : polar Q x w ≠ 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        hA 0, hB 0]
      simpa using hy
    exact ⟨(P 0).e, (P 0).e_ne_zero, (P 0).Q_e,
      perp_extract_mem (P 0) W hxW (hA 0) (HypPair.mem_perp.2 ⟨hwe, hwf⟩)
        (hWe (P 0).e w x hxW) hxw⟩
  obtain ⟨u₀, hu₀0, hu₀Q, hu₀W⟩ := hsing
  have hall : ∀ v : V, Q v = 0 → v ∈ W := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]; exact W.zero_mem
    obtain ⟨g, hg, hgv⟩ :=
      exists_mem_elementaryGroup_apply_eq hQ (hPorth 0 1 (by decide)) hu₀0 hv0
        (by rw [hu₀Q, hv])
    rw [← hgv]
    exact hW g hg u₀ hu₀W
  rw [eq_top_iff]
  intro v _
  have hle : Submodule.span K {u : V | Q u = 0} ≤ W := by
    rw [Submodule.span_le]
    rintro u hu
    exact hall u hu
  exact hle (by rw [span_singular_eq_top (P 0)]; exact Submodule.mem_top)

end CFSG.ClassicalGroups.Orthogonal
