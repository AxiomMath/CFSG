module

public import CFSG.GH74.GLS.C3.Layer1.BkL114Epw
public import CFSG.GH74.GLS.C3.Layer2.L5Fin

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

namespace Mod9

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Prop121

@[expose] def Y9 : Perm (Fin 9) := swap 0 1 * swap 2 3 * (swap 5 6 * swap 7 8)

theorem yS_eq : yS = Y9 := by decide +kernel

@[expose] def EL : List (Perm (Fin 9)) :=
  [1, swap 0 1 * swap 2 3, swap 0 1 * swap 5 6, swap 0 1 * swap 7 8, swap 2 3 * swap 5 6,
    swap 2 3 * swap 7 8, swap 5 6 * swap 7 8, Y9]

theorem EL_spec_chk : (EL.all fun q => decide (sign q = 1) &&
    decide (∀ p : Fin 9, q p = p ∨ q p = Y9 p)) = true := by
  decide +kernel

theorem EL_spec : ∀ q ∈ EL, sign q = 1 ∧ ∀ p : Fin 9, q p = p ∨ q p = Y9 p := by
  intro q hq
  have h := EL_spec_chk
  rw [List.all_eq_true] at h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h q hq

theorem EL_nodup : EL.Nodup := by decide +kernel

theorem perm_ext_fin {g σ : Perm (Fin 9)} (h0 : g 0 = σ 0) (h1 : g 1 = σ 1) (h2 : g 2 = σ 2) (h3 : g 3 = σ 3) (h4 : g 4 = σ 4) (h5 : g 5 = σ 5) (h6 : g 6 = σ 6) (h7 : g 7 = σ 7) (h8 : g 8 = σ 8) : g = σ := by
  refine Equiv.ext fun p => ?_
  fin_cases p
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]

theorem pw_cases (g : Perm (Fin 9)) (h : ∀ p, g p = p ∨ g p = Y9 p) (hs : sign g = 1) :
    g ∈ EL := by
  have hY : Y9 0 = 1 ∧ Y9 1 = 0 ∧ Y9 2 = 3 ∧ Y9 3 = 2 ∧ Y9 4 = 4 ∧ Y9 5 = 6 ∧ Y9 6 = 5 ∧ Y9 7 = 8 ∧ Y9 8 = 7 := by decide +kernel
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8⟩ := hY
  have p0 := pair_cases g (a := 0) (b := 1) (by decide) (by simpa [y0] using h 0)
    (by simpa [y1] using h 1)
  have p1 := pair_cases g (a := 2) (b := 3) (by decide) (by simpa [y2] using h 2)
    (by simpa [y3] using h 3)
  have p2 := pair_cases g (a := 5) (b := 6) (by decide) (by simpa [y5] using h 5)
    (by simpa [y6] using h 6)
  have p3 := pair_cases g (a := 7) (b := 8) (by decide) (by simpa [y7] using h 7)
    (by simpa [y8] using h 8)
  have f4 : g 4 = 4 := by simpa [y4] using h 4
  rcases p0 with ⟨x0, x1⟩ | ⟨x0, x1⟩ <;> rcases p1 with ⟨x2, x3⟩ | ⟨x2, x3⟩ <;>
    rcases p2 with ⟨x5, x6⟩ | ⟨x5, x6⟩ <;> rcases p3 with ⟨x7, x8⟩ | ⟨x7, x8⟩
  · have hg : g = 1 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 7 8 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 5 6 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 5 6 * swap 7 8 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 2 3 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 2 3 * swap 7 8 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 2 3 * swap 5 6 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 2 3 * swap 5 6 * swap 7 8 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 7 8 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 5 6 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 5 6 * swap 7 8 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 2 3 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 2 3 * swap 7 8 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 2 3 * swap 5 6 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 2 3 * swap 5 6 * swap 7 8 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [f4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [x8]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
@[expose] def yref : Perm (Fin 9) := swap 0 1 * swap 2 3

@[expose] def CL : List (Perm (Fin 9)) :=
  [1, swap 2 5 * swap 3 6, swap 2 7 * swap 3 8,
    swap 0 5 * swap 0 2 * (swap 1 6 * swap 1 3),
    swap 0 7 * swap 0 2 * (swap 1 8 * swap 1 3),
    swap 0 5 * swap 1 6 * (swap 2 7 * swap 3 8)]

theorem trans_check_chk : (EL.all fun q => decide (q = 1) || decide (q = Y9) ||
    CL.any fun c => decide (c * Y9 = Y9 * c) && decide (c * yref * c⁻¹ = q) &&
      decide (sign c = 1)) = true := by
  decide +kernel

theorem trans_check : ∀ q ∈ EL, q ≠ 1 → q ≠ Y9 →
    ∃ c ∈ CL, c * Y9 = Y9 * c ∧ c * yref * c⁻¹ = q ∧ sign c = 1 := by
  intro q hq h1 hy
  have h := trans_check_chk
  rw [List.all_eq_true] at h
  have h2 := h q hq
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at h2
  rcases h2 with (h3 | h3) | ⟨c, hc, ⟨h4, h5⟩, h6⟩
  · exact absurd h3 h1
  · exact absurd h3 hy
  · exact ⟨c, hc, h4, h5, h6⟩

@[expose] def yA : alternatingGroup (Fin 9) := ⟨Y9, mem_alternatingGroup.2 (by decide +kernel)⟩

theorem yA_sq : yA * yA = 1 := Subtype.ext (by
  show Y9 * Y9 = 1
  decide +kernel)

theorem mem_Epw_yA {g : alternatingGroup (Fin 9)} :
    g ∈ Epw yA yA_sq ↔ (g : Perm (Fin 9)) ∈ EL := by
  constructor
  · intro hg
    exact pw_cases g.1 (fun p => hg p) (mem_alternatingGroup.1 g.2)
  · intro hg p
    exact (EL_spec _ hg).2 p

theorem card_Epw_yA : Nat.card (Epw yA yA_sq) = 8 := by
  rw [card_Epw_of_list yA_sq EL EL_nodup (fun q hq => (EL_spec q hq).1) (fun g => mem_Epw_yA)]
  rfl

@[expose] def yrefA : alternatingGroup (Fin 9) :=
  ⟨yref, mem_alternatingGroup.2 (by decide +kernel)⟩

theorem trans_ref {z : alternatingGroup (Fin 9)} (hz : z ∈ Epw yA yA_sq) (h1 : z ≠ 1) (h2 : z ≠ yA) :
    ∃ c : alternatingGroup (Fin 9), c * yA = yA * c ∧ c * yrefA * c⁻¹ = z := by
  have hzL := mem_Epw_yA.1 hz
  obtain ⟨c, -, hc1, hc2, hc3⟩ := trans_check z.1 hzL (fun h => h1 (Subtype.ext h))
    (fun h => h2 (Subtype.ext h))
  exact ⟨⟨c, mem_alternatingGroup.2 hc3⟩, Subtype.ext hc1, Subtype.ext hc2⟩

theorem trans_Epw : ∀ z₁ ∈ Epw yA yA_sq, ∀ z₂ ∈ Epw yA yA_sq, z₁ ≠ 1 → z₁ ≠ yA → z₂ ≠ 1 → z₂ ≠ yA →
    ∃ c : alternatingGroup (Fin 9), c * yA = yA * c ∧ c * z₁ * c⁻¹ = z₂ := by
  intro z₁ hz₁ z₂ hz₂ h11 h1y h21 h2y
  obtain ⟨c₁, hc₁, hc₁'⟩ := trans_ref hz₁ h11 h1y
  obtain ⟨c₂, hc₂, hc₂'⟩ := trans_ref hz₂ h21 h2y
  have hc₁i : c₁⁻¹ * yA = yA * c₁⁻¹ := by
    calc c₁⁻¹ * yA = c₁⁻¹ * (yA * c₁) * c₁⁻¹ := by group
      _ = c₁⁻¹ * (c₁ * yA) * c₁⁻¹ := by rw [hc₁]
      _ = yA * c₁⁻¹ := by group
  refine ⟨c₂ * c₁⁻¹, ?_, ?_⟩
  · calc c₂ * c₁⁻¹ * yA = c₂ * (c₁⁻¹ * yA) := by group
      _ = c₂ * (yA * c₁⁻¹) := by rw [hc₁i]
      _ = (c₂ * yA) * c₁⁻¹ := by group
      _ = (yA * c₂) * c₁⁻¹ := by rw [hc₂]
      _ = yA * (c₂ * c₁⁻¹) := by group
  · calc c₂ * c₁⁻¹ * z₁ * (c₂ * c₁⁻¹)⁻¹ = c₂ * (c₁⁻¹ * z₁ * c₁) * c₂⁻¹ := by group
      _ = c₂ * yrefA * c₂⁻¹ := by rw [← hc₁']; group
      _ = z₂ := hc₂'

theorem center_S0A
    {s : alternatingGroup (Fin 9)} (hs : s ∈ S0A) (hsc : ∀ t ∈ S0A, s * t = t * s)
    (hs1 : s ≠ 1) : s = yA := by
  have h := Z_S0 (s := (s : Perm (Fin 9))) hs (fun t ht => by
    have htA : (⟨t, mem_alternatingGroup.2 (sign_S0 ht)⟩ : alternatingGroup (Fin 9)) ∈ S0A := ht
    have := congrArg Subtype.val (hsc _ htA)
    simpa using this)
  rcases h with h | h
  · exact absurd (Subtype.ext h) hs1
  · exact Subtype.ext (h.trans yS_eq)

theorem amodel_nine : AModel (5 + 4) := by
  refine amodel_of_model (m := 9) (by norm_num) S0A isSylowOf_S0A yA yA_sq ?_
    ⟨a0perm 5, mem_alternatingGroup.2 sign_a0⟩ a0_mem_S0 ?_ 0 ?_ ?_
    card_Epw_yA trans_Epw
  · intro s hs hsc _ hs1
    exact center_S0A hs hsc hs1
  · exact Subtype.ext a0_sq
  · show a0perm 5 0 ≠ 0
    decide +kernel
  · show a0perm 5 0 ≠ Y9 0
    decide +kernel

end Mod9

end CFSG.GH74.GLS.C3.Layer1.Bk
