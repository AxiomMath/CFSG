module

public import CFSG.GH74.GLS.C3.Layer1.BkL114Epw
public import CFSG.GH74.GLS.C3.Prop121.Card7Syl
public import Certificates.Certificate5151

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

namespace Mod11

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.HC CFSG.GH74.GLS.C3.Prop121.Card7.Syl

@[expose] def EL : List (Perm (Fin 11)) :=
  [1, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 0 1 * swap 6 7, swap 2 3 * swap 4 5,
    swap 2 3 * swap 6 7, swap 4 5 * swap 6 7, Y11]

theorem EL_spec_chk : (EL.all fun q => decide (sign q = 1) &&
    decide (∀ p : Fin 11, q p = p ∨ q p = Y11 p)) = true := by
  decide +kernel

theorem EL_spec : ∀ q ∈ EL, sign q = 1 ∧ ∀ p : Fin 11, q p = p ∨ q p = Y11 p := by
  intro q hq
  have h := EL_spec_chk
  rw [List.all_eq_true] at h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h q hq

theorem EL_nodup : EL.Nodup := by decide +kernel

theorem perm_ext_fin {g σ : Perm (Fin 11)} (h0 : g 0 = σ 0) (h1 : g 1 = σ 1) (h2 : g 2 = σ 2) (h3 : g 3 = σ 3) (h4 : g 4 = σ 4) (h5 : g 5 = σ 5) (h6 : g 6 = σ 6) (h7 : g 7 = σ 7) (h8 : g 8 = σ 8) (h9 : g 9 = σ 9) (h10 : g 10 = σ 10) : g = σ := by
  refine Equiv.ext fun p => ?_
  fin_cases p
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem pw_cases (g : Perm (Fin 11)) (h : ∀ p, g p = p ∨ g p = Y11 p) (hs : sign g = 1) :
    g ∈ EL := by
  have hY : Y11 0 = 1 ∧ Y11 1 = 0 ∧ Y11 2 = 3 ∧ Y11 3 = 2 ∧ Y11 4 = 5 ∧ Y11 5 = 4 ∧ Y11 6 = 7 ∧ Y11 7 = 6 ∧ Y11 8 = 8 ∧ Y11 9 = 9 ∧ Y11 10 = 10 := by decide +kernel
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10⟩ := hY
  have p0 := pair_cases g (a := 0) (b := 1) (by decide) (by simpa [y0] using h 0)
    (by simpa [y1] using h 1)
  have p1 := pair_cases g (a := 2) (b := 3) (by decide) (by simpa [y2] using h 2)
    (by simpa [y3] using h 3)
  have p2 := pair_cases g (a := 4) (b := 5) (by decide) (by simpa [y4] using h 4)
    (by simpa [y5] using h 5)
  have p3 := pair_cases g (a := 6) (b := 7) (by decide) (by simpa [y6] using h 6)
    (by simpa [y7] using h 7)
  have f8 : g 8 = 8 := by simpa [y8] using h 8
  have f9 : g 9 = 9 := by simpa [y9] using h 9
  have f10 : g 10 = 10 := by simpa [y10] using h 10
  rcases p0 with ⟨x0, x1⟩ | ⟨x0, x1⟩ <;> rcases p1 with ⟨x2, x3⟩ | ⟨x2, x3⟩ <;>
    rcases p2 with ⟨x4, x5⟩ | ⟨x4, x5⟩ <;> rcases p3 with ⟨x6, x7⟩ | ⟨x6, x7⟩
  · have hg : g = 1 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 6 7 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 4 5 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 4 5 * swap 6 7 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 2 3 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 2 3 * swap 6 7 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 2 3 * swap 4 5 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 2 3 * swap 4 5 * swap 6 7 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 6 7 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 4 5 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 4 5 * swap 6 7 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 2 3 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 2 3 * swap 6 7 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 2 3 * swap 4 5 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
  · have hg : g = swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 := perm_ext_fin (by rw [x0]; decide +kernel) (by rw [x1]; decide +kernel) (by rw [x2]; decide +kernel) (by rw [x3]; decide +kernel) (by rw [x4]; decide +kernel) (by rw [x5]; decide +kernel) (by rw [x6]; decide +kernel) (by rw [x7]; decide +kernel) (by rw [f8]; decide +kernel) (by rw [f9]; decide +kernel) (by rw [f10]; decide +kernel)
    rw [hg] at hs ⊢
    revert hs
    decide +kernel
@[expose] def yref : Perm (Fin 11) := swap 0 1 * swap 2 3

@[expose] def CL : List (Perm (Fin 11)) :=
  [1, swap 2 4 * swap 3 5, swap 2 6 * swap 3 7,
    swap 0 4 * swap 0 2 * (swap 1 5 * swap 1 3),
    swap 0 6 * swap 0 2 * (swap 1 7 * swap 1 3),
    swap 0 4 * swap 1 5 * (swap 2 6 * swap 3 7)]

theorem trans_check_chk : (EL.all fun q => decide (q = 1) || decide (q = Y11) ||
    CL.any fun c => decide (c * Y11 = Y11 * c) && decide (c * yref * c⁻¹ = q) &&
      decide (sign c = 1)) = true := by
  decide +kernel

theorem trans_check : ∀ q ∈ EL, q ≠ 1 → q ≠ Y11 →
    ∃ c ∈ CL, c * Y11 = Y11 * c ∧ c * yref * c⁻¹ = q ∧ sign c = 1 := by
  intro q hq h1 hy
  have h := trans_check_chk
  rw [List.all_eq_true] at h
  have h2 := h q hq
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at h2
  rcases h2 with (h3 | h3) | ⟨c, hc, ⟨h4, h5⟩, h6⟩
  · exact absurd h3 h1
  · exact absurd h3 hy
  · exact ⟨c, hc, h4, h5, h6⟩

theorem PS02_mem_SL_true : decide (PS 0 2 ∈ SL) = true :=
  Certificates.certificate5151.2.1

theorem SL_center_true :
    (SL.all fun s => (!(SL.all fun t => decide (s * t = t * s))) || decide (s = 1 ∨ s = Y11)) =
      true :=
  Certificates.certificate5151.2.2.2

@[expose] def yA : alternatingGroup (Fin 11) := ⟨Y11, mem_alternatingGroup.2 (by decide +kernel)⟩

theorem yA_sq : yA * yA = 1 := Subtype.ext (by
  show Y11 * Y11 = 1
  decide +kernel)

theorem mem_Epw_yA {g : alternatingGroup (Fin 11)} :
    g ∈ Epw yA yA_sq ↔ (g : Perm (Fin 11)) ∈ EL := by
  constructor
  · intro hg
    exact pw_cases g.1 (fun p => hg p) (mem_alternatingGroup.1 g.2)
  · intro hg p
    exact (EL_spec _ hg).2 p

theorem card_Epw_yA : Nat.card (Epw yA yA_sq) = 8 := by
  rw [card_Epw_of_list yA_sq EL EL_nodup (fun q hq => (EL_spec q hq).1) (fun g => mem_Epw_yA)]
  rfl

@[expose] def yrefA : alternatingGroup (Fin 11) :=
  ⟨yref, mem_alternatingGroup.2 (by decide +kernel)⟩

theorem trans_ref {z : alternatingGroup (Fin 11)} (hz : z ∈ Epw yA yA_sq) (h1 : z ≠ 1) (h2 : z ≠ yA) :
    ∃ c : alternatingGroup (Fin 11), c * yA = yA * c ∧ c * yrefA * c⁻¹ = z := by
  have hzL := mem_Epw_yA.1 hz
  obtain ⟨c, -, hc1, hc2, hc3⟩ := trans_check z.1 hzL (fun h => h1 (Subtype.ext h))
    (fun h => h2 (Subtype.ext h))
  exact ⟨⟨c, mem_alternatingGroup.2 hc3⟩, Subtype.ext hc1, Subtype.ext hc2⟩

theorem trans_Epw : ∀ z₁ ∈ Epw yA yA_sq, ∀ z₂ ∈ Epw yA yA_sq, z₁ ≠ 1 → z₁ ≠ yA → z₂ ≠ 1 → z₂ ≠ yA →
    ∃ c : alternatingGroup (Fin 11), c * yA = yA * c ∧ c * z₁ * c⁻¹ = z₂ := by
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

theorem sylow_Sstar : IsSylowOf 2 Sstar ⊤ := by
  refine isSylowOf_of_card le_top ?_
  rw [card_Sstar, Subgroup.card_top, card_A11]
  have h : (19958400 : ℕ).factorization 2 = 7 := by decide +kernel
  rw [h]
  norm_num

theorem center_Sstar
    {s : alternatingGroup (Fin 11)} (hs : s ∈ Sstar) (hsc : ∀ t ∈ Sstar, s * t = t * s)
    (hs1 : s ≠ 1) : s = yA := by
  have h5 := SL_center_true
  rw [List.all_eq_true] at h5
  have h6 := h5 (s : P11) hs
  have hall : (SL.all fun t => decide ((s : P11) * t = t * (s : P11))) = true := by
    rw [List.all_eq_true]
    intro t ht
    have htA : (⟨t, mem_alternatingGroup.2 (SL_even ht)⟩ : alternatingGroup (Fin 11)) ∈ Sstar := ht
    have := congrArg Subtype.val (hsc _ htA)
    simpa using this
  rw [hall] at h6
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at h6
  rcases h6 with h | h
  · exact absurd (Subtype.ext h) hs1
  · exact Subtype.ext h

theorem PS02_mem_Sstar :
    (⟨PS 0 2, mem_alternatingGroup.2 (by decide +kernel)⟩ : alternatingGroup (Fin 11)) ∈ Sstar := by
  show PS 0 2 ∈ SL
  exact of_decide_eq_true PS02_mem_SL_true

theorem amodel_eleven : AModel (7 + 4) := by
  refine amodel_of_model (m := 11) (by norm_num) Sstar sylow_Sstar yA yA_sq ?_
    ⟨PS 0 2, mem_alternatingGroup.2 (by decide +kernel)⟩ PS02_mem_Sstar ?_ 0 ?_ ?_
    card_Epw_yA trans_Epw
  · intro s hs hsc _ hs1
    exact center_Sstar hs hsc hs1
  · exact Subtype.ext (by
      show PS 0 2 * PS 0 2 = 1
      decide +kernel)
  · show PS 0 2 0 ≠ 0
    decide +kernel
  · show PS 0 2 0 ≠ Y11 0
    decide +kernel

end Mod11

end CFSG.GH74.GLS.C3.Layer1.Bk
