module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshXDet
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma4Rel

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp

section Lemma4

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

set_option linter.unusedSectionVars false

variable {d : G} {α : ℕ}

@[expose] noncomputable def μS : G12 := (wordVal wS).2

@[expose] noncomputable def gen4 (d : G) : Fin 8 → G
  | 6 => d
  | 7 => dW e₀ d μS⁻¹
  | i => valG e₀ (sub4 i)

theorem valG_eq_one_of_tblEq {w : List (Fin 5 × Bool)}
    (h : tblEq 14 (tblW w) (idT 14) = true) : valG e₀ w = 1 := by
  unfold valG
  rw [wordVal_eq_one_of_tblEq h, map_one]

theorem stepIs_sound (hd : CentralSwap e₀ α d) {wm y rhs : List (Fin 5 × Bool)}
    (hwm : epsT (tblW wm) = 0) (h : stepIs α wm y rhs = true) :
    valG e₀ rhs = dW e₀ d (wordVal wm).2 * valG e₀ y * (dW e₀ d (wordVal wm).2)⁻¹ := by
  unfold stepIs at h
  cases hs : stepW α wm y with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some f =>
    rw [hs] at h
    rw [← valG_eq_of_tblEq e₀ h]
    exact stepW_sound e₀ hd hwm hs

theorem stepIs_nil (hd : CentralSwap e₀ α d) {y rhs : List (Fin 5 × Bool)}
    (h : stepIs α [] y rhs = true) : valG e₀ rhs = d * valG e₀ y * d⁻¹ := by
  have := stepIs_sound e₀ hd epsT_tblW_nil h
  rwa [wordVal_nil, show (1 : Multiplicative (ZMod 2) × G12).2 = 1 from rfl, dW_one] at this

theorem stepIs_inv (hd : CentralSwap e₀ α d) {ws y rhs : List (Fin 5 × Bool)}
    (hws : epsT (tblW ws) = 0) (h : stepIs α (invW ws) y rhs = true) :
    valG e₀ rhs = dW e₀ d (wordVal ws).2⁻¹ * valG e₀ y * (dW e₀ d (wordVal ws).2⁻¹)⁻¹ := by
  have := stepIs_sound e₀ hd (epsT_tblW_invW hws) h
  rwa [wordVal_invW, show ((wordVal ws)⁻¹).2 = (wordVal ws).2⁻¹ from Prod.snd_inv _] at this

theorem stepIs_invS (hd : CentralSwap e₀ α d) {y rhs : List (Fin 5 × Bool)}
    (hws : epsT (tblW wS) = 0) (h : stepIs α (invW wS) y rhs = true) :
    valG e₀ rhs = dW e₀ d μS⁻¹ * valG e₀ y * (dW e₀ d μS⁻¹)⁻¹ :=
  stepIs_inv e₀ hd hws h

section Cert

theorem rel4P_trivial (d : G) : ∀ r ∈ rel4P, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1 := by
  obtain ⟨hP, -⟩ := lemma4_parts
  have hlt : ∀ r ∈ rel4P, ∀ l ∈ r, l.1.val < 6 := by decide
  intro r hr
  have hcongr : FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) =
      FreeGroup.lift (fun i => valG e₀ (sub4 i)) (FreeGroup.mk r) := by
    apply lift_mk_congr
    intro l hl
    have h6 := hlt r hr l hl
    obtain ⟨⟨i, hi⟩, b⟩ := l
    simp only at h6 ⊢
    interval_cases i <;> rfl
  rw [hcongr]
  have h1 : (fun i => valG e₀ (sub4 i)) =
      fun i => jH e₀ (FreeGroup.lift baseM (FreeGroup.mk (sub4 i))) := by
    funext i
    unfold valG
    rw [wordVal_def]
  rw [h1, lift_comp_substW (jH e₀) sub4 baseM r, ← wordVal_def]
  have hr' := List.all_eq_true.1 hP r hr
  rw [wordVal_eq_one_of_tblEq hr', map_one]

theorem yosh4 (he2 : orderOf e = 2) (hd : CentralSwap e₀ α d) (hα : α = 0 ∨ α = 1) :
    ∃ β : ℕ, (β = 0 ∨ β = 1) ∧
      ∀ r ∈ rel4 α β, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1 := by
  obtain ⟨β, hβ, hx⟩ := xElt_eq_zWord e₀ he2 hd hα
  refine ⟨β, hβ, ?_⟩
  obtain ⟨-, hstep, -, -⟩ := lemma4_parts
  obtain ⟨hstepα, -, hzok⟩ := hstep α (by omega)
  have hzβ := hzok β (by omega)
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq] at hstepα
  obtain ⟨hws, hs3, hc, hrs, hA, hB, hU, hR, hE', hA', hB', hU', -⟩ := hstepα
  simp only [zOK, Bool.and_eq_true] at hzβ
  obtain ⟨hz1, hz2, hz3⟩ := hzβ
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact rel4P_trivial e₀ d r hr
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd.sq
  have hvE : valG e₀ wE = e := valG_tau e₀ he2
  have hs : valG e₀ wS = ιH e₀ μS := valG_eq_ιH e₀ hws
  have hc' : valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB = cG e₀ := by
    have h := valG_eq_of_tblEq e₀ hc
    rwa [valG_append, valG_append, valG_append, valG_wJ] at h
  have hRS : (valG e₀ wR)⁻¹ * valG e₀ wS * valG e₀ wR = (valG e₀ wS)⁻¹ := by
    have h := valG_eq_of_tblEq e₀ hrs
    rwa [valG_append, valG_append, valG_invW, valG_invW] at h
  have hS3 : valG e₀ wS * valG e₀ wS * valG e₀ wS = 1 := by
    have h := valG_eq_one_of_tblEq e₀ hs3
    rwa [valG_append, valG_append] at h
  have hD'eq : dW e₀ d μS⁻¹ = (valG e₀ wS)⁻¹ * d * valG e₀ wS := by
    rw [hs]
    unfold dW
    rw [map_inv, inv_inv]
  have hD'D' : dW e₀ d μS⁻¹ * dW e₀ d μS⁻¹ = 1 := by
    rw [hD'eq]
    calc (valG e₀ wS)⁻¹ * d * valG e₀ wS * ((valG e₀ wS)⁻¹ * d * valG e₀ wS)
        = (valG e₀ wS)⁻¹ * (d * d) * valG e₀ wS := by group
      _ = 1 := by rw [hd.sq]; group
  have hD'i : (dW e₀ d μS⁻¹)⁻¹ = dW e₀ d μS⁻¹ := inv_eq_of_mul_eq_one_right hD'D'
  have fA : valG e₀ wA * cG e₀ ^ α = d * valG e₀ wA * d⁻¹ := by
    have h := stepIs_nil e₀ hd hA
    rwa [valG_append, valG_powW, valG_wJ] at h
  have fB : valG e₀ wB * cG e₀ ^ α = d * valG e₀ wB * d⁻¹ := by
    have h := stepIs_nil e₀ hd hB
    rwa [valG_append, valG_powW, valG_wJ] at h
  have fU : valG e₀ wU = d * valG e₀ wU * d⁻¹ := stepIs_nil e₀ hd hU
  have fR : valG e₀ wR = d * valG e₀ wR * d⁻¹ := stepIs_nil e₀ hd hR
  have fE' : valG e₀ wE * valG e₀ wA * valG e₀ wA =
      dW e₀ d μS⁻¹ * valG e₀ wE * (dW e₀ d μS⁻¹)⁻¹ := by
    have h := stepIs_invS e₀ hd hws hE'
    rwa [valG_append, valG_append] at h
  have fA' : valG e₀ wA = dW e₀ d μS⁻¹ * valG e₀ wA * (dW e₀ d μS⁻¹)⁻¹ :=
    stepIs_invS e₀ hd hws hA'
  have fB' : valG e₀ wB * (valG e₀ wA * valG e₀ wA) ^ α =
      dW e₀ d μS⁻¹ * valG e₀ wB * (dW e₀ d μS⁻¹)⁻¹ := by
    have h := stepIs_invS e₀ hd hws hB'
    rwa [valG_append, valG_powW, valG_append] at h
  have fU' : valG e₀ wU = dW e₀ d μS⁻¹ * valG e₀ wU * (dW e₀ d μS⁻¹)⁻¹ :=
    stepIs_invS e₀ hd hws hU'
  have hE : d * valG e₀ wE * d =
      valG e₀ wE * (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) := by
    have h := hd.conj_e
    rw [hdi] at h
    rw [hvE, hc']
    exact h
  have hA2 : d * valG e₀ wA * d =
      valG e₀ wA * (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ α := by
    rw [hc']
    have h := fA
    rw [hdi] at h
    exact h.symm
  have hB2 : d * valG e₀ wB * d =
      valG e₀ wB * (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ α := by
    rw [hc']
    have h := fB
    rw [hdi] at h
    exact h.symm
  have hU2 : d * valG e₀ wU * d = valG e₀ wU := by
    have h := fU
    rw [hdi] at h
    exact h.symm
  have hE2 : dW e₀ d μS⁻¹ * valG e₀ wE * dW e₀ d μS⁻¹ = valG e₀ wE * valG e₀ wA * valG e₀ wA := by
    have h := fE'
    rw [hD'i] at h
    exact h.symm
  have hA3 : dW e₀ d μS⁻¹ * valG e₀ wA * dW e₀ d μS⁻¹ = valG e₀ wA := by
    have h := fA'
    rw [hD'i] at h
    exact h.symm
  have hB3 : dW e₀ d μS⁻¹ * valG e₀ wB * dW e₀ d μS⁻¹ =
      valG e₀ wB * (valG e₀ wA * valG e₀ wA) ^ α := by
    have h := fB'
    rw [hD'i] at h
    exact h.symm
  have hU3 : dW e₀ d μS⁻¹ * valG e₀ wU * dW e₀ d μS⁻¹ = valG e₀ wU := by
    have h := fU'
    rw [hD'i] at h
    exact h.symm
  have hR2 : valG e₀ wR * d = d * valG e₀ wR := by
    calc valG e₀ wR * d = (d * valG e₀ wR * d⁻¹) * d := by rw [← fR]
      _ = d * valG e₀ wR := by group
  have hzval : valG e₀ (zWord α β) = valG e₀ wU ^ α *
      (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ β * valG e₀ wE ^ β := by
    unfold zWord
    rw [valG_append, valG_append, valG_powW, valG_powW, valG_powW, valG_wJ, hc']
  have hz : dW e₀ d μS⁻¹ * d * (valG e₀ wS * d * (valG e₀ wS)⁻¹) = valG e₀ wU ^ α *
      (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ β * valG e₀ wE ^ β := by
    rw [← hzval, ← hx]
    unfold xElt
    rw [hs]
    rfl
  have hZ1 : (valG e₀ wU ^ α * (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ β *
      valG e₀ wE ^ β) * (valG e₀ wU ^ α * (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ β *
      valG e₀ wE ^ β) = 1 := by
    have h := valG_eq_one_of_tblEq e₀ hz1
    rwa [valG_append, hzval] at h
  have hD'' : dW e₀ d (wordVal wS).2 = valG e₀ wS * d * (valG e₀ wS)⁻¹ := by
    rw [hs]
    rfl
  have hZ2 : (valG e₀ wU ^ α * (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ β *
      valG e₀ wE ^ β) * (valG e₀ wB * valG e₀ wB) ^ β =
      (valG e₀ wS * d * (valG e₀ wS)⁻¹) * (valG e₀ wU ^ α *
      (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ β * valG e₀ wE ^ β) *
      (valG e₀ wS * d * (valG e₀ wS)⁻¹)⁻¹ := by
    have h := stepIs_sound e₀ hd hws hz2
    rw [valG_append, valG_powW, valG_append, hzval, hD''] at h
    exact h
  have hZ3 : (valG e₀ wU ^ α * (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ β *
      valG e₀ wE ^ β) * (valG e₀ wB * valG e₀ wB) ^ β * (valG e₀ wU ^ α *
      (valG e₀ wA * valG e₀ wA * valG e₀ wB * valG e₀ wB) ^ β * valG e₀ wE ^ β) =
      (valG e₀ wB * valG e₀ wB) ^ β := by
    have h := valG_eq_of_tblEq e₀ hz3
    simp only [valG_append, valG_powW, hzval] at h
    exact h
  exact rel4D_trivial (gen4 e₀ d) α β hd.sq hD'D' hE hA2 hB2 hU2 hE2 hA3 hB3 hU3 hD'eq.symm hS3
    hR2 hRS hz hZ1 hZ2 hZ3 r hr

end Cert

end Lemma4

end CFSG.EvenSporadicStandard.M12Std.Yosh
