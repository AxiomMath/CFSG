module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshN

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp

section Conj

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

variable {d : G} {α : ℕ}

theorem ιH_eq_jH (m : G12) : ιH e₀ m = jH e₀ (1, m) := rfl

theorem dW_conj_jH (hd : CentralSwap e₀ α d) (μ : G12) (a : Multiplicative (ZMod 2)) (σ : G12)
    (hcomm : (μ⁻¹ * σ * μ) * Jelt = Jelt * (μ⁻¹ * σ * μ)) :
    dW e₀ d μ * jH e₀ (a, σ) * (dW e₀ d μ)⁻¹ =
      jH e₀ (a, σ) * ιH e₀ (μ * Jelt * μ⁻¹) ^
        ((Multiplicative.toAdd a).val + α * lamP ((μ⁻¹ * σ * μ : G12) : Equiv.Perm (Fin 12))) := by
  set σ' : G12 := μ⁻¹ * σ * μ with hσ'
  have hconj := hd.conj_jH a σ' hcomm
  have hw : jH e₀ (a, σ) = ιH e₀ μ * jH e₀ (a, σ') * (ιH e₀ μ)⁻¹ := by
    rw [ιH_eq_jH, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (by simp; exact inv_one) ?_
    show σ = μ * σ' * μ⁻¹
    rw [hσ']; group
  unfold dW
  have hinv : (ιH e₀ μ * d * (ιH e₀ μ)⁻¹)⁻¹ = ιH e₀ μ * d⁻¹ * (ιH e₀ μ)⁻¹ := by group
  have hcμ : ιH e₀ μ * cG e₀ * (ιH e₀ μ)⁻¹ = ιH e₀ (μ * Jelt * μ⁻¹) := by
    rw [cG_def, map_mul, map_mul, map_inv]
  calc ιH e₀ μ * d * (ιH e₀ μ)⁻¹ * jH e₀ (a, σ) * (ιH e₀ μ * d * (ιH e₀ μ)⁻¹)⁻¹
      = ιH e₀ μ * (d * jH e₀ (a, σ') * d⁻¹) * (ιH e₀ μ)⁻¹ := by rw [hinv, hw]; group
    _ = ιH e₀ μ * (jH e₀ (a, σ') * cG e₀ ^ ((Multiplicative.toAdd a).val +
          α * lamP (σ' : Equiv.Perm (Fin 12)))) * (ιH e₀ μ)⁻¹ := by rw [hconj]
    _ = (ιH e₀ μ * jH e₀ (a, σ') * (ιH e₀ μ)⁻¹) *
        (ιH e₀ μ * cG e₀ * (ιH e₀ μ)⁻¹) ^ ((Multiplicative.toAdd a).val +
          α * lamP (σ' : Equiv.Perm (Fin 12))) := by rw [conj_pow]; group
    _ = _ := by rw [← hw, hcμ]

theorem valG_eq_ιH {w : List (Fin 5 × Bool)} (hw : epsT (tblW w) = 0) :
    valG e₀ w = ιH e₀ (wordVal w).2 := by
  have h1 : wordVal w = (1, (wordVal w).2) := Prod.ext (fst_eq_one_of_epsT hw) rfl
  unfold valG
  rw [h1]
  rfl

theorem epsT_tblW_nil : epsT (tblW []) = 0 := by
  rw [epsT_tblW, wordVal_nil]
  rfl

theorem epsT_tblW_invW {w : List (Fin 5 × Bool)} (hw : epsT (tblW w) = 0) :
    epsT (tblW (invW w)) = 0 := by
  rw [epsT_tblW, wordVal_invW, Prod.fst_inv, fst_eq_one_of_epsT hw]
  rfl

theorem stepW_sound (hd : CentralSwap e₀ α d) {wm y y' : List (Fin 5 × Bool)}
    (hwm : epsT (tblW wm) = 0) (h : stepW α wm y = some y') :
    valG e₀ y' = dW e₀ d (wordVal wm).2 * valG e₀ y * (dW e₀ d (wordVal wm).2)⁻¹ := by
  unfold stepW at h
  split_ifs at h with hc
  rw [Option.some.injEq] at h
  subst h
  set μ : G12 := (wordVal wm).2 with hμ
  have hpm : wordVal wm = (1, μ) := Prod.ext (fst_eq_one_of_epsT hwm) rfl
  set p : Multiplicative (ZMod 2) × G12 := wordVal y with hp
  have hval : wordVal (invW wm ++ y ++ wm) = (p.1, μ⁻¹ * p.2 * μ) := by
    rw [wordVal_append, wordVal_append, wordVal_invW, hpm, ← hp]
    refine Prod.ext ?_ ?_
    · simp; exact inv_one
    · simp
  have hrep : Rep 14 (tblW (invW wm ++ y ++ wm)) (kapP (p.1, ((μ⁻¹ * p.2 * μ : G12) :
      Equiv.Perm (Fin 12)))) := by
    have := rep_tblW (invW wm ++ y ++ wm)
    rw [hval] at this
    exact this
  have heps := epsT_eq hrep
  have hlam := lamT_eq hrep
  have hcomm : (μ⁻¹ * p.2 * μ) * Jelt = Jelt * (μ⁻¹ * p.2 * μ) := by
    unfold commT at hc
    have h1 := Rep.compT hrep (rep_tblW wJ)
    have h2 := Rep.compT (rep_tblW wJ) hrep
    have h3 := (tblEq_iff_eq h1 h2).1 hc
    rw [wordVal_wJ] at h3
    have h4 : kapM ((p.1, μ⁻¹ * p.2 * μ) * (1, Jelt)) =
        kapM ((1, Jelt) * (p.1, μ⁻¹ * p.2 * μ)) := by
      rw [map_mul, map_mul]
      exact h3
    have h5 := congrArg Prod.snd (kapM_injective h4)
    simpa using h5
  have hkey := dW_conj_jH e₀ hd μ p.1 p.2 hcomm
  have hw : valG e₀ wm = ιH e₀ μ := valG_eq_ιH e₀ hwm
  have hcμ : ιH e₀ μ * cG e₀ * (ιH e₀ μ)⁻¹ = ιH e₀ (μ * Jelt * μ⁻¹) := by
    rw [cG_def, map_mul, map_mul, map_inv]
  rw [heps, hlam, valG_append, valG_powW, valG_append, valG_append, valG_invW, valG_wJ, hw, hcμ]
  have hy : valG e₀ y = jH e₀ (p.1, p.2) := rfl
  rw [hy, hkey]

theorem dW_one : dW e₀ d (1 : G12) = d := by
  simp [dW]

@[expose] noncomputable def xElt (d : G) (ws : List (Fin 5 × Bool)) : G :=
  dW e₀ d (wordVal ws).2⁻¹ * d * dW e₀ d (wordVal ws).2

theorem xAct_sound (hd : CentralSwap e₀ α d) {ws y y' : List (Fin 5 × Bool)}
    (hws : epsT (tblW ws) = 0) (h : xAct α ws y = some y') :
    valG e₀ y' = xElt e₀ d ws * valG e₀ y * (xElt e₀ d ws)⁻¹ := by
  unfold xAct at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨y₁, h1, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨y₂, h2, h3⟩ := h
  have hws' : epsT (tblW (invW ws)) = 0 := epsT_tblW_invW hws
  have e1 := stepW_sound e₀ hd hws h1
  have e2 := stepW_sound e₀ hd epsT_tblW_nil h2
  have e3 := stepW_sound e₀ hd hws' h3
  rw [wordVal_nil] at e2
  rw [wordVal_invW] at e3
  have hsnd : ((wordVal ws)⁻¹).2 = (wordVal ws).2⁻¹ := Prod.snd_inv _
  rw [hsnd] at e3
  have hone : (1 : Multiplicative (ZMod 2) × G12).2 = 1 := rfl
  rw [hone, dW_one] at e2
  rw [e3, e2, e1]
  unfold xElt
  group

end Conj

section Index

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

theorem exists_index_of_mem_Hc {y : G} (hy : y ∈ HcG e₀) :
    ∃ (k : ℕ) (a : Multiplicative (ZMod 2)) (σ : G12), k < 384 ∧ y = jH e₀ (a, σ) ∧
      Rep 14 yEl[k]! (kapP (a, (σ : Equiv.Perm (Fin 12)))) := by
  obtain ⟨⟨a, σ⟩, rfl⟩ := (mem_range_jH e₀).2 hy.1
  obtain ⟨k, hk, hkY⟩ := yelt_surj (ΘE e₀ ⟨jH e₀ (a, σ), hy⟩)
  refine ⟨k, a, σ, hk, rfl, ?_⟩
  have hperm : yperm k = kapP (a, (σ : Equiv.Perm (Fin 12))) := by
    rw [← yelt_coe' hk, hkY, ΘE_coe, ρH_apply, e₀_jH e₀ a σ]
  have := yrep hk
  rw [hperm] at this
  exact this

end Index


end CFSG.EvenSporadicStandard.M12Std.Yosh
