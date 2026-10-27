module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshQCert

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp

section XDet

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

variable {d : G} {α : ℕ}

theorem comm_of_conj_eq {X y : G} (h : X * y * X⁻¹ = y) : X * y = y * X := by
  calc X * y = (X * y * X⁻¹) * X := by group
    _ = y * X := by rw [h]

theorem tblEq_conj_of_valG {X : G} {a : Multiplicative (ZMod 2)} {σ : G12}
    (hX : X = jH e₀ (a, σ)) {T : Table} (hT : Rep 14 T (kapP (a, (σ : Equiv.Perm (Fin 12)))))
    {y f : List (Fin 5 × Bool)} (h : valG e₀ f = X * valG e₀ y * X⁻¹) :
    tblEq 14 (compT 14 T (tblW y)) (compT 14 (tblW f) T) = true := by
  have h1 : valG e₀ f * X = X * valG e₀ y := by
    rw [h]; group
  rw [hX] at h1
  unfold valG at h1
  rw [← map_mul, ← map_mul] at h1
  have h2 := jH_injective e₀ h1
  have h3 : kapM (wordVal f * (a, σ)) = kapM ((a, σ) * wordVal y) := by rw [h2]
  rw [map_mul, map_mul] at h3
  have r1 := Rep.compT hT (rep_tblW y)
  have r2 := Rep.compT (rep_tblW f) hT
  exact (tblEq_iff_eq r1 r2).2 h3.symm

section Cert


theorem xElt_eq_zWord (he2 : orderOf e = 2) (hd : CentralSwap e₀ α d) (hα : α = 0 ∨ α = 1) :
    ∃ β : ℕ, (β = 0 ∨ β = 1) ∧ xElt e₀ d wS = valG e₀ (zWord α β) := by
  obtain ⟨-, hstep, hdet, -⟩ := lemma4_parts
  have hαlt : α < 2 := by omega
  obtain ⟨hstepα, hxokα, -⟩ := hstep α hαlt
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq] at hstepα
  obtain ⟨hws, hs3, -⟩ := hstepα
  simp only [xOK, Bool.and_eq_true] at hxokα
  obtain ⟨hdef, hxe, hxc⟩ := hxokα
  have hdefs : ∀ y ∈ [wA, wB, wU], (xAct α wS y).isSome = true := List.all_eq_true.1 hdef
  set X : G := xElt e₀ d wS with hXdef
  set μ : G12 := (wordVal wS).2 with hμ
  have hpm : wordVal wS = (1, μ) := Prod.ext (fst_eq_one_of_epsT hws) rfl
  have hvE : valG e₀ wE = e := valG_tau e₀ he2
  have hvJ : valG e₀ wJ = cG e₀ := valG_wJ e₀
  have hcommE : X * e = e * X := by
    unfold xIs at hxe
    cases hxa : xAct α wS wE with
    | none => simp [hxa] at hxe
    | some f =>
      rw [hxa] at hxe
      have h1 := xAct_sound e₀ hd hws hxa
      have h2 := valG_eq_of_tblEq e₀ hxe
      rw [hvE] at h1 h2
      exact comm_of_conj_eq (h1.symm.trans h2)
  have hcommC : X * cG e₀ = cG e₀ * X := by
    unfold xIs at hxc
    cases hxa : xAct α wS wJ with
    | none => simp [hxa] at hxc
    | some f =>
      rw [hxa] at hxc
      have h1 := xAct_sound e₀ hd hws hxa
      have h2 := valG_eq_of_tblEq e₀ hxc
      rw [hvJ] at h1 h2
      exact comm_of_conj_eq (h1.symm.trans h2)
  have hXHc : X ∈ HcG e₀ :=
    ⟨mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hcommE.symm,
      mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hcommC.symm⟩
  obtain ⟨k, a, σ, hk, hXj, hrep⟩ := exists_index_of_mem_Hc e₀ hXHc
  have hcond : condX α yEl[k]! = true := by
    unfold condX
    rw [List.all_eq_true]
    intro y hy
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (hdefs y hy)
    have hres : xRes α y = f := by unfold xRes; rw [hf]; rfl
    rw [hres]
    exact tblEq_conj_of_valG e₀ hXj hrep (xAct_sound e₀ hd hws hf)
  have hdet1 := List.all_eq_true.1 hdet α (by simp; omega)
  have hdet2 := List.all_eq_true.1 hdet1 k (List.mem_range.2 hk)
  simp only [hcond, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hdet2
  obtain ⟨hcommS, hrest⟩ := hdet2
  have hq : (wordVal (invW wS)) * (a, σ) * wordVal wS = (a, μ⁻¹ * σ * μ) := by
    rw [wordVal_invW, hpm]
    refine Prod.ext ?_ ?_
    · simp; exact inv_one
    · simp
  have hrepq : Rep 14 (compT 14 (compT 14 (tblW (invW wS)) yEl[k]!) (tblW wS))
      (kapP (a, ((μ⁻¹ * σ * μ : G12) : Equiv.Perm (Fin 12)))) := by
    have h0 := Rep.compT (Rep.compT (rep_tblW (invW wS)) hrep) (rep_tblW wS)
    have h1 : kapM (wordVal (invW wS)) * kapP (a, (σ : Equiv.Perm (Fin 12))) * kapM (wordVal wS) =
        kapP (a, ((μ⁻¹ * σ * μ : G12) : Equiv.Perm (Fin 12))) := by
      have h2 : kapM (wordVal (invW wS) * (a, σ) * wordVal wS) = kapM (a, μ⁻¹ * σ * μ) := by
        rw [hq]
      rw [map_mul, map_mul] at h2
      exact h2
    rw [h1] at h0
    exact h0
  have hcommq : (μ⁻¹ * σ * μ) * Jelt = Jelt * (μ⁻¹ * σ * μ) := commJ_of_commT hrepq hcommS
  have hs : valG e₀ wS = ιH e₀ μ := valG_eq_ιH e₀ hws
  set s : G := ιH e₀ μ with hs_def
  have hs3' : s * s * s = 1 := by
    have h := wordVal_eq_one_of_tblEq hs3
    have h' : valG e₀ (wS ++ wS ++ wS) = 1 := by unfold valG; rw [h, map_one]
    rwa [valG_append, valG_append, hs] at h'
  have hsinv : s⁻¹ = s * s := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hs3')
  have hss : s⁻¹ * s⁻¹ = s := by
    calc s⁻¹ * s⁻¹ = s * (s * s * s) := by rw [hsinv]; group
      _ = s := by rw [hs3', mul_one]
  have hD'eq : dW e₀ d μ⁻¹ = s⁻¹ * d * s := by
    unfold dW
    rw [map_inv, inv_inv]
  have hD''eq : dW e₀ d μ = s * d * s⁻¹ := rfl
  have hX : X = dW e₀ d μ⁻¹ * d * dW e₀ d μ := rfl
  have hkey : s⁻¹ * X * s = dW e₀ d μ * X * (dW e₀ d μ)⁻¹ := by
    have e1 : s⁻¹ * X * s = (s⁻¹ * s⁻¹) * d * s * d * s * d := by
      rw [hX, hD'eq, hD''eq]; group
    have e2 : dW e₀ d μ * X * (dW e₀ d μ)⁻¹ = s * d * (s⁻¹ * s⁻¹) * d * s * d := by
      rw [hX, hD'eq, hD''eq]; group
    rw [e1, e2, hss]
  have hconjD := dW_conj_jH e₀ hd μ a σ hcommq
  have hconjs : s⁻¹ * X * s = jH e₀ (a, μ⁻¹ * σ * μ) := by
    have hp : ((1 : Multiplicative (ZMod 2)), μ)⁻¹ * (a, σ) * (1, μ) = (a, μ⁻¹ * σ * μ) :=
      Prod.ext (by simp; exact inv_one) (by simp)
    rw [hXj, hs_def, ιH_eq_jH, ← hp, map_mul, map_mul,
      show jH e₀ ((1, μ)⁻¹) = (jH e₀ (1, μ))⁻¹ from map_inv (jH e₀) _]
  have hjq : jH e₀ (a, μ⁻¹ * σ * μ) = jH e₀ (a, σ) * ιH e₀ (μ * Jelt * μ⁻¹) ^
      ((Multiplicative.toAdd a).val + α * lamP ((μ⁻¹ * σ * μ : G12) : Equiv.Perm (Fin 12))) := by
    rw [← hconjs, hkey, hXj, hconjD]
  have hq2 : (a, μ⁻¹ * σ * μ) = (a, σ) * (1, μ * Jelt * μ⁻¹) ^
      ((Multiplicative.toAdd a).val + α * lamP ((μ⁻¹ * σ * μ : G12) : Equiv.Perm (Fin 12))) := by
    apply jH_injective e₀
    rw [map_mul, map_pow, hjq]
    rfl
  have hval : wordVal (wS ++ wJ ++ invW wS) = (1, μ * Jelt * μ⁻¹) := by
    rw [wordVal_append, wordVal_append, wordVal_invW, hpm, wordVal_wJ]
    refine Prod.ext ?_ ?_
    · simp; exact inv_one
    · simp
  have hsEqn : sEqn α yEl[k]! = true := by
    simp only [sEqn]
    rw [epsT_eq hrepq, lamT_eq hrepq]
    have hpow := Rep.powT (by norm_num : 14 < 2 ^ 32) (rep_tblW (wS ++ wJ ++ invW wS))
      ((Multiplicative.toAdd a).val + α * lamP ((μ⁻¹ * σ * μ : G12) : Equiv.Perm (Fin 12)))
    have r2 := Rep.compT hrep hpow
    rw [hval] at r2
    refine (tblEq_iff_eq hrepq r2).2 ?_
    have h7 := congrArg kapM hq2
    rw [map_mul, map_pow] at h7
    exact h7
  simp only [hsEqn, Bool.not_true, Bool.false_or] at hrest
  obtain ⟨β, hβ, hβt⟩ := List.any_eq_true.1 hrest
  refine ⟨β, by simpa using hβ, ?_⟩
  have h5 := (tblEq_iff_eq hrep (rep_tblW (zWord α β))).1 hβt
  have h6 : (a, σ) = wordVal (zWord α β) := kapM_injective h5
  rw [hXj, h6]
  rfl

end Cert

end XDet

end CFSG.EvenSporadicStandard.M12Std.Yosh
