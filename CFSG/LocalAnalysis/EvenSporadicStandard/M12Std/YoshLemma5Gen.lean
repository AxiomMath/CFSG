module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma4

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b

section Gen5

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

@[expose] noncomputable def gen5 (d : G) (α β : ℕ) : Fin 9 → G := fun i =>
  if i = 7 then sG e₀ else FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk (toQ α β i))

variable {d : G} {α β : ℕ}

theorem qGens_size (hα : α < 2) (hβ : β < 2) : (qGens α β).size = 8 := by
  interval_cases α <;> interval_cases β <;> rfl

section Cert


theorem qTrivial (hα : α < 2) (hβ : β < 2) {H : Type*} [Group H] (x : Fin 8 → H)
    (hx : ∀ r ∈ rel4 α β, FreeGroup.lift x (FreeGroup.mk r) = 1) {w : List (Fin 8 × Bool)}
    (hw : tblEq 24 (modelT 24 8 (qGens α β) w) (idT 24) = true) :
    FreeGroup.lift x (FreeGroup.mk w) = 1 := by
  exact lift_eq_one_of_modelTrivial (by norm_num) (qGens_size hα hβ) (qModelOK α β hα hβ) x hx hw

theorem gen5_relNQL (hα : α < 2) (hβ : β < 2)
    (hrel : ∀ r ∈ rel4 α β, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1) :
    ∀ r ∈ relNQL α β, FreeGroup.lift (gen5 e₀ d α β) (FreeGroup.mk (swN r)) = 1 := by
  intro r hr
  have hne : ∀ α β : ℕ, α < 2 → β < 2 → ∀ r ∈ relNQL α β, ∀ l ∈ swN r, l.1 ≠ (7 : Fin 9) := by
    intro α β hα hβ
    interval_cases α <;> interval_cases β <;> decide
  have hcongr : FreeGroup.lift (gen5 e₀ d α β) (FreeGroup.mk (swN r)) =
      FreeGroup.lift (fun i => FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk (toQ α β i)))
        (FreeGroup.mk (swN r)) := by
    apply lift_mk_congr
    intro l hl
    simp [gen5, hne α β hα hβ r hr l hl]
  rw [hcongr]
  have h1 := lift_comp_substW (MonoidHom.id G) (toQ α β) (gen4 e₀ d) (swN r)
  simp only [MonoidHom.id_apply] at h1
  rw [h1]
  obtain ⟨-, -, -, -, -, -, h5, -⟩ := lemma5_parts
  have h6 := (h5 α β hα hβ).1
  unfold relNQCheck wordsTrivial at h6
  have h7 := List.all_eq_true.1 h6 (substW (toQ α β) (swN r)) (List.mem_map.2 ⟨r, hr, rfl⟩)
  exact qTrivial hα hβ (gen4 e₀ d) hrel h7

theorem wordVal_wSP : wordVal wSP = (1, ⟨sP, sP_mem_M12⟩) := by
  have h : wSP = [((4 : Fin 5), true)] ++ [((3 : Fin 5), true)] ++ [((3 : Fin 5), true)] ++
      [((4 : Fin 5), true)] := rfl
  rw [h, wordVal_append, wordVal_append, wordVal_append, wordVal_letter, wordVal_letter]
  refine Prod.ext (by simp [baseM]) (Subtype.ext ?_)
  simp [baseM, sP, mul_assoc]

theorem valG_wSP : valG e₀ wSP = sG e₀ := by
  unfold valG
  rw [wordVal_wSP, sG_def]
  rfl

theorem gen5_a1 : gen5 e₀ d α β 0 = valG e₀ wA1 := by
  have h : gen5 e₀ d α β 0 =
      FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk ([(1, true)] ++ [(2, true)])) := by
    simp [gen5, toQ]
  rw [h]
  simp only [lift_mk_append, lift_mk_single, wA1, valG_append]
  rfl

theorem gen5_a2 : gen5 e₀ d α β 1 = valG e₀ wA2 := by
  have h : gen5 e₀ d α β 1 = FreeGroup.lift (gen4 e₀ d)
      (FreeGroup.mk ([(1, true)] ++ [(1, true)] ++ [(3, true)] ++ [(5, true)])) := by
    simp [gen5, toQ]
  rw [h]
  simp only [lift_mk_append, lift_mk_single, wA2, valG_append]
  rfl

theorem gen5_b1 : gen5 e₀ d α β 2 = valG e₀ wB1 := by
  have h : gen5 e₀ d α β 2 =
      FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk ([(1, true)] ++ [(2, false)])) := by
    simp [gen5, toQ]
  have h2 : FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk [(2, false)]) = (gen4 e₀ d 2)⁻¹ := by
    have := lift_mk_invW (gen4 e₀ d) [(2, true)]
    rw [lift_mk_single] at this
    exact this
  rw [h]
  simp only [lift_mk_append, lift_mk_single, h2, wB1, valG_append, valG_invW]
  rfl

theorem gen5_b2 : gen5 e₀ d α β 3 = valG e₀ wB2 := by
  have h : gen5 e₀ d α β 3 = FreeGroup.lift (gen4 e₀ d)
      (FreeGroup.mk ([(1, false)] ++ [(2, false)] ++ [(5, true)])) := by
    simp [gen5, toQ]
  have h1 : FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk [(1, false)]) = (gen4 e₀ d 1)⁻¹ := by
    have := lift_mk_invW (gen4 e₀ d) [(1, true)]
    rw [lift_mk_single] at this
    exact this
  have h2 : FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk [(2, false)]) = (gen4 e₀ d 2)⁻¹ := by
    have := lift_mk_invW (gen4 e₀ d) [(2, true)]
    rw [lift_mk_single] at this
    exact this
  rw [h]
  simp only [lift_mk_append, lift_mk_single, h1, h2, wB2, valG_append, valG_invW]
  rfl

theorem gen5_d : gen5 e₀ d α β 4 = d := by
  have h : gen5 e₀ d α β 4 = FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk [(6, true)]) := by
    simp [gen5, toQ]
  rw [h, lift_mk_single]
  rfl

theorem gen5_e : gen5 e₀ d α β 5 = valG e₀ wE := by
  have h : gen5 e₀ d α β 5 = FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk [(0, true)]) := by
    simp [gen5, toQ]
  rw [h, lift_mk_single]
  rfl

theorem gen5_s : gen5 e₀ d α β 7 = sG e₀ := by simp [gen5]

theorem gen5_t : gen5 e₀ d α β 8 = valG e₀ wT := by
  have h : gen5 e₀ d α β 8 = FreeGroup.lift (gen4 e₀ d)
      (FreeGroup.mk ([(1, true)] ++ [(1, true)] ++ [(2, true)] ++ [(3, true)])) := by
    simp [gen5, toQ]
  rw [h]
  simp only [lift_mk_append, lift_mk_single, wT, valG_append]
  rfl

theorem gen5_x : gen5 e₀ d α β 6 = dW e₀ d μS⁻¹ *
    (gen5 e₀ d α β 8 * gen5 e₀ d α β 0 * gen5 e₀ d α β 1 * gen5 e₀ d α β 3 *
      gen5 e₀ d α β 4 * gen5 e₀ d α β 5 ^ β) ^ α := by
  have h : gen5 e₀ d α β 6 = FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk (toQ α β 6)) := by
    simp [gen5]
  have hT : gen5 e₀ d α β 8 = FreeGroup.lift (gen4 e₀ d)
      (FreeGroup.mk [(1, true), (1, true), (2, true), (3, true)]) := by simp [gen5, toQ]
  have hA1 : gen5 e₀ d α β 0 = FreeGroup.lift (gen4 e₀ d)
      (FreeGroup.mk [(1, true), (2, true)]) := by simp [gen5, toQ]
  have hA2 : gen5 e₀ d α β 1 = FreeGroup.lift (gen4 e₀ d)
      (FreeGroup.mk [(1, true), (1, true), (3, true), (5, true)]) := by simp [gen5, toQ]
  have hB2 : gen5 e₀ d α β 3 = FreeGroup.lift (gen4 e₀ d)
      (FreeGroup.mk [(1, false), (2, false), (5, true)]) := by simp [gen5, toQ]
  have hD : gen5 e₀ d α β 4 = FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk [(6, true)]) := by
    simp [gen5, toQ]
  have hE : gen5 e₀ d α β 5 = FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk [(0, true)]) := by
    simp [gen5, toQ]
  rw [hT, hA1, hA2, hB2, hD, hE, h]
  simp only [toQ, lift_mk_append, lift_mk_single, lift_mk_powW]
  rfl

end Cert

end Gen5

end CFSG.EvenSporadicStandard.M12Std.Yosh
