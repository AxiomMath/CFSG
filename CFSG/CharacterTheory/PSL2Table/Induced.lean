module

public import CFSG.CharacterTheory.PSL2Table.Partition
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Wreathed.CentralSL2.CharacterTools
public import CFSG.CharacterTheory.DirectProductCharacters
public import CFSG.CharacterTheory.PSL2Table.Fixed
public import CFSG.CharacterTheory.PermutationCharacterOrbits

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG.TwoRankLowerBound.Helpers

section General

variable {G : Type} [Group G] [Fintype G]

theorem inducedFunction_apply_TI {H : Subgroup G} {w : G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hinv : ∀ x ∈ H, w * x * w⁻¹ = x⁻¹) (hw : w ∉ H) {x : G} (hx : x ∈ H)
    (hTI : ∀ g, g * x * g⁻¹ ∈ H ↔ g ∈ H ∨ w⁻¹ * g ∈ H) (φ : H → ℂ) :
    inducedFunction H φ x = φ ⟨x, hx⟩ + φ ⟨x⁻¹, H.inv_mem hx⟩ := by
  classical
  have hconj : ∀ g : G, g⁻¹ * x * g ∈ H ↔ g ∈ H ∨ g * w ∈ H := by
    intro g
    have h := hTI g⁻¹
    rw [inv_inv] at h
    rw [h, inv_mem_iff]
    have : w⁻¹ * g⁻¹ = (g * w)⁻¹ := by group
    rw [this, inv_mem_iff]
  have hH : ∀ g ∈ H, g⁻¹ * x * g = x := by
    intro g hg
    rw [hcomm g⁻¹ (H.inv_mem hg) x hx, inv_mul_cancel_right]
  have hHw : ∀ g, g * w ∈ H → g⁻¹ * x * g = x⁻¹ := by
    intro g hg
    have h1 : g⁻¹ * x * g = w * ((g * w)⁻¹ * x * (g * w)) * w⁻¹ := by group
    rw [h1, hH _ hg, hinv x hx]
  have hdisj : ∀ g ∈ H, g * w ∉ H := fun g hg hgw =>
    hw (by simpa using H.mul_mem (H.inv_mem hg) hgw)
  have hpt : ∀ g : G, (if hmem : g⁻¹ * x * g ∈ H then φ ⟨g⁻¹ * x * g, hmem⟩ else 0) =
      (if g ∈ H then φ ⟨x, hx⟩ else 0) + (if g * w ∈ H then φ ⟨x⁻¹, H.inv_mem hx⟩ else 0) := by
    intro g
    by_cases hg : g ∈ H
    · rw [dite_eq_left ((hconj g).mpr (Or.inl hg)), ite_eq_left hg, ite_eq_right (hdisj g hg),
        add_zero]
      congr 1
      exact Subtype.ext (hH g hg)
    · by_cases hgw : g * w ∈ H
      · rw [dite_eq_left ((hconj g).mpr (Or.inr hgw)), ite_eq_right hg, ite_eq_left hgw, zero_add]
        congr 1
        exact Subtype.ext (hHw g hgw)
      · rw [dite_eq_right (fun h => ((hconj g).mp h).elim hg hgw), ite_eq_right hg,
          ite_eq_right hgw, add_zero]
  unfold inducedFunction
  rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib, Finset.sum_ite,
    Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const_zero, add_zero, add_zero,
    Finset.sum_const, Finset.sum_const]
  have hc1 : (Finset.univ.filter (fun g : G => g ∈ H)).card = Nat.card H := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hc2 : (Finset.univ.filter (fun g : G => g * w ∈ H)).card = Nat.card H := by
    rw [← hc1]
    refine Finset.card_nbij' (fun g => g * w) (fun g => g * w⁻¹) ?_ ?_ ?_ ?_
    · intro g hg
      simpa using hg
    · intro g hg
      simpa using hg
    · intro g _
      simp
    · intro g _
      simp
  rw [hc1, hc2, nsmul_eq_mul, nsmul_eq_mul, ← mul_add, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]

theorem inducedFunction_apply_eq_zero {H : Subgroup G} (φ : H → ℂ) {y : G}
    (hy : ∀ g : G, g⁻¹ * y * g ∉ H) : inducedFunction H φ y = 0 := by
  classical
  unfold inducedFunction
  rw [Finset.sum_eq_zero (fun g _ => dite_eq_right (hy g)), mul_zero]

theorem inducedFunction_apply_one (H : Subgroup G) (φ : H → ℂ) :
    inducedFunction H φ 1 = (Nat.card G : ℂ) / Nat.card H * φ 1 := by
  classical
  unfold inducedFunction
  have hpt : ∀ g : G, (if hmem : g⁻¹ * 1 * g ∈ H then φ ⟨g⁻¹ * 1 * g, hmem⟩ else 0) = φ 1 := by
    intro g
    have hmem : g⁻¹ * 1 * g ∈ H := by simp [H.one_mem]
    rw [dite_eq_left hmem]
    congr 1
    exact Subtype.ext (by simp)
  rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Nat.card_eq_fintype_card]
  ring

omit [Fintype G] in
theorem not_conj_mem_of_mem_conjSet [Finite G] {H K : Subgroup G}
    (hHK : Nat.Coprime (Nat.card H) (Nat.card K)) {y : G} (hy : y ∈ conjSet H) (g : G) :
    g⁻¹ * y * g ∉ K := by
  intro hg
  exact disjoint_conjSet hHK hy ⟨hy.1, g⁻¹, by simpa using hg⟩

end General

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

@[expose] noncomputable def indSplit (α : splitTorus F →* ℂˣ) : PSL(2, F) → ℂ :=
  inducedFunction (splitTorus F) (fun t => (α t : ℂ))

@[expose] noncomputable def indNonsplit {ν : F} (β : nonsplitTorus ν →* ℂˣ) : PSL(2, F) → ℂ :=
  inducedFunction (nonsplitTorus ν) (fun s => (β s : ℂ))

@[expose] noncomputable def permChar (F : Type) [Field F] [Fintype F] : PSL(2, F) → ℂ :=
  fixedPointCount PSL(2, F) (ProjLine F)

theorem linear_mem_blocksVChar {K : Type} [Group K] [Fintype K] (α : K →* ℂˣ) :
    (fun k => (α k : ℂ)) ∈ BlocksVChar K :=
  AddSubgroup.subset_closure
    (CFSG.Wreathed.CentralSL2.monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp α))

theorem indSplit_mem_blocksVChar (α : splitTorus F →* ℂˣ) :
    indSplit α ∈ BlocksVChar PSL(2, F) :=
  inducedFunction_mem_blocksVChar _ (linear_mem_blocksVChar α)

theorem indNonsplit_mem_blocksVChar {ν : F} (β : nonsplitTorus ν →* ℂˣ) :
    indNonsplit β ∈ BlocksVChar PSL(2, F) :=
  inducedFunction_mem_blocksVChar _ (linear_mem_blocksVChar β)

omit [DecidableEq F] in
theorem permChar_eq_character :
    permChar F = (permutationRepresentation PSL(2, F) (ProjLine F)).character := by
  classical
  let _ : Fintype (ProjLine F) := Fintype.ofFinite _
  funext g
  rw [permutationRepresentation_character]
  rfl

theorem permChar_mem_blocksVChar : permChar F ∈ BlocksVChar PSL(2, F) := by
  classical
  let _ : Fintype (ProjLine F) := Fintype.ofFinite _
  rw [permChar_eq_character]
  exact CFSG.DirectProduct.representation_character_mem_blocksVChar _

omit [DecidableEq F] in
theorem permChar_conj (g x : PSL(2, F)) : permChar F (g * x * g⁻¹) = permChar F x := by
  classical
  let _ : Fintype (ProjLine F) := Fintype.ofFinite _
  rw [permChar_eq_character]
  exact Representation.char_conj _ x g

omit [DecidableEq F] in
theorem permChar_one : permChar F 1 = Fintype.card F + 1 := by
  rw [permChar, fixedPointCount, card_fixedBy_one, Nat.card_eq_fintype_card]
  push_cast
  ring

omit [DecidableEq F] in
theorem permChar_unip {t : F} (ht : t ≠ 0) : permChar F (mk (unip t)) = 1 := by
  rw [permChar, fixedPointCount, card_fixedBy_unip ht]
  simp

omit [DecidableEq F] in
theorem permChar_diag {a : Fˣ} (ha : (a : F) ^ 2 ≠ 1) : permChar F (mk (diag a)) = 2 := by
  rw [permChar, fixedPointCount, card_fixedBy_diag ha]
  simp

omit [DecidableEq F] in
theorem permChar_nonsplit {ν : F} (hν : ¬ IsSquare ν) {C : SL(2, F)} (hC : C ∈ nonsplitSL ν)
    (hy : (C : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : permChar F (mk C) = 0 := by
  rw [permChar, fixedPointCount, card_fixedBy_nonsplit hν hC hy]
  simp

omit [DecidableEq F] in
theorem permChar_of_mem_unipotent (h2 : (2 : F) ≠ 0) {x : PSL(2, F)} (hx : x ∈ unipotent F)
    (hx1 : x ≠ 1) : permChar F x = 1 := by
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
  exact permChar_unip (fun h => hx1 ((mk_unip_eq_one_iff h2 t).mpr h))

omit [DecidableEq F] in
theorem permChar_of_mem_splitTorus {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) :
    permChar F x = 2 := by
  obtain ⟨a, rfl⟩ := (mem_splitTorus_iff_exists x).mp hx
  exact permChar_diag (fun h => hx1 ((mk_diag_eq_one_iff a).mpr h))

omit [DecidableEq F] in
theorem permChar_of_mem_nonsplitTorus {ν : F} (hν : ¬ IsSquare ν) {x : PSL(2, F)}
    (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) : permChar F x = 0 := by
  obtain ⟨C, hC, hy, rfl⟩ := exists_of_mem_nonsplitTorus hx hx1
  exact permChar_nonsplit hν hC hy

omit [DecidableEq F] in
theorem permChar_of_mem_conjSet {H : Subgroup PSL(2, F)} {c : ℂ}
    (hH : ∀ x ∈ H, x ≠ 1 → permChar F x = c) {y : PSL(2, F)} (hy : y ∈ conjSet H) :
    permChar F y = c := by
  obtain ⟨hy1, g, hg⟩ := hy
  have hne : g * y * g⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  rw [← permChar_conj g y]
  exact hH _ hg hne

section Split

theorem indSplit_apply_of_mem {α : splitTorus F →* ℂˣ} {x : PSL(2, F)}
    (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) :
    indSplit α x = (α ⟨x, hx⟩ : ℂ) + (α ⟨x, hx⟩⁻¹ : ℂ) := by
  rw [indSplit, inducedFunction_apply_TI (fun _ ha _ hb => splitTorus_mul_comm ha hb)
    (fun _ h => splitWeyl_conj h) splitWeyl_not_mem hx (splitTorus_conj_mem_iff hx hx1)]
  congr 2

variable (hF : ringChar F ≠ 2)
include hF

theorem indSplit_one (α : splitTorus F →* ℂˣ) :
    indSplit α 1 = Fintype.card F * (Fintype.card F + 1) := by
  have h2 := Ring.two_ne_zero hF
  rw [indSplit, inducedFunction_apply_one]
  have hG := card_PSL h2 (F := F)
  have hT := card_splitTorus h2 (F := F)
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hT0 : (Nat.card (splitTorus F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hG' : (Nat.card PSL(2, F) : ℂ) * 2 =
      Fintype.card F * ((Fintype.card F : ℂ) ^ 2 - 1) := by
    have := congrArg (Nat.cast (R := ℂ)) hG
    push_cast [Nat.cast_sub (by nlinarith : 1 ≤ Fintype.card F ^ 2)] at this
    exact this
  have hT' : (Nat.card (splitTorus F) : ℂ) * 2 = (Fintype.card F : ℂ) - 1 := by
    have := congrArg (Nat.cast (R := ℂ)) hT
    push_cast [Nat.cast_sub hq1] at this
    exact this
  rw [map_one, Units.val_one, mul_one, div_eq_iff hT0]
  linear_combination hG' / 2 - (Fintype.card F : ℂ) * (Fintype.card F + 1) * hT' / 2

theorem indSplit_of_mem_conjSet_unipotent (α : splitTorus F →* ℂˣ) {y : PSL(2, F)}
    (hy : y ∈ conjSet (unipotent F)) : indSplit α y = 0 :=
  inducedFunction_apply_eq_zero _
    (not_conj_mem_of_mem_conjSet (coprime_card_unipotent_splitTorus hF) hy)

theorem indSplit_of_mem_conjSet_nonsplit (α : splitTorus F →* ℂˣ) {ν : F}
    (hν : ¬ IsSquare ν) {y : PSL(2, F)} (hy : y ∈ conjSet (nonsplitTorus ν)) :
    indSplit α y = 0 :=
  inducedFunction_apply_eq_zero _ (not_conj_mem_of_mem_conjSet
    (Nat.Coprime.symm (coprime_card_splitTorus_nonsplitTorus hF hν)) hy)

end Split

section Nonsplit

variable (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν)
include hF hν

theorem indNonsplit_apply_of_mem {β : nonsplitTorus ν →* ℂˣ} {x : PSL(2, F)}
    (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) :
    indNonsplit β x = (β ⟨x, hx⟩ : ℂ) + (β ⟨x, hx⟩⁻¹ : ℂ) := by
  obtain ⟨w, hw, -, hinv, hTI⟩ := exists_nonsplitWeyl hF hν
  rw [indNonsplit, inducedFunction_apply_TI (fun _ ha _ hb => nonsplitTorus_mul_comm ha hb)
    hinv hw hx (hTI x hx hx1)]
  congr 2

theorem indNonsplit_one (β : nonsplitTorus ν →* ℂˣ) :
    indNonsplit β 1 = Fintype.card F * (Fintype.card F - 1) := by
  have h2 := Ring.two_ne_zero hF
  rw [indNonsplit, inducedFunction_apply_one]
  have hG := card_PSL h2 (F := F)
  have hS := card_nonsplitTorus hF hν
  have hS0 : (Nat.card (nonsplitTorus ν) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hG' : (Nat.card PSL(2, F) : ℂ) * 2 =
      Fintype.card F * ((Fintype.card F : ℂ) ^ 2 - 1) := by
    have := congrArg (Nat.cast (R := ℂ)) hG
    push_cast [Nat.cast_sub (by nlinarith [Fintype.card_pos (α := F)] :
      1 ≤ Fintype.card F ^ 2)] at this
    exact this
  have hS' : (Nat.card (nonsplitTorus ν) : ℂ) * 2 = (Fintype.card F : ℂ) + 1 := by
    exact_mod_cast hS
  rw [map_one, Units.val_one, mul_one, div_eq_iff hS0]
  linear_combination hG' / 2 - (Fintype.card F : ℂ) * (Fintype.card F - 1) * hS' / 2

theorem indNonsplit_of_mem_conjSet_unipotent (β : nonsplitTorus ν →* ℂˣ) {y : PSL(2, F)}
    (hy : y ∈ conjSet (unipotent F)) : indNonsplit β y = 0 :=
  inducedFunction_apply_eq_zero _
    (not_conj_mem_of_mem_conjSet (coprime_card_unipotent_nonsplitTorus hF hν) hy)

theorem indNonsplit_of_mem_conjSet_split (β : nonsplitTorus ν →* ℂˣ) {y : PSL(2, F)}
    (hy : y ∈ conjSet (splitTorus F)) : indNonsplit β y = 0 :=
  inducedFunction_apply_eq_zero _
    (not_conj_mem_of_mem_conjSet (coprime_card_splitTorus_nonsplitTorus hF hν) hy)

end Nonsplit

end CFSG.PSL2Table
