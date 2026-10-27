module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.G2Data
public import CFSG.HardMathSupport.Timmesfeld.LieRank.TripleLift
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound
import all CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3

set_option maxRecDepth 100000 in
theorem LA_comm : ∀ i j, LA i * LA j = LA j * LA i := by decide +kernel

set_option maxRecDepth 100000 in
theorem LA_pow : ∀ i, LA i ^ 3 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem LA_indep : ∀ i j k l : Fin 3,
    (LA 0 ^ i.val * LA 1 ^ j.val) * (LA 2 ^ k.val * LA 3 ^ l.val) = 1 →
      i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 := by decide +kernel

@[expose] noncomputable def specA : ModuleSpec RG 3 where
  n := 4
  m := 0
  a := aX
  g := Fin.elim0
  M := Fin.elim0
  comm i j := valHom_injective (by
    rw [map_mul, map_mul, valHom_aX, valHom_aX]
    exact LA_comm i j)
  pow i := valHom_injective (by
    rw [map_pow, valHom_aX, map_one]
    exact LA_pow i)
  indep c h := by
    have h1 := congrArg valHom h
    rw [map_list_prod, List.map_map, map_one] at h1
    have h2 : (List.finRange 4).map (valHom ∘ fun k => aX k ^ (c k).val) =
        [LA 0 ^ (c 0).val, LA 1 ^ (c 1).val, LA 2 ^ (c 2).val, LA 3 ^ (c 3).val] := by
      simp [List.finRange_succ, Function.comp_def, map_pow, valHom_aX]
    rw [h2] at h1
    simp only [List.prod_cons, List.prod_nil, mul_one, ← mul_assoc] at h1
    have h3 : (LA 0 ^ (c 0).val * LA 1 ^ (c 1).val) * (LA 2 ^ (c 2).val * LA 3 ^ (c 3).val) =
        1 := by
      rw [← mul_assoc]
      exact h1
    obtain ⟨e0, e1, e2, e3⟩ := LA_indep (c 0) (c 1) (c 2) (c 3) h3
    funext k
    fin_cases k
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  act j := Fin.elim0 j

@[expose] def eltM (c : Fin 4 → ZMod 3) : M14 :=
  ((List.finRange 4).map fun k => LA k ^ (c k).val).prod

theorem valHom_elt (c : Fin 4 → ZMod 3) : valHom (specA.elt c) = eltM c := by
  show valHom (((List.finRange 4).map fun k => aX k ^ (c k).val).prod) = _
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun k _ => by simp [map_pow, valHom_aX])

@[expose] def Ma : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def Mb : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, 1]

set_option maxRecDepth 100000 in
theorem acts_a : ∀ i : Fin 4, Lxa * LA i = eltM (fun k => Ma k i) * Lxa := by decide +kernel

set_option maxRecDepth 100000 in
theorem acts_b : ∀ i : Fin 4, Lxb * LA i = eltM (fun k => Mb k i) * Lxb := by decide +kernel

theorem actsBy_gxa : ActsBy specA gxa Ma := by
  intro (i : Fin 4)
  rw [mul_inv_eq_iff_eq_mul]
  apply valHom_injective
  change valHom (gxa * aX i) = valHom (specA.elt (fun k : Fin 4 => Ma k i) * gxa)
  rw [map_mul, map_mul, valHom_elt (fun k : Fin 4 => Ma k i), valHom_aX]
  exact acts_a i

theorem actsBy_gxb : ActsBy specA gxb Mb := by
  intro (i : Fin 4)
  rw [mul_inv_eq_iff_eq_mul]
  apply valHom_injective
  change valHom (gxb * aX i) = valHom (specA.elt (fun k : Fin 4 => Mb k i) * gxb)
  rw [map_mul, map_mul, valHom_elt (fun k : Fin 4 => Mb k i), valHom_aX]
  exact acts_b i

set_option maxRecDepth 100000 in
theorem Lxa_pow : Lxa ^ 3 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem Lxb_pow : Lxb ^ 3 = 1 := by decide +kernel

theorem gxa_pow : gxa ^ 3 = 1 := valHom_injective (by rw [map_pow, map_one]; exact Lxa_pow)

theorem gxb_pow : gxb ^ 3 = 1 := valHom_injective (by rw [map_pow, map_one]; exact Lxb_pow)

@[expose] def cvec1 : Fin 4 → ZMod 3 := ![1, 1, 2, 2]

@[expose] def cvec2 : Fin 4 → ZMod 3 := ![2, 1, 1, 1]

set_option maxRecDepth 100000 in
theorem comm_matrix_1 : Lxb * Lxa ^ 1 = Lxa ^ 1 * Lxb * eltM cvec1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem comm_matrix_2 : Lxb * Lxa ^ 2 = Lxa ^ 2 * Lxb * eltM cvec2 := by decide +kernel

theorem comm_xb_xa : ∀ i : Fin 3,
    ∃ c ∈ specA.span, gxb * gxa ^ i.val = gxa ^ i.val * gxb * c := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨1, one_mem _, by simp⟩
  | ⟨1, _⟩ =>
    refine ⟨specA.elt cvec1, specA.elt_mem _, valHom_injective ?_⟩
    change valHom (gxb * gxa ^ 1) = valHom (gxa ^ 1 * gxb * specA.elt cvec1)
    rw [map_mul, map_mul, map_pow, map_mul, valHom_elt, valHom_gxa, valHom_gxb]
    exact comm_matrix_1
  | ⟨2, _⟩ =>
    refine ⟨specA.elt cvec2, specA.elt_mem _, valHom_injective ?_⟩
    change valHom (gxb * gxa ^ 2) = valHom (gxa ^ 2 * gxb * specA.elt cvec2)
    rw [map_mul, map_mul, map_pow, map_mul, valHom_elt, valHom_gxa, valHom_gxb]
    exact comm_matrix_2

set_option maxRecDepth 100000 in
theorem distinct_nine : ∀ a b : Fin 9, a ≠ b →
    Ma ^ (a.val / 3) * Mb ^ (a.val % 3) ≠ Ma ^ (b.val / 3) * Mb ^ (b.val % 3) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem card_fixed :
    Nat.card {c : Fin 4 → ZMod 3 // Ma.mulVec c = c ∧ Mb.mulVec c = c} ≤ 3 ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
theorem torus_facts : (Lta * LA 0 = LA 0 ^ 2 * Lta ∧ Lta * LA 1 = LA 1 ^ 2 * Lta ∧
    Lta * LA 3 = LA 3 * Lta) ∧ (Ltb * LA 0 = LA 0 ^ 2 * Ltb ∧ Ltb * LA 1 = LA 1 * Ltb ∧
    Ltb * LA 3 = LA 3 ^ 2 * Ltb) := by
  decide +kernel

theorem elt_four (c : Fin 4 → ZMod 3) : specA.elt c =
    aX 0 ^ (c 0).val * aX 1 ^ (c 1).val * aX 2 ^ (c 2).val * aX 3 ^ (c 3).val := by
  apply valHom_injective
  rw [valHom_elt]
  simp [eltM, List.finRange_succ, map_pow, valHom_aX, mul_assoc]

theorem card_closure_three :
    27 ≤ Nat.card (Subgroup.closure {aX 0, aX 1, aX 3}) := by
  have hmem : ∀ c : Fin 4 → ZMod 3, c 2 = 0 →
      specA.elt c ∈ Subgroup.closure {aX 0, aX 1, aX 3} := by
    intro c hc
    rw [elt_four, hc]
    simp only [ZMod.val_zero, pow_zero, mul_one]
    refine mul_mem (mul_mem (pow_mem (Subgroup.subset_closure ?_) _)
      (pow_mem (Subgroup.subset_closure ?_) _)) (pow_mem (Subgroup.subset_closure ?_) _) <;> simp
  have hinj : Function.Injective (fun c : {c : Fin 4 → ZMod 3 // c 2 = 0} =>
      (⟨specA.elt c.1, hmem c.1 c.2⟩ : Subgroup.closure {aX 0, aX 1, aX 3})) := by
    intro c d h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (specA.elt_injective h')
  have h27 : Nat.card {c : Fin 4 → ZMod 3 // c 2 = 0} = 27 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [← h27]
  exact Nat.card_le_card_of_injective _ hinj

theorem four_le_pRank_of_cover_RG {L : Type} [Group L] [Finite L] (φ : L →* RG)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center L) {z : L} (hz : z ∈ φ.ker)
    (hzo : orderOf z = 3) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨⟨ta0, ta1, ta3⟩, ⟨tb0, tb1, tb3⟩⟩ := torus_facts
  have p0 : aX 0 ^ 3 = 1 := specA.pow (0 : Fin 4)
  have p1 : aX 1 ^ 3 = 1 := specA.pow (1 : Fin 4)
  have p3 : aX 3 ^ 3 = 1 := specA.pow (3 : Fin 4)
  have c01 : aX 0 * aX 1 = aX 1 * aX 0 := specA.comm (0 : Fin 4) (1 : Fin 4)
  have c03 : aX 0 * aX 3 = aX 3 * aX 0 := specA.comm (0 : Fin 4) (3 : Fin 4)
  have c13 : aX 1 * aX 3 = aX 3 * aX 1 := specA.comm (1 : Fin 4) (3 : Fin 4)
  refine four_le_pRank_of_cover φ hφ hker hz hzo (u₀ := aX 0) (u₁ := aX 1) (u₂ := aX 3)
    (t := tA) (s := tB) p0 p1 p3 c01 c03 c13 ?_ ?_ ?_ ?_ ?_ ?_ card_closure_three
  · apply valHom_injective
    rw [map_mul, map_mul, map_pow, valHom_aX, valHom_tA]
    exact ta0
  · apply valHom_injective
    rw [map_mul, map_mul, map_pow, valHom_aX, valHom_tA]
    exact ta1
  · apply valHom_injective
    rw [map_mul, map_mul, valHom_aX, valHom_tA]
    exact ta3
  · apply valHom_injective
    rw [map_mul, map_mul, map_pow, valHom_aX, valHom_tB]
    exact tb0
  · apply valHom_injective
    rw [map_mul, map_mul, valHom_aX, valHom_tB]
    exact tb1
  · apply valHom_injective
    rw [map_mul, map_mul, map_pow, valHom_aX, valHom_tB]
    exact tb3

end CFSG.HardMathSupport.Timmesfeld.LieRank
