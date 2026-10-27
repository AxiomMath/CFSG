module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16SL
public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Basic

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Matrix MatrixGroups

variable {F : Type*} [Field F]

section Involution

variable [CharP F 2]

theorem involution_entries (x : SL(2, F)) (hx : x * x = 1) : x 1 1 = x 0 0 ∧
    x 0 0 * x 0 0 + x 0 1 * x 1 0 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hd := det_entries x
  have h00 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) hx
  have h01 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hx
  have h10 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 1 0) hx
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  have hsum : x 0 0 + x 1 1 = 0 := by
    by_contra hne
    have hb : x 0 1 = 0 := by
      have : x 0 1 * (x 0 0 + x 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.1 this).resolve_right hne
    have hc : x 1 0 = 0 := by
      have : x 1 0 * (x 0 0 + x 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.1 this).resolve_right hne
    rw [hb, hc] at h00 hd
    have ha : x 0 0 ≠ 0 := by
      intro h
      rw [h] at h00
      simp at h00
    have had : x 0 0 = x 1 1 := by
      have : x 0 0 * (x 0 0 - x 1 1) = 0 := by linear_combination h00 - hd
      have := (mul_eq_zero.1 this).resolve_left ha
      linear_combination this
    apply hne
    rw [← had]
    linear_combination (x 0 0) * h2
  refine ⟨?_, h00⟩
  linear_combination hsum - (x 0 0) * h2

theorem exists_conj_uE_of_involution (x : SL(2, F)) (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ (g : SL(2, F)) (c : F), c ≠ 0 ∧ x = g * uE c * g⁻¹ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨hd, hdet⟩ := involution_entries x hx2
  by_cases hc : x 1 0 = 0
  · rw [hc, mul_zero, add_zero] at hdet
    have ha : x 0 0 = 1 := by
      have : (x 0 0 + 1) ^ 2 = 0 := by linear_combination hdet + (x 0 0) * h2 + h2
      have h3 := pow_eq_zero_iff (two_ne_zero) |>.1 this
      linear_combination h3 - h2
    have hb : x 0 1 ≠ 0 := by
      intro hb
      apply hx1
      apply sl_eq
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, ha, hd]
    refine ⟨1, x 0 1, hb, ?_⟩
    rw [one_mul, inv_one, mul_one]
    apply sl_eq
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uE, hc, ha, hd]
  · let P : SL(2, F) := ⟨!![x 0 0 + 1, (x 1 0)⁻¹; x 1 0, 0], by
      rw [Matrix.det_fin_two]
      simp [hc]
      linear_combination (-1 : F) * h2⟩
    refine ⟨P, (x 1 0)⁻¹, inv_ne_zero hc, ?_⟩
    have hxP : x * P = P * uE (x 1 0)⁻¹ := by
      apply sl_eq
      rw [sl_coe_mul, sl_coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [P, uE, Matrix.mul_apply, hd]
      · linear_combination hdet
      · linear_combination (-(x 1 0)⁻¹) * h2
      · linear_combination (x 0 0 * x 1 0) * h2
    exact (mul_inv_cancel_right x P).symm.trans (by rw [hxP])

theorem card_centralizer_conj {G : Type*} [Group G] (g u : G) :
    Nat.card (Subgroup.centralizer ({g * u * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({u} : Set G)) := by
  refine Nat.card_congr
    ⟨fun h => ⟨g⁻¹ * h.1 * g, ?_⟩, fun h => ⟨g * h.1 * g⁻¹, ?_⟩, fun h => ?_, fun h => ?_⟩
  · have := h.2
    rw [Subgroup.mem_centralizer_iff] at this ⊢
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    have h1 := this (g * u * g⁻¹) rfl
    calc u * (g⁻¹ * h.1 * g) = g⁻¹ * ((g * u * g⁻¹) * h.1) * g := by group
      _ = g⁻¹ * (h.1 * (g * u * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * h.1 * g * u := by group
  · have := h.2
    rw [Subgroup.mem_centralizer_iff] at this ⊢
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    have h1 := this u rfl
    calc g * u * g⁻¹ * (g * h.1 * g⁻¹) = g * (u * h.1) * g⁻¹ := by group
      _ = g * (h.1 * u) * g⁻¹ := by rw [h1]
      _ = g * h.1 * g⁻¹ * (g * u * g⁻¹) := by group
  · apply Subtype.ext
    show g * (g⁻¹ * h.1 * g) * g⁻¹ = h.1
    group
  · apply Subtype.ext
    show g⁻¹ * (g * h.1 * g⁻¹) * g = h.1
    group

section Centralizer

theorem centralizer_uE (c : F) (hc : c ≠ 0) :
    (Subgroup.centralizer ({uE c} : Set SL(2, F)) : Set SL(2, F)) = Set.range uE := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext g
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    Set.mem_range]
  constructor
  · intro h
    have hdet := det_entries g
    have hm : (uE c : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
        (g : Matrix (Fin 2) (Fin 2) F) * (uE c : Matrix (Fin 2) (Fin 2) F) := congrArg Subtype.val h
    have e00 := congrFun (congrFun hm 0) 0
    have e01 := congrFun (congrFun hm 0) 1
    have e10 := congrFun (congrFun hm 1) 0
    have e11 := congrFun (congrFun hm 1) 1
    simp [uE, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    have hg10 : g 1 0 = 0 := e00.resolve_left hc
    have hg11 : g 1 1 = g 0 0 := by
      have h3 : c * (g 1 1 - g 0 0) = 0 := by linear_combination e01
      have h4 := (mul_eq_zero.1 h3).resolve_left hc
      linear_combination h4
    have hg00 : g 0 0 = 1 := by
      rw [hg10, mul_zero, sub_zero, hg11] at hdet
      have h3 : (g 0 0 + 1) ^ 2 = 0 := by linear_combination hdet + (g 0 0) * h2 + h2
      have h4 := (pow_eq_zero_iff two_ne_zero).1 h3
      linear_combination h4 - h2
    refine ⟨g 0 1, ?_⟩
    apply sl_eq
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uE, hg10, hg11, hg00]
  · rintro ⟨b, rfl⟩
    rw [← uE_add, ← uE_add, add_comm]

theorem card_centralizer_involution_of_charP (hF : Nat.card F = 16) (x : SL(2, F)) (hx1 : x ≠ 1)
    (hx2 : x * x = 1) : Nat.card (Subgroup.centralizer ({x} : Set SL(2, F))) = 16 := by
  obtain ⟨g, c, hc, rfl⟩ := exists_conj_uE_of_involution x hx1 hx2
  rw [card_centralizer_conj]
  calc Nat.card (Subgroup.centralizer ({uE c} : Set SL(2, F)))
      = Nat.card (Set.range (uE : F → SL(2, F))) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun y => by
          rw [← SetLike.mem_coe, centralizer_uE c hc])
    _ = Nat.card F := Nat.card_range_of_injective uE_injective
    _ = 16 := hF

end Centralizer

end Involution

theorem card_centralizer_involution (hF : Nat.card F = 16) (x : SL(2, F)) (hx1 : x ≠ 1)
    (hx2 : x * x = 1) : Nat.card (Subgroup.centralizer ({x} : Set SL(2, F))) = 16 := by
  have := charP_two hF
  exact card_centralizer_involution_of_charP hF x hx1 hx2

end Nat16

end CFSG.OddStandard.Seitz77
