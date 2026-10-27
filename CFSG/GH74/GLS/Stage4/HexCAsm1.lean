module

public import CFSG.GH74.GLS.Stage4.HexCoord
public import CFSG.GH74.GLS.Stage4.HexCMu

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {root : ℤ → Subgroup G} {F : Type} [Field F]

theorem inv_eq_of_add {f : F → G} (h : ∀ c d, f (c + d) = f c * f d) (c : F) : (f c)⁻¹ = f (-c) := by
  have h0 : f 0 = 1 := map_zero_of_add' h
  have := h c (-c)
  rw [add_neg_cancel, h0] at this
  exact inv_eq_of_mul_eq_one_right this.symm

@[expose] def g2ψ (D : HexData root F) (e : F) (Λ : F → G) : Fin 6 → F → G
  | 0 => D.p1
  | 1 => fun d => D.p2 (-e * d)
  | 2 => fun v => Λ (-(3 * e) * v)
  | 3 => fun w => D.p4 (-e * w)
  | 4 => D.p5
  | 5 => D.p6

section Asm

variable (hC : Hex6Comm root) (D : HexData root F) {Λ : F → G} (hΛmem : ∀ v, Λ v ∈ root 3)
  (hΛadd : ∀ v w, Λ (v + w) = Λ v * Λ w) (hr5 : ∀ t v, ⁅D.p5 t, Λ v⁆ = D.p4 (t * v))

include hC hΛmem hΛadd hr5 in
theorem inv_reorder (a b c d : F) :
    (D.p2 a * Λ b * D.p4 c * D.p5 d)⁻¹ =
      D.p2 (-a) * Λ (-b) * D.p4 (-c + d * b) * D.p5 (-d) := by
  have i2 := inv_eq_of_add D.p2_add
  have i4 := inv_eq_of_add D.p4_add
  have i5 := inv_eq_of_add D.p5_add
  have iΛ := inv_eq_of_add hΛadd
  have k34 : ∀ x y, D.p4 x * Λ y = Λ y * D.p4 x := fun x y =>
    (hC.c34 _ (hΛmem y) _ (D.p4_mem x)).symm
  have k24 : ∀ x y, D.p4 x * D.p2 y = D.p2 y * D.p4 x := fun x y =>
    (hC.l24 _ (D.p2_mem y) _ (D.p4_mem x)).symm
  have k23 : ∀ x y, Λ x * D.p2 y = D.p2 y * Λ x := fun x y =>
    (hC.c23 _ (D.p2_mem y) _ (hΛmem x)).symm
  have c45 : D.p5 (-d) * D.p4 (-c) = D.p4 (-c) * D.p5 (-d) :=
    (hC.c45 _ (D.p4_mem _) _ (D.p5_mem _)).symm
  have c25 : D.p5 (-d) * D.p2 (-a) = D.p2 (-a) * D.p5 (-d) :=
    (hC.o25 _ (D.p2_mem _) _ (D.p5_mem _)).symm
  have cc : D.p5 (-d) * Λ (-b) = D.p4 (d * b) * Λ (-b) * D.p5 (-d) := by
    have := hr5 (-d) (-b)
    rw [neg_mul_neg] at this
    rw [← this]; simp only [commutatorElement_def]; group
  rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, i2, i4, i5, iΛ]
  calc D.p5 (-d) * (D.p4 (-c) * (Λ (-b) * D.p2 (-a)))
      = (D.p5 (-d) * D.p4 (-c)) * (Λ (-b) * D.p2 (-a)) := by rw [← mul_assoc]
    _ = (D.p4 (-c) * D.p5 (-d)) * (Λ (-b) * D.p2 (-a)) := by rw [c45]
    _ = D.p4 (-c) * ((D.p5 (-d) * Λ (-b)) * D.p2 (-a)) := by simp only [mul_assoc]
    _ = D.p4 (-c) * ((D.p4 (d * b) * Λ (-b) * D.p5 (-d)) * D.p2 (-a)) := by rw [cc]
    _ = D.p4 (-c) * (D.p4 (d * b) * Λ (-b) * (D.p5 (-d) * D.p2 (-a))) := by simp only [mul_assoc]
    _ = D.p4 (-c) * (D.p4 (d * b) * Λ (-b) * (D.p2 (-a) * D.p5 (-d))) := by rw [c25]
    _ = (D.p4 (-c) * D.p4 (d * b)) * Λ (-b) * D.p2 (-a) * D.p5 (-d) := by simp only [mul_assoc]
    _ = D.p4 (-c + d * b) * Λ (-b) * D.p2 (-a) * D.p5 (-d) := by rw [← D.p4_add]
    _ = (Λ (-b) * D.p4 (-c + d * b)) * D.p2 (-a) * D.p5 (-d) := by rw [k34]
    _ = Λ (-b) * (D.p4 (-c + d * b) * D.p2 (-a)) * D.p5 (-d) := by simp only [mul_assoc]
    _ = Λ (-b) * (D.p2 (-a) * D.p4 (-c + d * b)) * D.p5 (-d) := by rw [k24]
    _ = (Λ (-b) * D.p2 (-a)) * D.p4 (-c + d * b) * D.p5 (-d) := by simp only [mul_assoc]
    _ = D.p2 (-a) * Λ (-b) * D.p4 (-c + d * b) * D.p5 (-d) := by rw [k23]

variable (e : F) (hr1 : ∀ s v, ⁅D.p1 s, Λ v⁆ = D.p2 (s * v))
  (hc15 : ∀ s t, ⁅D.p1 s, D.p5 t⁆ =
    D.p2 (3 * e * s ^ 2 * t) * Λ (6 * e * (s * t)) * D.p4 (3 * e * s * t ^ 2))
  (hAct : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = D.p2 (e * c * s ^ 3) * Λ (3 * e * c * s ^ 2) *
    D.p4 (2 * e * c ^ 2 * s ^ 3) * D.p5 (c * s))

include hC hΛmem hΛadd hr5 hr1 hc15 hAct in
theorem g2Rel_of_data : G2Rel (fun g : Σ _ : Fin 6, F => g2ψ D e Λ g.1 g.2) where
  add i c d := by
    fin_cases i
    · exact D.p1_add c d
    · show D.p2 (-e * (c + d)) = D.p2 (-e * c) * D.p2 (-e * d)
      rw [mul_add, D.p2_add]
    · show Λ (-(3 * e) * (c + d)) = Λ (-(3 * e) * c) * Λ (-(3 * e) * d)
      rw [mul_add, hΛadd]
    · show D.p4 (-e * (c + d)) = D.p4 (-e * c) * D.p4 (-e * d)
      rw [mul_add, D.p4_add]
    · exact D.p5_add c d
    · exact D.p6_add c d
  r02 s t := by
    show ⁅D.p1 s, Λ (-(3 * e) * t)⁆ = D.p2 (-e * (3 * (s * t)))
    rw [hr1]; congr 1; ring
  r24 s t := by
    show ⁅Λ (-(3 * e) * s), D.p5 t⁆ = D.p4 (-e * -(3 * (s * t)))
    rw [← commutatorElement_inv, hr5, inv_eq_of_add D.p4_add]; congr 1; ring
  r15 s t := by
    show ⁅D.p2 (-e * s), D.p6 t⁆ = D.p4 (-e * -(s * t))
    rw [← commutatorElement_inv, D.rel_long, inv_eq_of_add D.p4_add]; congr 1; ring
  r04 s t := by
    show ⁅D.p1 s, D.p5 t⁆ = D.p2 (-e * -(3 * (s ^ 2 * t))) * Λ (-(3 * e) * -(2 * (s * t))) *
      D.p4 (-e * -(3 * (s * t ^ 2)))
    rw [hc15, show 3 * e * s ^ 2 * t = -e * -(3 * (s ^ 2 * t)) by ring,
      show 6 * e * (s * t) = -(3 * e) * -(2 * (s * t)) by ring,
      show 3 * e * s * t ^ 2 = -e * -(3 * (s * t ^ 2)) by ring]
  r05 s t := by
    show ⁅D.p1 s, D.p6 t⁆ = D.p2 (-e * (t * s ^ 3)) * Λ (-(3 * e) * (t * s ^ 2)) *
      D.p4 (-e * -(t ^ 2 * s ^ 3)) * D.p5 (-(t * s))
    rw [← commutatorElement_inv, hAct, inv_reorder hC D hΛmem hΛadd hr5,
      show -(e * t * s ^ 3) = -e * (t * s ^ 3) by ring,
      show -(3 * e * t * s ^ 2) = -(3 * e) * (t * s ^ 2) by ring,
      show -(2 * e * t ^ 2 * s ^ 3) + t * s * (3 * e * t * s ^ 2) = -e * -(t ^ 2 * s ^ 3) by ring]
  c01 s t := hC.c12 _ (D.p1_mem _) _ (D.p2_mem _)
  c03 s t := hC.o14 _ (D.p1_mem _) _ (D.p4_mem _)
  c12 s t := hC.c23 _ (D.p2_mem _) _ (hΛmem _)
  c13 s t := hC.l24 _ (D.p2_mem _) _ (D.p4_mem _)
  c14 s t := hC.o25 _ (D.p2_mem _) _ (D.p5_mem _)
  c23 s t := hC.c34 _ (hΛmem _) _ (D.p4_mem _)
  c25 s t := hC.o36 _ (hΛmem _) _ (D.p6_mem _)
  c34 s t := hC.c45 _ (D.p4_mem _) _ (D.p5_mem _)
  c35 s t := hC.l46 _ (D.p4_mem _) _ (D.p6_mem _)
  c45 s t := hC.c56 _ (D.p5_mem _) _ (D.p6_mem _)

end Asm

end CFSG.GH74.GLS.Stage4.Hex
