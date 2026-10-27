module

public import CFSG.GH74.GLS.Stage4.HexCAsm1

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

@[expose] def g2ψ3 (D : HexData root F) (e : F) (Λ : F → G) : Fin 6 → F → G
  | 0 => D.p1
  | 1 => fun d => D.p2 (-e * d)
  | 2 => Λ
  | 3 => fun w => D.p4 (-e * w)
  | 4 => D.p5
  | 5 => D.p6

section Asm3

variable (hC : Hex6Comm root) (D : HexData root F) {Λ : F → G} (hΛmem : ∀ v, Λ v ∈ root 3)
  (hΛadd : ∀ v w, Λ (v + w) = Λ v * Λ w) (hr5 : ∀ t v, ⁅D.p5 t, Λ v⁆ = 1)

include hC hΛmem hΛadd hr5 in
theorem inv_reorder3 (a b c d : F) :
    (D.p2 a * Λ b * D.p4 c * D.p5 d)⁻¹ = D.p2 (-a) * Λ (-b) * D.p4 (-c) * D.p5 (-d) := by
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
  have cc : D.p5 (-d) * Λ (-b) = Λ (-b) * D.p5 (-d) := by
    have := hr5 (-d) (-b)
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, i2, i4, i5, iΛ]
  calc D.p5 (-d) * (D.p4 (-c) * (Λ (-b) * D.p2 (-a)))
      = (D.p5 (-d) * D.p4 (-c)) * (Λ (-b) * D.p2 (-a)) := by rw [← mul_assoc]
    _ = (D.p4 (-c) * D.p5 (-d)) * (Λ (-b) * D.p2 (-a)) := by rw [c45]
    _ = D.p4 (-c) * ((D.p5 (-d) * Λ (-b)) * D.p2 (-a)) := by simp only [mul_assoc]
    _ = D.p4 (-c) * ((Λ (-b) * D.p5 (-d)) * D.p2 (-a)) := by rw [cc]
    _ = D.p4 (-c) * (Λ (-b) * (D.p5 (-d) * D.p2 (-a))) := by simp only [mul_assoc]
    _ = D.p4 (-c) * (Λ (-b) * (D.p2 (-a) * D.p5 (-d))) := by rw [c25]
    _ = (D.p4 (-c) * Λ (-b)) * D.p2 (-a) * D.p5 (-d) := by simp only [mul_assoc]
    _ = (Λ (-b) * D.p4 (-c)) * D.p2 (-a) * D.p5 (-d) := by rw [k34]
    _ = Λ (-b) * (D.p4 (-c) * D.p2 (-a)) * D.p5 (-d) := by simp only [mul_assoc]
    _ = Λ (-b) * (D.p2 (-a) * D.p4 (-c)) * D.p5 (-d) := by rw [k24]
    _ = (Λ (-b) * D.p2 (-a)) * D.p4 (-c) * D.p5 (-d) := by simp only [mul_assoc]
    _ = D.p2 (-a) * Λ (-b) * D.p4 (-c) * D.p5 (-d) := by rw [k23]

variable {e : F} (h3z : (3 : F) = 0) (hr1 : ∀ s v, ⁅D.p1 s, Λ v⁆ = 1)
  (hc15 : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Λ (s * t))
  (hAct : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = D.p2 (e * c * s ^ 3) * Λ (-(c * s ^ 2)) *
    D.p4 (2 * e * c ^ 2 * s ^ 3) * D.p5 (c * s))

include hC hΛmem hΛadd hr5 h3z hr1 hc15 hAct in
theorem g2Rel_of_data3 : G2Rel (fun g : Σ _ : Fin 6, F => g2ψ3 D e Λ g.1 g.2) where
  add i c d := by
    fin_cases i
    · exact D.p1_add c d
    · show D.p2 (-e * (c + d)) = D.p2 (-e * c) * D.p2 (-e * d)
      rw [mul_add, D.p2_add]
    · exact hΛadd c d
    · show D.p4 (-e * (c + d)) = D.p4 (-e * c) * D.p4 (-e * d)
      rw [mul_add, D.p4_add]
    · exact D.p5_add c d
    · exact D.p6_add c d
  r02 s t := by
    show ⁅D.p1 s, Λ t⁆ = D.p2 (-e * (3 * (s * t)))
    have z : -e * (3 * (s * t)) = 0 := by rw [h3z]; ring
    rw [hr1, z, map_zero_of_add' D.p2_add]
  r24 s t := by
    show ⁅Λ s, D.p5 t⁆ = D.p4 (-e * -(3 * (s * t)))
    have z : -e * -(3 * (s * t)) = 0 := by rw [h3z]; ring
    rw [← commutatorElement_inv, hr5, inv_one, z, map_zero_of_add' D.p4_add]
  r15 s t := by
    show ⁅D.p2 (-e * s), D.p6 t⁆ = D.p4 (-e * -(s * t))
    rw [← commutatorElement_inv, D.rel_long, inv_eq_of_add D.p4_add]; congr 1; ring
  r04 s t := by
    show ⁅D.p1 s, D.p5 t⁆ = D.p2 (-e * -(3 * (s ^ 2 * t))) * Λ (-(2 * (s * t))) *
      D.p4 (-e * -(3 * (s * t ^ 2)))
    have z1 : -e * -(3 * (s ^ 2 * t)) = 0 := by rw [h3z]; ring
    have z3 : -e * -(3 * (s * t ^ 2)) = 0 := by rw [h3z]; ring
    have z2 : -(2 * (s * t)) = s * t := by linear_combination (-(s * t)) * h3z
    rw [hc15, z1, z3, z2, map_zero_of_add' D.p2_add, map_zero_of_add' D.p4_add, one_mul, mul_one]
  r05 s t := by
    show ⁅D.p1 s, D.p6 t⁆ = D.p2 (-e * (t * s ^ 3)) * Λ (t * s ^ 2) *
      D.p4 (-e * -(t ^ 2 * s ^ 3)) * D.p5 (-(t * s))
    rw [← commutatorElement_inv, hAct, inv_reorder3 hC D hΛmem hΛadd hr5,
      show -(e * t * s ^ 3) = -e * (t * s ^ 3) by ring, neg_neg,
      show -(2 * e * t ^ 2 * s ^ 3) = -e * -(t ^ 2 * s ^ 3) by
        linear_combination (-(e * t ^ 2 * s ^ 3)) * h3z]
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

end Asm3

theorem g2Coords_of_data3 [IsSimpleGroup G] (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) (D : HexData root F) {e : F} (he : e ≠ 0)
    {Λ : F → G} (hΛmem : ∀ v, Λ v ∈ root 3) (hΛinj : Function.Injective Λ)
    (hΛsurj : ∀ u ∈ root 3, ∃ v, Λ v = u)
    (hrel : G2Rel (fun g : Σ _ : Fin 6, F => g2ψ3 D e Λ g.1 g.2)) :
    G2Coords (R.toPre hgen).toSystemOfSimple (g2ψ3 D e Λ) where
  rel := hrel
  mem i c := by
    fin_cases i
    · exact D.p1_mem c
    · exact D.p2_mem _
    · exact hΛmem _
    · exact D.p4_mem _
    · exact D.p5_mem c
    · exact D.p6_mem c
  inj i := by
    have hn : -e ≠ 0 := neg_ne_zero.2 he
    fin_cases i
    · exact D.p1_inj
    · intro a b hab
      exact mul_left_cancel₀ hn (D.p2_inj hab)
    · exact hΛinj
    · intro a b hab
      exact mul_left_cancel₀ hn (D.p4_inj hab)
    · exact D.p5_inj
    · exact D.p6_inj
  surj i y hy := by
    have hn : -e ≠ 0 := neg_ne_zero.2 he
    fin_cases i
    · exact D.p1_surj y hy
    · obtain ⟨d, hd⟩ := D.p2_surj y hy
      refine ⟨d / -e, ?_⟩
      show D.p2 (-e * (d / -e)) = y
      rw [show -e * (d / -e) = d by field_simp]; exact hd
    · exact hΛsurj y hy
    · obtain ⟨d, hd⟩ := D.p4_surj y hy
      refine ⟨d / -e, ?_⟩
      show D.p4 (-e * (d / -e)) = y
      rw [show -e * (d / -e) = d by field_simp]; exact hd
    · exact D.p5_surj y hy
    · exact D.p6_surj y hy

end CFSG.GH74.GLS.Stage4.Hex
