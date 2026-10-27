module

public import CFSG.GH74.GLS.Stage4.HexCMu

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

@[expose] def Nel (D : HexData root F) (e : F) (u : G) (f : F) : G := D.p2 e * u * D.p4 f

section Ncalc

variable (hC : Hex6Comm root) (D : HexData root F)

theorem Nel_mem {e : F} {u : G} {f : F} (hu : u ∈ root 3) : Nel D e u f ∈ Vsub root 2 4 :=
  mem_V24_of (D.p2_mem e) hu (D.p4_mem f)

include hC in
theorem Nel_mul {e e' f f' : F} {u u' : G} (hu : u ∈ root 3) (hu' : u' ∈ root 3) :
    Nel D e u f * Nel D e' u' f' = Nel D (e + e') (u * u') (f + f') := by
  have hCA : Commute (D.p4 f) (D.p2 e') := (hC.l24 _ (D.p2_mem e') _ (D.p4_mem f)).symm
  have hCB : Commute (D.p4 f) u' := (hC.c34 u' hu' _ (D.p4_mem f)).symm
  have hBA : Commute u (D.p2 e') := (hC.c23 _ (D.p2_mem e') u hu).symm
  unfold Nel
  rw [(Commute.mul_right hCA hCB).mul_mul_mul_comm (D.p2 e * u) (D.p4 f'),
    hBA.mul_mul_mul_comm (D.p2 e) u', D.p2_add, D.p4_add]

include hC in
theorem conj_p1_Nel {μ : G → F} (hμ : MuData D μ) (s e f : F) {u : G} (hu : u ∈ root 3) :
    D.p1 s * Nel D e u f * (D.p1 s)⁻¹ = Nel D (e + s * μ u) u f := by
  have h1 : D.p1 s * D.p2 e * (D.p1 s)⁻¹ = D.p2 e := by
    rw [mul_inv_eq_iff_eq_mul]; exact hC.c12 _ (D.p1_mem s) _ (D.p2_mem e)
  have h3 : D.p1 s * D.p4 f * (D.p1 s)⁻¹ = D.p4 f := by
    rw [mul_inv_eq_iff_eq_mul]; exact hC.o14 _ (D.p1_mem s) _ (D.p4_mem f)
  have h2 : D.p1 s * u * (D.p1 s)⁻¹ = D.p2 (s * μ u) * u := by
    rw [← hμ.r1 s u hu]; simp only [commutatorElement_def]; group
  unfold Nel
  calc D.p1 s * (D.p2 e * u * D.p4 f) * (D.p1 s)⁻¹
      = (D.p1 s * D.p2 e * (D.p1 s)⁻¹) * (D.p1 s * u * (D.p1 s)⁻¹) *
        (D.p1 s * D.p4 f * (D.p1 s)⁻¹) := by group
    _ = D.p2 e * (D.p2 (s * μ u) * u) * D.p4 f := by rw [h1, h2, h3]
    _ = D.p2 (e + s * μ u) * u * D.p4 f := by rw [D.p2_add]; group

include hC in
theorem conj_p5_Nel {μ : G → F} (hμ : MuData D μ) (t e f : F) {u : G} (hu : u ∈ root 3) :
    D.p5 t * Nel D e u f * (D.p5 t)⁻¹ = Nel D e u (f + t * μ u) := by
  have h1 : D.p5 t * D.p2 e * (D.p5 t)⁻¹ = D.p2 e := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.o25 _ (D.p2_mem e) _ (D.p5_mem t)).symm
  have h3 : D.p5 t * D.p4 f * (D.p5 t)⁻¹ = D.p4 f := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.c45 _ (D.p4_mem f) _ (D.p5_mem t)).symm
  have h2 : D.p5 t * u * (D.p5 t)⁻¹ = D.p4 (t * μ u) * u := by
    rw [← hμ.r5 t u hu]; simp only [commutatorElement_def]; group
  have hc : D.p4 (t * μ u) * u = u * D.p4 (t * μ u) := (hC.c34 u hu _ (D.p4_mem _)).symm
  unfold Nel
  calc D.p5 t * (D.p2 e * u * D.p4 f) * (D.p5 t)⁻¹
      = (D.p5 t * D.p2 e * (D.p5 t)⁻¹) * (D.p5 t * u * (D.p5 t)⁻¹) *
        (D.p5 t * D.p4 f * (D.p5 t)⁻¹) := by group
    _ = D.p2 e * (D.p4 (t * μ u) * u) * D.p4 f := by rw [h1, h2, h3]
    _ = D.p2 e * u * (D.p4 (t * μ u) * D.p4 f) := by rw [hc]; group
    _ = D.p2 e * u * D.p4 (f + t * μ u) := by rw [← D.p4_add, add_comm]

include hC in
theorem conj_p6_Nel (c e f : F) {u : G} (hu : u ∈ root 3) :
    D.p6 c * Nel D e u f * (D.p6 c)⁻¹ = Nel D e u (f + c * e) := by
  have h1 : D.p6 c * D.p2 e * (D.p6 c)⁻¹ = D.p4 (c * e) * D.p2 e := by
    rw [← D.rel_long c e]; simp only [commutatorElement_def]; group
  have h2 : D.p6 c * u * (D.p6 c)⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.o36 u hu _ (D.p6_mem c)).symm
  have h3 : D.p6 c * D.p4 f * (D.p6 c)⁻¹ = D.p4 f := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.l46 _ (D.p4_mem f) _ (D.p6_mem c)).symm
  have hc1 : D.p4 (c * e) * D.p2 e = D.p2 e * D.p4 (c * e) :=
    (hC.l24 _ (D.p2_mem e) _ (D.p4_mem _)).symm
  have hc2 : D.p4 (c * e) * u = u * D.p4 (c * e) := (hC.c34 u hu _ (D.p4_mem _)).symm
  unfold Nel
  calc D.p6 c * (D.p2 e * u * D.p4 f) * (D.p6 c)⁻¹
      = (D.p6 c * D.p2 e * (D.p6 c)⁻¹) * (D.p6 c * u * (D.p6 c)⁻¹) *
        (D.p6 c * D.p4 f * (D.p6 c)⁻¹) := by group
    _ = D.p4 (c * e) * D.p2 e * u * D.p4 f := by rw [h1, h2, h3]
    _ = (D.p2 e * D.p4 (c * e)) * u * D.p4 f := by rw [hc1]
    _ = D.p2 e * (D.p4 (c * e) * u) * D.p4 f := by group
    _ = D.p2 e * (u * D.p4 (c * e)) * D.p4 f := by rw [hc2]
    _ = D.p2 e * u * (D.p4 (c * e) * D.p4 f) := by group
    _ = D.p2 e * u * D.p4 (f + c * e) := by rw [← D.p4_add, add_comm]

end Ncalc

end CFSG.GH74.GLS.Stage4.Hex
