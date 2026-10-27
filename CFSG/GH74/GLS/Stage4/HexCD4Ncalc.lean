module

public import CFSG.GH74.GLS.Stage4.HexCD4Mu

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F K : Type} [Field F] [Field K]

@[expose] def Nel4 (D : HexData4 root F K) (e : F) (u : G) (f : F) : G := D.p2 e * u * D.p4 f

section Ncalc

variable (hC : Hex6Comm root) (D : HexData4 root F K)

theorem Nel4_mem {e : F} {u : G} {f : F} (hu : u ∈ root 3) : Nel4 D e u f ∈ Vsub root 2 4 :=
  mem_V24_of (D.p2_mem e) hu (D.p4_mem f)

include hC in
theorem Nel4_mul {e e' f f' : F} {u u' : G} (hu : u ∈ root 3) (hu' : u' ∈ root 3) :
    Nel4 D e u f * Nel4 D e' u' f' = Nel4 D (e + e') (u * u') (f + f') := by
  have hCA : Commute (D.p4 f) (D.p2 e') := (hC.l24 _ (D.p2_mem e') _ (D.p4_mem f)).symm
  have hCB : Commute (D.p4 f) u' := (hC.c34 u' hu' _ (D.p4_mem f)).symm
  have hBA : Commute u (D.p2 e') := (hC.c23 _ (D.p2_mem e') u hu).symm
  unfold Nel4
  rw [(Commute.mul_right hCA hCB).mul_mul_mul_comm (D.p2 e * u) (D.p4 f'),
    hBA.mul_mul_mul_comm (D.p2 e) u', D.p2_add, D.p4_add]

include hC in
theorem conj_p1_Nel4 {β : K → G → F} (hβ : PairData D β) (s : K) (e f : F) {u : G}
    (hu : u ∈ root 3) :
    D.p1 s * Nel4 D e u f * (D.p1 s)⁻¹ = Nel4 D (e + β s u) u f := by
  have h1 : D.p1 s * D.p2 e * (D.p1 s)⁻¹ = D.p2 e := by
    rw [mul_inv_eq_iff_eq_mul]; exact hC.c12 _ (D.p1_mem s) _ (D.p2_mem e)
  have h3 : D.p1 s * D.p4 f * (D.p1 s)⁻¹ = D.p4 f := by
    rw [mul_inv_eq_iff_eq_mul]; exact hC.o14 _ (D.p1_mem s) _ (D.p4_mem f)
  have h2 : D.p1 s * u * (D.p1 s)⁻¹ = D.p2 (β s u) * u := by
    rw [← hβ.r1 s u hu]; simp only [commutatorElement_def]; group
  unfold Nel4
  calc D.p1 s * (D.p2 e * u * D.p4 f) * (D.p1 s)⁻¹
      = (D.p1 s * D.p2 e * (D.p1 s)⁻¹) * (D.p1 s * u * (D.p1 s)⁻¹) *
        (D.p1 s * D.p4 f * (D.p1 s)⁻¹) := by group
    _ = D.p2 e * (D.p2 (β s u) * u) * D.p4 f := by rw [h1, h2, h3]
    _ = D.p2 (e + β s u) * u * D.p4 f := by rw [D.p2_add]; group

include hC in
theorem conj_p5_Nel4 {β : K → G → F} (hβ : PairData D β) (t : K) (e f : F) {u : G}
    (hu : u ∈ root 3) :
    D.p5 t * Nel4 D e u f * (D.p5 t)⁻¹ = Nel4 D e u (f + β t u) := by
  have h1 : D.p5 t * D.p2 e * (D.p5 t)⁻¹ = D.p2 e := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.o25 _ (D.p2_mem e) _ (D.p5_mem t)).symm
  have h3 : D.p5 t * D.p4 f * (D.p5 t)⁻¹ = D.p4 f := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.c45 _ (D.p4_mem f) _ (D.p5_mem t)).symm
  have h2 : D.p5 t * u * (D.p5 t)⁻¹ = D.p4 (β t u) * u := by
    rw [← hβ.r5 t u hu]; simp only [commutatorElement_def]; group
  have hc : D.p4 (β t u) * u = u * D.p4 (β t u) := (hC.c34 u hu _ (D.p4_mem _)).symm
  unfold Nel4
  calc D.p5 t * (D.p2 e * u * D.p4 f) * (D.p5 t)⁻¹
      = (D.p5 t * D.p2 e * (D.p5 t)⁻¹) * (D.p5 t * u * (D.p5 t)⁻¹) *
        (D.p5 t * D.p4 f * (D.p5 t)⁻¹) := by group
    _ = D.p2 e * (D.p4 (β t u) * u) * D.p4 f := by rw [h1, h2, h3]
    _ = D.p2 e * u * (D.p4 (β t u) * D.p4 f) := by rw [hc]; group
    _ = D.p2 e * u * D.p4 (f + β t u) := by rw [← D.p4_add, add_comm]

include hC in
theorem conj_p6_Nel4 (c e f : F) {u : G} (hu : u ∈ root 3) :
    D.p6 c * Nel4 D e u f * (D.p6 c)⁻¹ = Nel4 D e u (f + c * e) := by
  have h1 : D.p6 c * D.p2 e * (D.p6 c)⁻¹ = D.p4 (c * e) * D.p2 e := by
    rw [← D.rel_long c e]; simp only [commutatorElement_def]; group
  have h2 : D.p6 c * u * (D.p6 c)⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.o36 u hu _ (D.p6_mem c)).symm
  have h3 : D.p6 c * D.p4 f * (D.p6 c)⁻¹ = D.p4 f := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.l46 _ (D.p4_mem f) _ (D.p6_mem c)).symm
  have hc1 : D.p4 (c * e) * D.p2 e = D.p2 e * D.p4 (c * e) :=
    (hC.l24 _ (D.p2_mem e) _ (D.p4_mem _)).symm
  have hc2 : D.p4 (c * e) * u = u * D.p4 (c * e) := (hC.c34 u hu _ (D.p4_mem _)).symm
  unfold Nel4
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


section Ls

variable (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData4 root F K)

include R in
theorem Nel4_inj {e e' f f' : F} {u u' : G} (hu : u ∈ root 3) (hu' : u' ∈ root 3)
    (h : Nel4 D e u f = Nel4 D e' u' f') : e = e' ∧ u = u' ∧ f = f' := by
  obtain ⟨h1, h2, h3⟩ := rgd2_unique_234 R (D.p2_mem e) (D.p2_mem e') hu hu' (D.p4_mem f)
    (D.p4_mem f') h
  exact ⟨D.p2_inj h1, h2, D.p4_inj h3⟩

theorem conj_T_Nel4 (t : Fˣ) {e f : F} {u : G} (hu : u ∈ root 3) :
    D.T t * Nel4 D e u f * (D.T t)⁻¹ = Nel4 D ((t : F)⁻¹ * e) u ((t : F) * f) := by
  have hTu : D.T t * u * (D.T t)⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul, D.T_eq]; exact D.cent3 _ u hu
  unfold Nel4
  calc D.T t * (D.p2 e * u * D.p4 f) * (D.T t)⁻¹
      = (D.T t * D.p2 e * (D.T t)⁻¹) * (D.T t * u * (D.T t)⁻¹) * (D.T t * D.p4 f * (D.T t)⁻¹) := by
        group
    _ = _ := by rw [D.w2, hTu, D.w4]

end Ls

end CFSG.GH74.GLS.Stage4.Hex
