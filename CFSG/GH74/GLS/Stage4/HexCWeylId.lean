module

public import CFSG.GH74.GLS.Stage4.HexCNcalc
public import CFSG.GH74.GLS.Stage4.HexCNorm
public import CFSG.GH74.GLS.Stage4.HexCUniq

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

theorem weyl_aux {n u x y z : G} (hBR : n * u * n⁻¹ = u⁻¹ * n * u⁻¹) (hx : n * x * n⁻¹ = y)
    (hy : u * y = y * u) (hz : n * y * n⁻¹ = z) : n * (u * x * u⁻¹) * n⁻¹ = u⁻¹ * z * u := by
  have hBR' : n * u⁻¹ * n⁻¹ = u * n⁻¹ * u := by
    have : n * u⁻¹ * n⁻¹ = (n * u * n⁻¹)⁻¹ := by group
    rw [this, hBR]; group
  have hyc : u⁻¹ * y * u = y := by rw [mul_assoc, ← hy, inv_mul_cancel_left]
  calc n * (u * x * u⁻¹) * n⁻¹ = (n * u * n⁻¹) * (n * x * n⁻¹) * (n * u⁻¹ * n⁻¹) := by group
    _ = (u⁻¹ * n * u⁻¹) * y * (u * n⁻¹ * u) := by rw [hBR, hx, hBR']
    _ = u⁻¹ * (n * (u⁻¹ * y * u) * n⁻¹) * u := by group
    _ = u⁻¹ * z * u := by rw [hyc, hz]

theorem weyl_conj_Nel (hC : Hex6Comm root) (D : HexData root F) {n : G} {f₂ f₄ : F → F}
    (hf2 : ∀ d, n * D.p2 d * n⁻¹ = D.p4 (f₂ d)) (hf4 : ∀ d, n * D.p4 d * n⁻¹ = D.p2 (f₄ d))
    (e f : F) {v : G} (hv : n * v * n⁻¹ ∈ root 3) :
    n * Nel D e v f * n⁻¹ = Nel D (f₄ f) (n * v * n⁻¹) (f₂ e) := by
  unfold Nel
  have hA : D.p4 (f₂ e) * (n * v * n⁻¹) = (n * v * n⁻¹) * D.p4 (f₂ e) :=
    (hC.c34 _ hv _ (D.p4_mem _)).symm
  have hB : D.p4 (f₂ e) * D.p2 (f₄ f) = D.p2 (f₄ f) * D.p4 (f₂ e) :=
    (hC.l24 _ (D.p2_mem _) _ (D.p4_mem _)).symm
  have hC' : (n * v * n⁻¹) * D.p2 (f₄ f) = D.p2 (f₄ f) * (n * v * n⁻¹) :=
    (hC.c23 _ (D.p2_mem _) _ hv).symm
  calc n * (D.p2 e * v * D.p4 f) * n⁻¹
      = (n * D.p2 e * n⁻¹) * (n * v * n⁻¹) * (n * D.p4 f * n⁻¹) := by group
    _ = D.p4 (f₂ e) * (n * v * n⁻¹) * D.p2 (f₄ f) := by rw [hf2, hf4]
    _ = D.p2 (f₄ f) * (n * v * n⁻¹) * D.p4 (f₂ e) := by
      rw [hA, mul_assoc, hB, ← mul_assoc, hC']

theorem weyl_cmp (R : RGD2 6 H r₁ r₂ U root) (D : HexData root F) {VL VR : G}
    (hVL : VL ∈ Vsub root 2 4) (hVR : VR ∈ Vsub root 2 4) {a a' b b' : F}
    (hK : ⁅D.p1 a', D.p5 b'⁆ ∈ Vsub root 2 4)
    (h : VL * D.p1 a * D.p5 b = VR * D.p5 b' * D.p1 a') : a = a' ∧ b = b' := by
  obtain ⟨K', hK'⟩ : ∃ K', K' = ⁅D.p5 b', D.p1 a'⁆ := ⟨_, rfl⟩
  have hK'mem : K' ∈ Vsub root 2 4 := by
    rw [hK', ← commutatorElement_inv]; exact (Vsub root 2 4).inv_mem hK
  have hcomm : D.p5 b' * D.p1 a' = K' * (D.p1 a' * D.p5 b') := by
    rw [hK']; simp only [commutatorElement_def]; group
  rw [mul_assoc VR, hcomm] at h
  obtain ⟨P, hP⟩ : ∃ P, P = VL⁻¹ * (VR * K') := ⟨_, rfl⟩
  have hPmem : P ∈ Vsub root 2 4 := by
    rw [hP]
    exact (Vsub root 2 4).mul_mem ((Vsub root 2 4).inv_mem hVL)
      ((Vsub root 2 4).mul_mem hVR hK'mem)
  have h1 : D.p1 a * D.p5 b = P * (D.p1 a' * D.p5 b') := by
    calc D.p1 a * D.p5 b = VL⁻¹ * (VL * D.p1 a * D.p5 b) := by group
      _ = VL⁻¹ * (VR * (K' * (D.p1 a' * D.p5 b'))) := by rw [h]
      _ = P * (D.p1 a' * D.p5 b') := by rw [hP]; group
  have hx : (D.p1 a')⁻¹ * D.p1 a ∈ root 1 :=
    (root 1).mul_mem ((root 1).inv_mem (D.p1_mem _)) (D.p1_mem _)
  have hy : D.p5 b * (D.p5 b')⁻¹ ∈ root 5 :=
    (root 5).mul_mem (D.p5_mem _) ((root 5).inv_mem (D.p5_mem _))
  have hP' : (D.p1 a')⁻¹ * P * D.p1 a' ∈ Vsub root 2 4 := by
    have := root1_norm R ((root 1).inv_mem (D.p1_mem a')) hPmem
    simpa using this
  have h2 : ((D.p1 a')⁻¹ * D.p1 a) * (D.p5 b * (D.p5 b')⁻¹) ∈ Vsub root 2 4 := by
    have e : ((D.p1 a')⁻¹ * D.p1 a) * (D.p5 b * (D.p5 b')⁻¹) = (D.p1 a')⁻¹ * P * D.p1 a' := by
      calc _ = (D.p1 a')⁻¹ * (D.p1 a * D.p5 b) * (D.p5 b')⁻¹ := by group
        _ = (D.p1 a')⁻¹ * (P * (D.p1 a' * D.p5 b')) * (D.p5 b')⁻¹ := by rw [h1]
        _ = _ := by group
    rw [e]; exact hP'
  obtain ⟨hx1, hy1⟩ := rgd2_unique_15 R hx hy h2
  exact ⟨D.p1_inj (inv_mul_eq_one.1 hx1).symm, D.p5_inj (mul_inv_eq_one.1 hy1)⟩

end CFSG.GH74.GLS.Stage4.Hex
