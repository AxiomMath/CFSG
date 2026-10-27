module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13e_M1_aux (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {W : Subgroup G}
    (hWP : W ≤ q13P t tau x₁ x₂ rho om) (hNW : ctxN tau x₁ x₂ ≤ W)
    (hWM : ∀ g ∈ ctxM t tau x₁ x₂, ∀ w ∈ W, g * w * g⁻¹ ∈ W) {w : G} (hw : w ∈ W)
    (hwA : w ∉ q13AN t tau x₁ x₂ rho) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, p ∉ q13AN t tau x₁ x₂ rho → p ∈ W := by
  intro p hp hpA
  have hII := hD.A_cent
  obtain ⟨v, hv, hp2⟩ := q13e_sq_of_not_mem_AN h hD hp hpA
  obtain ⟨v₀, hv₀, hw2⟩ := q13e_sq_of_not_mem_AN h hD (hWP hw) hwA
  have hp2mem : p ^ 2 ∈ tau • (fourGrp x₁ x₂ : Set G) :=
    Set.mem_smul_set.mpr ⟨v, hv, by rw [smul_eq_mul, hp2]⟩
  have hw2mem : w ^ 2 ∈ tau • (fourGrp x₁ x₂ : Set G) :=
    Set.mem_smul_set.mpr ⟨v₀, hv₀, by rw [smul_eq_mul, hw2]⟩
  have hp2c : p ^ 2 ∈ conjIn (ctxM t tau x₁ x₂) tau := by
    rw [h.c11.tauM]; exact hp2mem
  have hw2c : w ^ 2 ∈ conjIn (ctxM t tau x₁ x₂) tau := by
    rw [h.c11.tauM]; exact hw2mem
  simp only [conjIn, Set.mem_setOf_eq] at hp2c hw2c
  obtain ⟨g₂, hg₂M, hg₂⟩ := hp2c
  obtain ⟨g₁, hg₁M, hg₁⟩ := hw2c
  let g := g₂ * g₁⁻¹
  have hgM : g ∈ ctxM t tau x₁ x₂ :=
    (ctxM t tau x₁ x₂).mul_mem hg₂M ((ctxM t tau x₁ x₂).inv_mem hg₁M)
  have hg₁' : g₁ * tau * g₁⁻¹ = tau * v₀ := hg₁.trans hw2
  have hg₂' : g₂ * tau * g₂⁻¹ = tau * v := hg₂.trans hp2
  have hg : g * (tau * v₀) * g⁻¹ = tau * v := by
    dsimp only [g]
    rw [← hg₁', ← hg₂']
    group
  let w' := g * w * g⁻¹
  have hw'W : w' ∈ W := hWM g hgM w hw
  have hw'P : w' ∈ q13P t tau x₁ x₂ rho om := hWP hw'W
  have hw'2 : w' ^ 2 = tau * v := by
    dsimp only [w']
    calc (g * w * g⁻¹) ^ 2 = g * w * g⁻¹ * (g * w * g⁻¹) := by rw [pow_two]
      _ = g * (w * w) * g⁻¹ := by group
      _ = g * w ^ 2 * g⁻¹ := by rw [pow_two]
      _ = g * (tau * v₀) * g⁻¹ := by rw [hw2]
      _ = tau * v := hg
  let u := p * w'⁻¹
  have huP : u ∈ q13P t tau x₁ x₂ rho om :=
    (q13P t tau x₁ x₂ rho om).mul_mem hp ((q13P t tau x₁ x₂ rho om).inv_mem hw'P)
  have hcomm : p * w'⁻¹ = w'⁻¹ * p :=
    q13d_P_comm h hII p hp w'⁻¹ ((q13P t tau x₁ x₂ rho om).inv_mem hw'P)
  have hpp : p ^ 2 = w' ^ 2 := by rw [hp2, hw'2]
  have hu2 : u ^ 2 = 1 := by
    dsimp only [u]
    rw [Commute.mul_pow hcomm 2, hpp, inv_pow, mul_inv_cancel]
  have huN : u ∈ ctxN tau x₁ x₂ := q13d_P_sq_eq_one_mem_N h hII u huP hu2
  have huW : u ∈ W := hNW huN
  have huw : u * w' = p := by dsimp only [u]; group
  rw [← huw]
  exact W.mul_mem huW hw'W

theorem q13e_M1 (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om)
    {W : Subgroup G} (hWP : W ≤ q13P t tau x₁ x₂ rho om) (hNW : ctxN tau x₁ x₂ ≤ W)
    (hWM : ∀ g ∈ ctxM t tau x₁ x₂, ∀ w ∈ W, g * w * g⁻¹ ∈ W) {w : G} (hw : w ∈ W)
    (hwA : w ∉ q13AN t tau x₁ x₂ rho) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, p ∈ W := by
  intro p hp
  by_cases hpA : p ∈ q13AN t tau x₁ x₂ rho
  · have hpwP : p * w ∈ q13P t tau x₁ x₂ rho om :=
      (q13P t tau x₁ x₂ rho om).mul_mem hp (hWP hw)
    have hpwA : p * w ∉ q13AN t tau x₁ x₂ rho := by
      intro hmem
      apply hwA
      have hpw : p⁻¹ * (p * w) = w := by group
      rw [← hpw]
      exact (q13AN t tau x₁ x₂ rho).mul_mem ((q13AN t tau x₁ x₂ rho).inv_mem hpA) hmem
    have hpwW : p * w ∈ W := q13e_M1_aux h hD hWP hNW hWM hw hwA (p * w) hpwP hpwA
    have hpeq : p = (p * w) * w⁻¹ := by group
    rw [hpeq]
    exact W.mul_mem hpwW (W.inv_mem hw)
  · exact q13e_M1_aux h hD hWP hNW hWM hw hwA p hp hpA

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
