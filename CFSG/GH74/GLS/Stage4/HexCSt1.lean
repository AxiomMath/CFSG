module

public import CFSG.GH74.GLS.Stage4.HexCAct
public import CFSG.GH74.GLS.Stage4.HexCSolve1

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

theorem stage1 (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData root F)
    (h2 : (2 : F) ≠ 0) {μ : G → F} (hμ : MuData D μ) {a2 a4 : F → F → F} {L : F → F → G}
    (hcd : CommData D a2 a4 L) {A2 A4 : F → F → F} {g3 : F → F → G} (had : ActData D A2 A4 g3) :
    ∃ e : F, μ (L 1 1) = 6 * e ∧ (∀ s t, a2 s t = 3 * e * s ^ 2 * t) ∧
      (∀ c s, A2 c s = e * c * s ^ 3) ∧ (∀ c s, μ (g3 c s) = 3 * e * c * s ^ 2) := by
  refine solve_stage1 h2 a2 A2 (fun c s => μ (g3 c s)) (fun s t => μ (L s t)) (μ (L 1 1))
    (fun s t => ?_) (fun s s' t => (comm15_add_s R hC D hμ hcd s s' t).1)
    (fun τ s t => (comm15_torus R D hcd τ s t).1)
    (fun c s t => act_comm R hC D hμ hcd had c s t) (fun c c' s => ?_)
    (fun c s s' => (act_add_s R hC D hμ hcd had c s s').1)
    (fun τ c s => (act_torus R D had τ c s).1)
  · rw [L_eq_mul R D hcd s t, mu_L R hC D hμ hcd (s * t)]
  · have h1 := (act_add_c R hC D hμ had c c' s).2.2
    have h3 := (act_add_c R hC D hμ had c' c s).2.2
    rw [add_comm c' c] at h3
    linear_combination h3 - h1

end CFSG.GH74.GLS.Stage4.Hex
