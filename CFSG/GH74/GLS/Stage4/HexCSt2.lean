module

public import CFSG.GH74.GLS.Stage4.HexCSolve2
public import CFSG.GH74.GLS.Stage4.HexCSt1
public import CFSG.GH74.GLS.Stage4.HexCWeylSlot

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

theorem stage2 (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData root F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {μ : G → F} (hμ : MuData D μ) {a2 a4 : F → F → F}
    {L : F → F → G} (hcd : CommData D a2 a4 L) {A2 A4 : F → F → F} {g3 : F → F → G}
    (had : ActData D A2 A4 g3) {n : G} (hnφ : n = D.φ (sl2W F))
    (hnact : ActsPos 6 root n (fun q => 4 - q)) :
    ∃ e : F, (∀ s t, a2 s t = 3 * e * s ^ 2 * t) ∧ (∀ s t, μ (L s t) = 6 * e * (s * t)) ∧
      (∀ s t, a4 s t = 3 * e * s * t ^ 2) ∧ (∀ c s, A2 c s = e * c * s ^ 3) ∧
      (∀ c s, μ (g3 c s) = 3 * e * c * s ^ 2) ∧ (∀ c s, A4 c s = 2 * e * c ^ 2 * s ^ 3) := by
  obtain ⟨e, hκ, ha2, hA2, hMg⟩ := stage1 R hC D h2 hμ hcd had
  have hmuL : ∀ s t, μ (L s t) = 6 * e * (s * t) := by
    intro s t
    rw [L_eq_mul R D hcd s t, mu_L R hC D hμ hcd, hκ]
  have ha4 : ∀ s t, a4 s t = 3 * e * s * t ^ 2 := by
    refine solve_a4 h2 e a4 (fun s s' t => (comm15_add_s R hC D hμ hcd s s' t).2.2)
      (fun s t t' => ?_) (fun τ s t => (comm15_torus R D hcd τ s t).2.2)
    have := (comm15_add_t R hC D hμ hcd s t t').2.2
    rwa [hmuL] at this
  obtain ⟨-, -, ⟨f₂, hf2⟩, -⟩ := weyl_coords D hnact
  obtain ⟨-, ⟨f₅, hf5⟩, -, -⟩ := weyl_coords D hnact
  obtain ⟨⟨f₁, hf1⟩, -, -, -⟩ := weyl_coords D hnact
  obtain ⟨-, -, -, ⟨f₄, hf4⟩⟩ := weyl_coords D hnact
  have hf2add : ∀ x y, f₂ (x + y) = f₂ x + f₂ y := fun x y =>
    conj_add_of D.p2_add D.p4_add D.p4_inj hf2 x y
  have hA4 : ∀ c s, A4 c s = 2 * e * c ^ 2 * s ^ 3 := by
    refine solve_A4 h2 h3 e a4 A4 f₂ hf2add ha4 (fun c c' s => ?_) (fun c s s' => ?_)
      (fun τ c s => (act_torus R D had τ c s).2.2) (fun s => ?_)
    · have := (act_add_c R hC D hμ had c c' s).2.2
      rwa [hA2 c' s, hMg c s] at this
    · have := (act_add_s R hC D hμ hcd had c s s').2.2
      rwa [hμ.add _ (had.g3_mem c s') _ (hcd.L_mem s (c * s')), hMg c s', hmuL] at this
    · have := weyl_slot R hC D hcd had hnφ hnact hf1 hf5 hf2 hf4 s
      rwa [hA2 1 s] at this
  exact ⟨e, ha2, hmuL, ha4, hA2, hMg, hA4⟩

end CFSG.GH74.GLS.Stage4.Hex
