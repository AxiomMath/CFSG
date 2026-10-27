module

public import CFSG.GH74.GLS.IVK.Prod32.LangClasses
public import CFSG.GH74.GLS.IVK.Prod32.LangFixed

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace ConjU

variable {X : Type} [Group X]

theorem mono {A B : Subgroup X} (hAB : A ≤ B) {x y : X} (h : ConjUnder A x y) : ConjUnder B x y := by
  obtain ⟨g, hg, hgxy⟩ := h
  exact ⟨g, hAB hg, hgxy⟩

theorem symm {A : Subgroup X} {x y : X} (h : ConjUnder A x y) : ConjUnder A y x := by
  obtain ⟨g, hg, hgxy⟩ := h
  refine ⟨g⁻¹, A.inv_mem hg, ?_⟩
  rw [← hgxy]
  group

theorem trans {A : Subgroup X} {x y w : X} (h₁ : ConjUnder A x y) (h₂ : ConjUnder A y w) :
    ConjUnder A x w := by
  obtain ⟨g, hg, hgxy⟩ := h₁
  obtain ⟨g', hg', hgyw⟩ := h₂
  refine ⟨g' * g, A.mul_mem hg' hg, ?_⟩
  rw [← hgyw, ← hgxy]
  group

end ConjU

section A8

variable {H : Type} [Group H] {K₁ K₂ : Subgroup H} {z a : H} {T : Subgroup H}

theorem prod3_Cg_Ch {F : Type} [Field F] [Finite F] {e₁ : ↥K₁ ≃* SL2 F} {e₂ : ↥K₂ ≃* SL2 F}
    {σ : F ≃+* F} (hL : LangHyp K₁ K₂ z a e₁ e₂ σ σ) {Y : Subgroup H} {r : ℕ} (hr : 3 ≤ r)
    (hF : Nat.card F = r ^ 4)
    (hdiag : P T K₁ K₂ ≠ Y → ∃ y ∈ Y, DiagOutE K₁ e₁ y ∧ DiagOutE K₂ e₂ y ∧
      Y = P T K₁ K₂ ⊔ zpowers y)
    (hc : ∀ y ∈ Y, ⁅y, a⁆ ∈ K₁ ⊔ K₂) :
    Cg K₁ K₂ Y z a T ∧ Ch K₁ K₂ a r := by
  refine ⟨⟨hL.two_classes, ?_, hL.z_class⟩, hL.fixed hr hF hF⟩
  intro hne u hu v hv
  obtain ⟨y, hyY, hy₁, hy₂, -⟩ := hdiag hne
  have hcK : ⁅y, a⁆ ∈ K₁ ⊔ K₂ := hc y hyY
  have hya : y * a * y⁻¹ = ⁅y, a⁆ * a := by
    rw [commutatorElement_def]
    group
  obtain ⟨hca, hnca⟩ := hL.fuse hy₁ hy₂ hcK hya
  obtain ⟨b, hb, hbn, hball⟩ := hL.two_classes
  have hKY : K₁ ⊔ K₂ ≤ K₁ ⊔ K₂ ⊔ Y := le_sup_left
  have hcb : ConjUnder (K₁ ⊔ K₂) b (⁅y, a⁆ * a) := (hball _ hca).resolve_left hnca
  have hca' : ConjUnder (K₁ ⊔ K₂ ⊔ Y) (⁅y, a⁆ * a) a := by
    refine ⟨y⁻¹, (K₁ ⊔ K₂ ⊔ Y).inv_mem (Subgroup.mem_sup_right hyY), ?_⟩
    rw [← hya]
    group
  have hba : ConjUnder (K₁ ⊔ K₂ ⊔ Y) b a := ConjU.trans (ConjU.mono hKY hcb) hca'
  have key : ∀ w ∈ invCoset (K₁ ⊔ K₂) a, ConjUnder (K₁ ⊔ K₂ ⊔ Y) a w := by
    intro w hw
    rcases hball w hw with h1 | h1
    · exact ConjU.mono hKY h1
    · exact ConjU.trans (ConjU.symm hba) (ConjU.mono hKY h1)
  exact ConjU.trans (ConjU.symm (key u hu)) (key v hv)

end A8

end CFSG.GH74.GLS.IVK.Prod3
