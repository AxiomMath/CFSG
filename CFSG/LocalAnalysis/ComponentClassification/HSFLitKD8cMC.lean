module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cNormMain

public section

namespace CFSG.ComponentClassification.HSFLit.KD8c

open Sec8

@[expose] def cidx (x : MC) : ℕ := x.a.val / 2 % 4 + 4 * (x.g.val / 2)

@[expose] def crep (j : ℕ) : MC :=
  ⟨⟨2 * (j % 4), by omega⟩, ⟨2 * (j / 4 % 8), by show 2 * (j / 4 % 8) < 16; omega⟩⟩

@[expose] def zpart (x : MC) : MC :=
  ⟨⟨x.a.val % 2 + 8 * (x.a.val / 8), by have := x.a.isLt; omega⟩, ⟨0, by norm_num⟩⟩

@[expose] def Ereps : Fin 8 → List ℕ :=
  ![[1, 2, 3], [2, 4, 6], [4, 16, 20], [8, 20, 28], [3, 13, 14], [13, 17, 28], [1, 16, 17],
    [6, 8, 14]]

theorem inZ_iff' : ∀ x : MC, inZ x = (inR1 x && cidx x == 0) := by decide +kernel

theorem crep_zpart : ∀ x : MC, inR1 x = true → crep (cidx x) * zpart x = x := by decide +kernel

theorem zpart_inZ : ∀ x : MC, inZ (zpart x) = true := by decide +kernel

theorem crep_inR1 : ∀ j : Fin 32, inR1 (crep j) = true := by decide +kernel

theorem cidx_lt (x : MC) : cidx x < 32 := by
  have h1 := x.g.isLt
  have h2 : x.a.val / 2 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  change x.g.val < 16 at h1
  unfold cidx
  omega

theorem cidx_crep_mul : ∀ α β : Fin 32, cidx (crep α * crep β) = α.val ^^^ β.val := by
  decide +kernel

theorem cidx_mul_Z : ∀ w : MC, inR1 w = true → ∀ z ∈ Zl, cidx (w * z) = cidx w := by
  decide +kernel

theorem Zl_central : ∀ z ∈ Zl, ∀ g : MC, inR1 g = true → z * g = g * z := by decide +kernel

theorem Zl_sq : ∀ z ∈ Zl, z * z = 1 := by decide +kernel

theorem inE_iff' : ∀ i : Fin 8, ∀ x : MC,
    inE i x = (inR1 x && (cidx x == 0 || (Ereps i).contains (cidx x))) := by
  decide +kernel

theorem pair_crep : ∀ α β : Fin 32, α.val ≠ 0 → β.val ≠ 0 → α ≠ β → crep α * crep α = 1 →
    crep β * crep β = 1 → crep α * crep β = crep β * crep α →
    ∃ i : Fin 8, α.val ∈ Ereps i ∧ β.val ∈ Ereps i := by
  decide +kernel

theorem cent_crep : ∀ i : Fin 8, ∀ α ∈ Ereps i, ∀ β ∈ Ereps i, α ≠ β → ∀ γ : Fin 32,
    crep γ * crep α = crep α * crep γ → crep γ * crep β = crep β * crep γ →
    γ.val = 0 ∨ γ.val ∈ Ereps i := by
  decide +kernel

end CFSG.ComponentClassification.HSFLit.KD8c
