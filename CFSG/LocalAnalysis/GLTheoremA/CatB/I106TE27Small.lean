module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TE27Lift
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.E27

open Equiv Equiv.Perm Matrix

@[expose] def a9Elt (a b c d : Fin 9) (h₁ : a ≠ b) (h₂ : c ≠ d) : alternatingGroup (Fin 9) :=
  ⟨swap a b * swap c d, by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap h₁, sign_swap h₂]
    exact Int.units_mul_self _⟩

@[expose] def a9x₀ : alternatingGroup (Fin 9) := a9Elt 0 1 1 2 (by decide) (by decide)

@[expose] def a9x₁ : alternatingGroup (Fin 9) := a9Elt 3 4 4 5 (by decide) (by decide)

@[expose] def a9x₂ : alternatingGroup (Fin 9) := a9Elt 6 7 7 8 (by decide) (by decide)

@[expose] def a9n₀ : alternatingGroup (Fin 9) := a9Elt 1 2 3 4 (by decide) (by decide)

@[expose] def a9n₁ : alternatingGroup (Fin 9) := a9Elt 1 2 6 7 (by decide) (by decide)

@[expose] def a9Dec (σ : alternatingGroup (Fin 9)) : Fin 3 × Fin 3 × Fin 3 :=
  (⟨((σ : Perm (Fin 9)) 0).val % 3, Nat.mod_lt _ (by norm_num)⟩,
    ⟨((σ : Perm (Fin 9)) 3).val % 3, Nat.mod_lt _ (by norm_num)⟩,
    ⟨((σ : Perm (Fin 9)) 6).val % 3, Nat.mod_lt _ (by norm_num)⟩)

theorem a9Dec_prod3 : ∀ v, a9Dec (prod3 a9x₀ a9x₁ a9x₂ v) = v := by decide +kernel

theorem e27Lifts_alt9 : E27Lifts (alternatingGroup (Fin 9)) :=
  e27Lifts_of_pairs (x₀ := a9x₀) (x₁ := a9x₁) (x₂ := a9x₂) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (Function.LeftInverse.injective a9Dec_prod3)
    ⟨a9n₀, by decide +kernel⟩ ⟨a9n₀, by decide +kernel⟩ ⟨a9n₁, by decide +kernel⟩
    (Or.inl ⟨a9n₁, by decide +kernel, by decide +kernel⟩)
    (Or.inl ⟨a9n₀, by decide +kernel, by decide +kernel⟩)
    (Or.inl ⟨a9n₀, by decide +kernel, by decide +kernel⟩)

@[expose] def plM (k : Fin 3) (a b c d : ZMod 2) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fromBlocks (diagonal fun i => if i = k then a else 1) (diagonal fun i => if i = k then b else 0)
    (diagonal fun i => if i = k then c else 0) (diagonal fun i => if i = k then d else 1)

theorem plM_x_mul : ∀ k, plM k 0 1 1 1 * plM k 1 1 1 0 = 1 := by decide +kernel

theorem plM_x_mul' : ∀ k, plM k 1 1 1 0 * plM k 0 1 1 1 = 1 := by decide +kernel

theorem plM_t_mul : ∀ k, plM k 0 1 1 0 * plM k 0 1 1 0 = 1 := by decide +kernel

theorem plM_x_sp : ∀ k, (plM k 0 1 1 1)ᵀ * fromBlocks 0 1 (-1) 0 * plM k 0 1 1 1 =
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) := by
  decide +kernel

theorem plM_t_sp : ∀ k, (plM k 0 1 1 0)ᵀ * fromBlocks 0 1 (-1) 0 * plM k 0 1 1 0 =
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) := by
  decide +kernel

@[expose] def spX (k : Fin 3) : CFSG.Open.StatedSp 3 (ZMod 2) :=
  ⟨⟨plM k 0 1 1 1, plM k 1 1 1 0, plM_x_mul k, plM_x_mul' k⟩,
    CFSG.Open.StatedAPI.mem_statedSp_iff.mpr (plM_x_sp k)⟩

@[expose] def spT (k : Fin 3) : CFSG.Open.StatedSp 3 (ZMod 2) :=
  ⟨⟨plM k 0 1 1 0, plM k 0 1 1 0, plM_t_mul k, plM_t_mul k⟩,
    CFSG.Open.StatedAPI.mem_statedSp_iff.mpr (plM_t_sp k)⟩

@[expose] def dec2 (a b : ZMod 2) : Fin 3 := if a = 0 then 1 else if b = 0 then 0 else 2

@[expose] def spDec (g : CFSG.Open.StatedSp 3 (ZMod 2)) : Fin 3 × Fin 3 × Fin 3 :=
  (dec2 ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) (.inl 0) (.inl 0))
      ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) (.inl 0) (.inr 0)),
    dec2 ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) (.inl 1) (.inl 1))
      ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) (.inl 1) (.inr 1)),
    dec2 ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) (.inl 2) (.inl 2))
      ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) (.inl 2) (.inr 2)))

theorem spDec_prod3 : ∀ v, spDec (prod3 (spX 0) (spX 1) (spX 2) v) = v := by decide +kernel

theorem e27Lifts_sp62 : E27Lifts (CFSG.Open.StatedSp 3 (ZMod 2)) :=
  e27Lifts_of_pairs (x₀ := spX 0) (x₁ := spX 1) (x₂ := spX 2) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (Function.LeftInverse.injective spDec_prod3)
    ⟨spT 0, by decide +kernel⟩ ⟨spT 1, by decide +kernel⟩ ⟨spT 2, by decide +kernel⟩
    (Or.inl ⟨spT 0, by decide +kernel, by decide +kernel⟩)
    (Or.inl ⟨spT 0, by decide +kernel, by decide +kernel⟩)
    (Or.inl ⟨spT 1, by decide +kernel, by decide +kernel⟩)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.E27
