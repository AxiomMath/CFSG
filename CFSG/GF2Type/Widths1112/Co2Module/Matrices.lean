module

public import CFSG.GF2Type.Widths1112.Co2Module.Idempotents

public section

namespace CFSG.GF2Type.Widths1112.Co2Module

@[expose] def coef (c : ZMod 3) : Fin 2 → ZMod 2 :=
  if c = 0 then ![1, 0] else if c = 1 then ![0, 1] else ![1, 1]

abbrev BIdx : Type := Fin 2 ⊕ (Fin 10 × Fin 2)

@[expose] def idxEncode : BIdx → Fin 22
  | Sum.inl a => ⟨a.val, by omega⟩
  | Sum.inr (i, j) => ⟨2 + 2 * i.val + j.val, by omega⟩

@[expose] def idxDecode (k : Fin 22) : BIdx :=
  if h : k.val < 2 then Sum.inl ⟨k.val, h⟩
  else Sum.inr (⟨(k.val - 2) / 2, by omega⟩, ⟨(k.val - 2) % 2, by omega⟩)

@[expose] def idxEquiv : BIdx ≃ Fin 22 where
  toFun := idxEncode
  invFun := idxDecode
  left_inv := by decide
  right_inv := by decide

@[expose] def cfTab (w₁ v₀ : F3Vec) (u : Fin 10 → Fin 2 → F3Vec) (i : Fin 10) (j : Fin 2)
    (c : Fin 2) : ZMod 2 :=
  coef ((w₁ ⬝ᵥ u i j) * (w₁ ⬝ᵥ v₀)⁻¹) c

@[expose] def Xmat (θ : Matrix (Fin 2) (Fin 2) (ZMod 2)) (σ : Fin 10 → Fin 10)
    (cf : Fin 10 → Fin 2 → Fin 2 → ZMod 2) : Matrix BIdx BIdx (ZMod 2) :=
  Matrix.of fun r k => match r, k with
    | Sum.inl a', Sum.inl a => θ a' a
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr (i', c), Sum.inr (i, j) => if i' = σ i then cf i j c else 0

@[expose] def Qmat (S : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Matrix BIdx BIdx (ZMod 2) :=
  Matrix.of fun r k => match r, k with
    | Sum.inl a', Sum.inl a => S a' a
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr p', Sum.inr p => if p' = p then 1 else 0

@[expose] def Xfin (θ : Matrix (Fin 2) (Fin 2) (ZMod 2)) (σ : Fin 10 → Fin 10)
    (cf : Fin 10 → Fin 2 → Fin 2 → ZMod 2) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Matrix.reindex idxEquiv idxEquiv (Xmat θ σ cf)

@[expose] def Qfin (S : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Matrix.reindex idxEquiv idxEquiv (Qmat S)

@[expose] def wordProd {M : Type*} [Monoid M] (G : Fin 2 → M) (w : List (Fin 2 × ℕ)) : M :=
  (w.map fun q => G q.1 ^ q.2).prod

@[expose] def iN (s : Fin 2) : Fin 8 := ⟨s.val, by omega⟩

@[expose] def iY (k : Fin 3) : Fin 8 := ⟨2 + k.val, by omega⟩

@[expose] def iZ (k : Fin 3) : Fin 8 := ⟨5 + k.val, by omega⟩

end CFSG.GF2Type.Widths1112.Co2Module
