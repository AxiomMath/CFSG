module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FCount

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E27Lie

theorem ev_inj {K I : Type*} [CommRing K] (r : I → I) (f : I → K) (S : Set I)
    (hreach : ∀ δ, δ ∈ S ∨ r δ ∈ S ∨ r (r δ) ∈ S) (a b : I → K)
    (ha : ∀ δ, a δ = f δ * a (r δ)) (hb : ∀ δ, b δ = f δ * b (r δ))
    (h : ∀ δ ∈ S, a δ = b δ) : a = b := by
  funext δ
  rcases hreach δ with h0 | h1 | h2
  · exact h δ h0
  · rw [ha δ, hb δ, h _ h1]
  · have e1 : a (r δ) = b (r δ) := by
      rw [ha (r δ), hb (r δ), h _ h2]
    rw [ha δ, hb δ, e1]

variable {K : Type} [Field K] [Finite K]


theorem layerImage_coord {α : MulAut ↥(adjointGroup Tag.D4 K)}
    (la : LayerAct Tag.D4 α (1 : K ≃+* K)) {A : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hfix : ∀ a ∈ A, α a = a) (k : ℕ) {q : UnitCoord Tag.D4 K k} (hq : q ∈ layerImage A k)
    (δ : UnitRoots Tag.D4 k) :
    Multiplicative.toAdd q δ = la.f k δ * Multiplicative.toAdd q (la.r k δ) := by
  have h := congrArg (fun q' : UnitCoord Tag.D4 K k => Multiplicative.toAdd q' δ)
    (layerImage_fixed la hfix k hq)
  exact h.symm

theorem layerImage_card_le {α : MulAut ↥(adjointGroup Tag.D4 K)}
    (la : LayerAct Tag.D4 α (1 : K ≃+* K)) {A : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hfix : ∀ a ∈ A, α a = a) (k : ℕ) (δ₀ : UnitRoots Tag.D4 k)
    (hreach : ∀ δ : UnitRoots Tag.D4 k,
      δ = δ₀ ∨ la.r k δ = δ₀ ∨ la.r k (la.r k δ) = δ₀) :
    Nat.card (layerImage A k) ≤ Nat.card K := by
  refine Nat.card_le_card_of_injective (fun q => Multiplicative.toAdd q.1 δ₀) ?_
  intro q q' h
  have := ev_inj (la.r k) (la.f k) {δ₀} (fun δ => by simpa using hreach δ)
    (Multiplicative.toAdd q.1) (Multiplicative.toAdd q'.1)
    (layerImage_coord la hfix k q.2) (layerImage_coord la hfix k q'.2)
    (fun δ hδ => by rw [Set.mem_singleton_iff.1 hδ]; exact h)
  exact Subtype.ext (Multiplicative.toAdd.injective this)

end CFSG.LocalAnalysis.GLTheoremA
