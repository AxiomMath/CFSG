module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cIface
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cKInfl
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cNGlue

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Mix11cN Mix11cK

namespace Mix11cK

section Surj

theorem kclass_surj (h : Mix11cSL2Class) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ n) {K : Type} [Group K]
    (π : SLm F →* K) (hπ : Function.Surjective π) :
    (∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        (σ : Representation (ZMod p) K W), IsSimpleModule (MonoidAlgebra (ZMod p) K) σ.asModule →
        (∃ x, σ x ≠ 1) → 2 * n ≤ Module.finrank (ZMod p) W) ∧
    (∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        (σ : Representation (ZMod p) K W), IsSimpleModule (MonoidAlgebra (ZMod p) K) σ.asModule →
        2 * n < Module.finrank (ZMod p) W → Module.finrank (ZMod p) W < 4 * n →
        ((∀ w, σ (π (T2.negOne F)) w = -w) ∧ 3 * Module.finrank (ZMod p) W = 8 * n) ∨
        ((∀ w, σ (π (T2.negOne F)) w = w) ∧ Module.finrank (ZMod p) W = 3 * n ∧
          Nat.card (Module.End (MonoidAlgebra (ZMod p) K) σ.asModule) = p ^ n)) ∧
    (∀ (W W' : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
        [AddCommGroup W'] [Module (ZMod p) W'] [Module.Finite (ZMod p) W']
        (σ : Representation (ZMod p) K W) (σ' : Representation (ZMod p) K W'),
        IsSimpleModule (MonoidAlgebra (ZMod p) K) σ.asModule →
        IsSimpleModule (MonoidAlgebra (ZMod p) K) σ'.asModule →
        2 * n < Module.finrank (ZMod p) W → Module.finrank (ZMod p) W < 4 * n →
        Module.finrank (ZMod p) W' = Module.finrank (ZMod p) W →
        Nonempty (σ.asModule ≃ₗ[MonoidAlgebra (ZMod p) K] σ'.asModule)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2, h3⟩ := h p n hp hp2 hn F hF
  refine ⟨?_, ?_, ?_⟩
  · intro W _ _ _ σ hs hne
    exact h1 W (infl π σ) ((isSimpleModule_comp_iff π hπ σ).2 hs)
      ((exists_ne_one_comp_iff π hπ σ).2 hne)
  · intro W _ _ _ σ hs hlo hhi
    rcases h2 W (infl π σ) ((isSimpleModule_comp_iff π hπ σ).2 hs) hlo hhi with
      ⟨hneg, hd⟩ | ⟨hneg, hd, hcard⟩
    · exact Or.inl ⟨hneg, hd⟩
    · exact Or.inr ⟨hneg, hd, by rw [← card_end_comp π hπ σ]; exact hcard⟩
  · intro W W' _ _ _ _ _ _ σ σ' hs hs' hlo hhi hd
    obtain ⟨e⟩ := h3 W W' (infl π σ) (infl π σ') ((isSimpleModule_comp_iff π hπ σ).2 hs)
      ((isSimpleModule_comp_iff π hπ σ').2 hs') hlo hhi hd
    exact nonempty_equiv_of_comp π hπ σ σ' e

end Surj

end Mix11cK

end CFSG.GH74.GLS.Stage4.Rest
