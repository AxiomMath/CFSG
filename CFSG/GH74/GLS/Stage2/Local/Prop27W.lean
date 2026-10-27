module

public import CFSG.GH74.GLS.Stage2.Local.Prop28Weak

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local.Prop28

section Statements

variable {G : Type} [Group G]

@[expose] def Prop27WJ (z x : G) : Prop :=
  ((∃ r : ℕ, Odd r ∧ 3 < r ∧ IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun s => s = r)) ∨
      Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* alternatingGroup (Fin 7))) ∧
    x ∉ Jx x ∧ ∀ j ∈ Jx x, orderOf j = 2 → IsConj z (x * j)

@[expose] def Prop27WM12 (z x : G) : Prop :=
  ∃ q : ℕ, Odd q ∧ IVK.IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q) ∧
    ∀ u ∈ Jx x, orderOf u = 2 → IsConj z u

@[expose] def Prop27W (z : G) (k : Kind) : Prop :=
  (IsClassicalKind k → (∃ x₀ ∈ Cen z, IsNonCentralInvolution x₀) →
      ∃ x ∈ Cen z, IsNonCentralInvolution x ∧ Ixz z x ≠ ⊥ ∧ Prop27WJ z x) ∧
    (k = Kind.m12 → ∀ x ∈ Cen z, IsNonCentralInvolution x → Prop27WM12 z x)

@[expose] def Leaf_Prop27W
    (Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx G z k S → Prop27W z k

end Statements

section Classes

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}

theorem kind_cases_of_data (hcen : IsCentralInvolution z) (hd : Stage1Data G z S k) :
    (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) ∨
      ((IsClassicalKind k ∨ k = Kind.m12) ∧ ∃ x₀ : G, orderOf x₀ = 2 ∧ ¬ IsConj z x₀ ∧
        ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x₀ u) := by
  cases hd with
  | g2 h => exact Or.inl h.one_class
  | m12 h => exact Or.inr ⟨Or.inr rfl, h.two_classes⟩
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    obtain ⟨x, hx⟩ := h.two
    exact Or.inr ⟨Or.inl (Or.inl rfl), x, hx.x_inv,
      fun hc => hx.x_nonCentral (isCentralInvolution_of_isConj' hcen hc), hx.classes⟩
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    rcases h.fusion with ⟨-, hone⟩ | ⟨-, x, hx, -⟩
    · exact Or.inl hone
    · exact Or.inr ⟨Or.inl (Or.inr ⟨ε, rfl⟩), x, hx.x_inv,
        fun hc => hx.x_nonCentral (isCentralInvolution_of_isConj' hcen hc), hx.classes⟩
  | mcl h =>
    obtain ⟨n, -, h⟩ := h
    exact Or.inl h.one_class
  | ly h =>
    obtain ⟨n, -, h⟩ := h
    exact Or.inl h.one_class

end Classes

section Prop28

variable {G : Type} [Group G] [Finite G]

theorem compsGood_of_prop27W
    {z : G} {k : Kind} (hk : IsClassicalKind k) (hz : IsCentralInvolution z) {x₀ : G}
    (hcl : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x₀ u) (hW : Prop27W z k) {y : G}
    (hy : Prop27Y z y) : CompsGood y := by
  obtain ⟨x, -, hxnc, -, hJ⟩ := hW.1 hk ⟨y, hy.1, hy.2.1⟩
  have hxx₀ : IsConj x₀ x := isConj_second_class hz hcl hxnc
  have hclx : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x u := by
    intro u hu
    rcases hcl u hu with h | h
    · exact Or.inl h
    · exact Or.inr (hxx₀.symm.trans h)
  have hx : CompsGood x := by
    rcases hJ.1 with ⟨r, hr, hr3, hL2⟩ | hA7
    · exact compsGood_of_hat_isL2 hr hr3 hL2
    · exact compsGood_of_hat_A7 hA7
  exact compsGood_of_isConj (isConj_second_class hz hclx hy.2.1) hx

end Prop28

end CFSG.GH74.GLS.Stage2.Local
