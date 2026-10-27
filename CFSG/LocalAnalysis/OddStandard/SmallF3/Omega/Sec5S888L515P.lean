module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PrB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem s888_sl23_exists_noncomm : ∃ a b : SL23, a * b ≠ b * a := by
  decide +kernel

theorem sec5_pair_unique (hF2 : Asc82FactPocketsTwo) {X : Subgroup G} {z : G}
    (hz2 : orderOf z = 2) {K₁ K₂ P₁ P₂ : Subgroup G} (hp : Sec5Pair K₁ K₂ z)
    (hM : K₁ ⊔ K₂ = twoRes (X ⊓ centralizer ({z} : Set G))) (hP₁ : Sl23PocketIn X z P₁)
    (hP₂ : Sl23PocketIn X z P₂) (hne : P₁ ≠ P₂) (hle : P₁ ⊔ P₂ ≤ K₁ ⊔ K₂) :
    (P₁ = K₁ ∧ P₂ = K₂) ∨ (P₁ = K₂ ∧ P₂ = K₁) := by
  obtain ⟨hK₁, hK₂⟩ := hp.pocket hM
  have hcomm : ⁅K₁, K₂⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hp.comm x hx y hy).symm
  have hneK : K₁ ≠ K₂ := by
    intro heq
    obtain ⟨a, b, hab⟩ := s888_sl23_exists_noncomm
    obtain ⟨e₁⟩ := hp.iso₁
    apply hab
    have hcomm' : ∀ x y : ↥K₁, x * y = y * x := by
      intro x y
      refine Subtype.ext ?_
      have hy2 : (y : G) ∈ K₂ := heq ▸ y.2
      exact hp.comm x x.2 y hy2
    simpa using congrArg e₁ (hcomm' (e₁.symm a) (e₁.symm b))
  have h1 := hF2 G X z K₁ K₂ P₁ hz2 hK₁ hK₂ hneK hcomm hM hp.iso₁ hp.iso₂ hP₁
    (le_sup_left.trans hle)
  have h2 := hF2 G X z K₁ K₂ P₂ hz2 hK₁ hK₂ hneK hcomm hM hp.iso₁ hp.iso₂ hP₂
    (le_sup_right.trans hle)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

end CFSG.OddStandard.SmallF3.Omega
