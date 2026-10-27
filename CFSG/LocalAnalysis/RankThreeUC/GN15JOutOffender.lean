module

public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutBase
public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

@[expose] def FFOffenderInvertsOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W), Function.Injective ρ → CFSG.Open.IsKGroup G →
    CFSG.pCore 2 G = ⊥ → ∀ A : Subgroup G, CFSG.IsElementaryAbelian 2 ↥A →
    CFSG.RankThree.FFModules.IsBestOffender ρ A → ∀ L : Subgroup G,
    CFSG.Open.IsComponentOf L ⊤ → A ≤ Subgroup.normalizer (L : Set G) → ⁅L, A⁆ = L →
    ∀ a ∈ A, ∀ y ∈ Subgroup.normalizer (L : Set G), a * y * a⁻¹ = y⁻¹ →
      ∀ r e : ℕ, r.Prime → r ≠ 2 → orderOf y = r ^ e → y ∈ L ⊔ Subgroup.centralizer (L : Set G)

theorem commutator_mem_of_offender (hS : FFOffenderInvertsOdd) {G : Type} [Group G] [Finite G]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) G W} (hρ : Function.Injective ρ) (hK : CFSG.Open.IsKGroup G)
    (hO2 : CFSG.pCore 2 G = ⊥) {A : Subgroup G} (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hAb : CFSG.RankThree.FFModules.IsBestOffender ρ A) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hLA : ⁅L, A⁆ = L) (hodd : Odd (Nat.card (commutator (Outer ↥L)))) {w : G}
    (hw : w ∈ Subgroup.normalizer (L : Set G)) {a : G} (ha : a ∈ A) :
    ⁅w, a⁆ ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have hsq : a * a = 1 := by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [pow_two] at this
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hAN ha
  have hy : ⁅w, a⁆ ∈ Subgroup.normalizer (L : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hw haN) (inv_mem hw)) (inv_mem haN)
  have hinv : a * ⁅w, a⁆ * a⁻¹ = ⁅w, a⁆⁻¹ := JOut.inverted_commutator hsq w
  obtain ⟨m, hm, hym⟩ := JOut.exists_odd_pow_mem_of_commutator hodd hw haN
  obtain ⟨c, hco, hcK⟩ := JOut.exists_odd_order_pow_of_pow_mem hm hym
  refine hcK (JOut.mem_of_odd_primary_parts (P := fun z => ∃ d : ℕ, z = ⁅w, a⁆ ^ d)
    (fun z d ⟨c', hc'⟩ => ⟨c' * d, by rw [hc', ← pow_mul]⟩) ?_ (⁅w, a⁆ ^ c) ⟨c, rfl⟩ hco)
  rintro z r e hr hr2 ⟨d, rfl⟩ hord
  refine hS G W ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha _ (pow_mem hy d) ?_ r e hr hr2 hord
  rw [← conj_pow, hinv, inv_pow]

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
