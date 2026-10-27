module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LieType.Ree.LargeReeModelSchreier

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem mem_inner_of_sq_eq_one_of_odd {G : Type*} [Group G]
    (hodd : Odd (Nat.card (Outer G))) {α : MulAut G} (hα : α ^ 2 = 1) : α ∈ inner G := by
  have h2 : orderOf (α : Outer G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
  have hn : orderOf (α : Outer G) ∣ Nat.card (Outer G) := orderOf_dvd_natCard _
  have h1 : orderOf (α : Outer G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hn
      exact absurd (even_iff_two_dvd.2 hn) (Nat.not_even_iff_odd.2 hodd)
  rw [orderOf_eq_one_iff] at h1
  exact (QuotientGroup.eq_one_iff α).1 h1

theorem large_Ree_model_field_outer_group_and_inner_involutions (G : Type) [Group G] (p f : ℕ)
    (h : ReeTitsModel G .twistedF4 p f) :
    p = 2 ∧ 3 ≤ f ∧ Odd f ∧ IsCyclic (Outer G) ∧ Nat.card (Outer G) = f ∧
    (∀ α : MulAut G, α ^ 2 = 1 → α ∈ inner G) ∧
    ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime], f = 2 * a + 1 →
      Nat.card K = 2 ^ f →
      Nonempty (G ≃* DerivedCentralQuotient (reeFixedGroup .F4 K reeF4Perm
        fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))) →
      Nonempty (G ≃* F4.reeGamma K a) ∧
        ∀ (e : G ≃* F4.reeGamma K a) (α : MulAut G),
          ∃! q : F4.reeGamma K a × (K ≃+* K),
            MulAut.congr e α = MulAut.conj q.1 * F4.reeGammaFieldAut K a q.2 := by
  obtain ⟨-, -, -, hp, ⟨a, ha, hfa⟩, hiso⟩ := large_Ree_model_Schreier G p f h
  subst hp
  obtain ⟨-, a', hfa', K, _, _, hK, ⟨e₀⟩⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a' K hfa hK ⟨e₀⟩
  have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hfa]
  obtain ⟨-, -, -, hcyc, hcard, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form a' ha K hK'
  have EOut : Outer G ≃* Outer (F4.reeGamma K a') :=
    CFSG.ComponentClassification.OuterAutomorphisms.equivalence E
  have hcardG : Nat.card (Outer G) = f := by
    rw [Nat.card_congr EOut.toEquiv, hcard, hfa]
  have hoddf : Odd f := ⟨a', by omega⟩
  refine ⟨rfl, by omega, hoddf, isCyclic_of_surjective EOut.symm.toMonoidHom EOut.symm.surjective,
    hcardG, fun α hα => mem_inner_of_sq_eq_one_of_odd (hcardG ▸ hoddf) hα,
    fun b L _ _ _ hfb hL hw => ⟨hiso b L hfb hL hw, fun e α => ?_⟩⟩
  have hb : 1 ≤ b := by omega
  have hL' : Nat.card L = 2 ^ (2 * b + 1) := by rw [hL, hfb]
  exact (large_Ree_full_inner_field_automorphism_normal_form b hb L hL').2.1 (MulAut.congr e α)

end CFSG.ComponentClassification.UnbalancedCatalog
