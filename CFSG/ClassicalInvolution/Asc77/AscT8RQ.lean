module

public import CFSG.ClassicalInvolution.Asc77.AscT8RVL

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3

namespace T8R

section Group

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_sylow_of_le_centralizer (S : Sylow 2 G) {a : G}
    (haS : ∀ s ∈ (S : Subgroup G), s * a = a * s) {n : G} {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hQC : ∀ y ∈ Q, y * (n * a * n⁻¹) = (n * a * n⁻¹) * y) :
    ∃ n' : G, n' * a * n'⁻¹ = n * a * n⁻¹ ∧ Q ≤ conjSub n' (S : Subgroup G) := by
  set c : G := n * a * n⁻¹ with hc
  have hPC : conjSub n (S : Subgroup G) ≤ Subgroup.centralizer ({c} : Set G) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := haS _ hy
    calc y * c = n * ((n⁻¹ * y * n) * a) * n⁻¹ := by rw [hc]; group
      _ = n * (a * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
      _ = c * y := by rw [hc]; group
  have hPs := isSylow2In_conjSub_sylow S n hPC
  have hQC' : Q ≤ Subgroup.centralizer ({c} : Set G) := fun y hy => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hQC y hy
  obtain ⟨V, hV, hQV⟩ := IsSylow2In.exists_ge hQ hQC'
  obtain ⟨c₂, hc₂, hc₂V⟩ := Thompson.exists_conj_of_isSylow2In hPs hV
  have hc₂c : c₂ * c = c * c₂ := Subgroup.mem_centralizer_singleton_iff.mp hc₂
  refine ⟨c₂ * n, ?_, ?_⟩
  · calc c₂ * n * a * (c₂ * n)⁻¹ = c₂ * (n * a * n⁻¹) * c₂⁻¹ := by group
      _ = c₂ * c * c₂⁻¹ := by rw [hc]
      _ = c := by rw [hc₂c]; group
  · rw [conjSub_mul, hc₂V]
    exact hQV

theorem exists_orderOf_four_of_swap {R : Subgroup G} {z : G} (hz : IsUniqueInvolution R z)
    (hR2 : IsPGroup 2 ↥R) (h8 : 8 ≤ Nat.card ↥R) (N : Subgroup G) (hNR : N ≤ R)
    (hprod : ∀ x ∈ R, ∀ y ∈ R, x ∉ N → y ∉ N → x * y ∈ N) : ∃ x ∈ N, orderOf x = 4 := by
  by_cases hN : N = R
  · obtain ⟨x, hx, hxo⟩ := exists_orderOf_four_of_four_le hz le_rfl hR2 (by omega)
    exact ⟨x, hN ▸ hx, hxo⟩
  · have hex : ∃ a ∈ R, a ∉ N := by
      by_contra hcon
      push Not at hcon
      exact hN (le_antisymm hNR hcon)
    obtain ⟨a, haR, haN⟩ := hex
    have hle : Nat.card ↥R ≤ 2 * Nat.card ↥N := by
      classical
      let f : ↥R → ↥N ⊕ ↥N := fun r =>
        if h : (r : G) ∈ N then Sum.inl ⟨r, h⟩ else
          Sum.inr ⟨a⁻¹ * r, hprod a⁻¹ (R.inv_mem haR) r r.2
            (fun h' => haN (by simpa using N.inv_mem h')) (fun h' => h h')⟩
      have hf : Function.Injective f := by
        intro r s hrs
        by_cases hr : (r : G) ∈ N <;> by_cases hs : (s : G) ∈ N
        · simp only [f, hr, hs, dite_true] at hrs
          exact Subtype.ext (congrArg Subtype.val (Sum.inl.inj hrs)).symm.symm
        · simp only [f, hr, hs, dite_true, dite_false] at hrs
          exact absurd hrs (by simp)
        · simp only [f, hr, hs, dite_true, dite_false] at hrs
          exact absurd hrs (by simp)
        · simp only [f, hr, hs, dite_false] at hrs
          have := congrArg Subtype.val (Sum.inr.inj hrs)
          exact Subtype.ext (mul_left_cancel this)
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_sum, ← two_mul] at this
    have h4 : 4 ≤ Nat.card ↥N := by omega
    exact exists_orderOf_four_of_four_le hz hNR (hR2.to_le hNR) h4

end Group

end T8R

end CFSG.ClassicalInvolution.Asc77
