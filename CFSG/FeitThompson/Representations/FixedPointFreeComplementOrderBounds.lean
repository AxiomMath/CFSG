module
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.SemidirectProduct

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open MulAction

variable {H E : Type*} [Group H] [Group E] {φ : E →* MulAut H}

theorem card_dvd_card_sub_one_of_fixedPointFree [Finite H]
    (hφ : ∀ u : E, u ≠ 1 → MonoidHom.FixedPointFree (φ u : H → H)) :
    Nat.card E ∣ Nat.card H - 1 := by
  let _ : MulDistribMulAction E H := MulDistribMulAction.compHom H φ
  let S : SubMulAction E H :=
    { carrier := {1}ᶜ
      smul_mem' := fun u _ hx hx1 => hx (smul_left_cancel u (by rw [hx1, smul_one])) }
  have hmem : ∀ x : S, (x : H) ≠ 1 := fun x => x.2
  have hst : ∀ x : S, stabilizer E x = ⊥ := by
    intro x
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    by_contra hu1
    have h : (u • (x : H)) = x := congrArg Subtype.val (mem_stabilizer_iff.1 hu)
    exact hmem x (hφ u hu1 x.1 h)
  have h1 : Nat.card S = Nat.card (Quotient (orbitRel E S)) * Nat.card E := by
    rw [Nat.card_congr (selfEquivOrbitsQuotientProd hst), Nat.card_prod]
  have h2 : Nat.card S = Nat.card H - 1 := by
    classical
    have : Fintype H := Fintype.ofFinite H
    have h3 : Nat.card S = Nat.card {x : H // ¬ x = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
    rw [h3, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (p := fun x : H => x = 1)]
    simp
  exact ⟨_, by rw [← h2, h1, Nat.mul_comm]⟩

theorem coprime_card_of_fixedPointFree [Finite H] [Nontrivial H]
    (hφ : ∀ u : E, u ≠ 1 → MonoidHom.FixedPointFree (φ u : H → H)) :
    Nat.Coprime (Nat.card H) (Nat.card E) := by
  have h1 : 1 < Nat.card H := Finite.one_lt_card_iff_nontrivial.2 ‹_›
  have hco : Nat.Coprime (Nat.card H) (Nat.card H - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card H = m + 1 := ⟨Nat.card H - 1, by omega⟩
    simp [hm, Nat.Coprime]
  exact hco.coprime_dvd_right (card_dvd_card_sub_one_of_fixedPointFree hφ)

theorem one_lt_card_of_odd_card_semidirectProduct [Nontrivial E]
    (hodd : Odd (Nat.card (H ⋊[φ] E))) : 1 < Nat.card E := by
  rw [SemidirectProduct.card] at hodd
  have hE : Odd (Nat.card E) := Nat.Odd.of_mul_right hodd
  have hne : Nat.card E ≠ 0 := by
    rintro h
    rw [h] at hE
    simp at hE
  have : Finite E := Nat.finite_of_card_ne_zero hne
  exact Finite.one_lt_card_iff_nontrivial.2 ‹_›

theorem two_mul_card_le_card_sub_one_of_fixedPointFree [Finite H] [Nontrivial H]
    (hφ : ∀ u : E, u ≠ 1 → MonoidHom.FixedPointFree (φ u : H → H))
    (hodd : Odd (Nat.card (H ⋊[φ] E))) :
    2 * Nat.card E ≤ Nat.card H - 1 := by
  rw [SemidirectProduct.card] at hodd
  obtain ⟨hH, hE⟩ := Nat.odd_mul.1 hodd
  obtain ⟨k, hk⟩ := card_dvd_card_sub_one_of_fixedPointFree hφ
  have h1 : 1 < Nat.card H := Finite.one_lt_card_iff_nontrivial.2 ‹_›
  have hev : Even (Nat.card H - 1) := Nat.Odd.sub_odd hH odd_one
  have hk2 : 2 ≤ k := by
    rcases Nat.even_mul.1 (hk ▸ hev) with h | h
    · exact absurd h (Nat.not_even_iff_odd.2 hE)
    · rcases Nat.eq_zero_or_pos k with rfl | hpos
      · omega
      · obtain ⟨m, rfl⟩ := h
        omega
  calc 2 * Nat.card E = Nat.card E * 2 := Nat.mul_comm _ _
    _ ≤ Nat.card E * k := Nat.mul_le_mul_left _ hk2
    _ = Nat.card H - 1 := hk.symm

end CFSG.FeitThompson
