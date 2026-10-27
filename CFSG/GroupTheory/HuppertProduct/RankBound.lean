module

public import CFSG.GroupTheory.HuppertProduct.Mho
public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.HuppertProduct.ProductIndex
import CFSG.GroupTheory.HuppertProduct.SmallQuotient
import CFSG.GroupTheory.HuppertProduct.PGroupMho
import CFSG.GroupTheory.HuppertProduct.PowerfulEmbedding
import CFSG.GroupTheory.HuppertProduct.CubeMap
import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

theorem le_relIndex_of_not_le [Finite G] {p : ℕ} [Fact p.Prime] {M E : Subgroup G}
    (hE : IsPGroup p E) (h : ¬ E ≤ M) : p ≤ M.relIndex E := by
  obtain ⟨n, hn⟩ := hE.index (M.subgroupOf E)
  have hrel : M.relIndex E = p ^ n := hn
  have hne : M.relIndex E ≠ 1 := fun h1 => h (Subgroup.relIndex_eq_one.1 h1)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact absurd (by rw [hrel, h0, pow_zero]) hne
  · rw [hrel]
    exact Nat.le_self_pow hpos.ne' p

theorem card_le_three_of_isCyclic [Finite G] {S F : Subgroup G} (hS : IsCyclic S) (hFS : F ≤ S)
    (hF : ∀ e ∈ F, e ^ 3 = 1) : Nat.card F ≤ 3 := by
  haveI : IsCyclic (F.subgroupOf S) := Subgroup.isCyclic _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F.subgroupOf S)
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have := hF (((g : S)) : G) (Subgroup.mem_subgroupOf.1 g.2)
    simpa using this
  have hcard : Nat.card (F.subgroupOf S) = orderOf g :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have h3 : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
  have hFS' : Nat.card F = Nat.card (F.subgroupOf S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFS).toEquiv.symm
  omega

theorem relIndex_mho_mho_le_nine [Finite G] {H : Subgroup G} (hH : IsPGroup 3 H)
    (h : (mho H 3).relIndex H ≤ 9) : (mho (mho H 3) 3).relIndex (mho H 3) ≤ 9 := by
  have hcomm : ⁅H, H⁆ ≤ mho H 3 := commutator_le_mho_of_relIndex_le (p := 3) (by simpa using h)
  exact (relIndex_mho_mho_le hcomm (commutator_mho_le_mho_mho hH hcomm)).trans h

theorem card_ne_twentySeven_of_relIndex_mho_le [Finite G] {H E : Subgroup G} (hH : IsPGroup 3 H)
    (hidx : (mho H 3).relIndex H ≤ 9) (hEH : E ≤ H) (hE3 : ∀ e ∈ E, e ^ 3 = 1) :
    Nat.card E ≠ 27 := by
  have main : ∀ n : ℕ, ∀ (H E : Subgroup G), Nat.card H = n → IsPGroup 3 H →
      (mho H 3).relIndex H ≤ 9 → E ≤ H → (∀ e ∈ E, e ^ 3 = 1) → Nat.card E ≠ 27 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H E hn hH hidx hEH hE3
      by_cases hbot : H = ⊥
      · subst hbot
        have hE : E = ⊥ := le_bot_iff.1 hEH
        subst hE
        simp
      have hMH : mho H 3 ≤ H := mho_le H 3
      have hMne : mho H 3 ≠ H := fun h => hbot (eq_bot_of_mho_eq_self hH h)
      have hcard : Nat.card (mho H 3) < n :=
        hn ▸ Subgroup.card_lt_of_lt (lt_of_le_of_ne hMH hMne)
      have hMp : IsPGroup 3 (mho H 3) := hH.to_le hMH
      have hMidx : (mho (mho H 3) 3).relIndex (mho H 3) ≤ 9 := relIndex_mho_mho_le_nine hH hidx
      by_cases hEM : E ≤ mho H 3
      · exact ih _ hcard (mho H 3) E rfl hMp hMidx hEM hE3
      · intro hE27
        have hcomm : ⁅H, H⁆ ≤ mho H 3 :=
          commutator_le_mho_of_relIndex_le (p := 3) (by simpa using hidx)
        have hpow := commutator_mho_le_mho_mho hH hcomm
        have hab : (mho (mho H 3) 3).relIndex (mho H 3) * (mho H 3).relIndex E ≤ 9 :=
          (relIndex_mul_le hcomm hpow hEH hE3).trans hidx
        have hb3 : 3 ≤ (mho H 3).relIndex E := le_relIndex_of_not_le (hH.to_le hEH) hEM
        have hbc : (mho H 3).relIndex E * Nat.card ((mho H 3 ⊓ E : Subgroup G)) = Nat.card E :=
          Subgroup.relIndex_mul_card _ _
        have ha1 : 0 < (mho (mho H 3) 3).relIndex (mho H 3) :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        have ha3 : (mho (mho H 3) 3).relIndex (mho H 3) ≤ 3 := by nlinarith
        have hMcyc : IsCyclic (mho H 3) := isCyclic_of_relIndex_mho_le hMp ha3
        have hc3 : Nat.card ((mho H 3 ⊓ E : Subgroup G)) ≤ 3 :=
          card_le_three_of_isCyclic hMcyc inf_le_left (fun e he => hE3 e he.2)
        rw [hE27] at hbc
        have hb9 : 9 ≤ (mho H 3).relIndex E := by nlinarith
        have ha_eq : (mho (mho H 3) 3).relIndex (mho H 3) = 1 := by nlinarith
        have hMbot : mho H 3 = ⊥ :=
          eq_bot_of_mho_eq_self hMp
            (le_antisymm (mho_le _ 3) (Subgroup.relIndex_eq_one.1 ha_eq))
        have hc1 : Nat.card ((mho H 3 ⊓ E : Subgroup G)) = 1 := by
          rw [hMbot, bot_inf_eq]
          exact Subgroup.card_bot
        rw [hc1, mul_one] at hbc
        rw [ha_eq] at hab
        omega
  exact main _ H E rfl hH hidx hEH hE3

theorem card_ne_twentySeven_of_product [Finite G] {W A B E : Subgroup G} (hW : IsPGroup 3 W)
    (hA : A ≤ W) (hB : B ≤ W) (hAc : IsCyclic A) (hBc : IsCyclic B)
    (hprod : ∀ w ∈ W, ∃ a ∈ A, ∃ b ∈ B, w = a * b) (hEW : E ≤ W) (hE3 : ∀ e ∈ E, e ^ 3 = 1) :
    Nat.card E ≠ 27 :=
  card_ne_twentySeven_of_relIndex_mho_le hW
    ((relIndex_mho_le_of_mul_cyclic (p := 3) (by norm_num) hA hB hAc hBc hprod).trans
      (by norm_num)) hEW hE3

theorem kFactHuppertProductThree_holds :
    ∀ (G : Type) [Group G] [Finite G] (W A B E : Subgroup G), IsPGroup 3 W → A ≤ W → B ≤ W →
      IsCyclic A → IsCyclic B → (∀ w ∈ W, ∃ a ∈ A, ∃ b ∈ B, w = a * b) →
      E ≤ W → (IsMulCommutative E ∧ ∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≠ 27 :=
  fun _ _ _ _ _ _ _ hW hA hB hAc hBc hprod hEW hE =>
    card_ne_twentySeven_of_product hW hA hB hAc hBc hprod hEW hE.2

end CFSG.GroupTheory.HuppertProduct
