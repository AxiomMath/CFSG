module

public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaABase
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaAStep

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

universe u

private theorem exists_index_two_card_centralizer_ge_sixteen_aux :
    ∀ n : ℕ, ∀ (T : Type u) [Group T] [Finite T],
    Nat.card T = n → IsPGroup 2 T → 16 ≤ Nat.card T →
    ∀ {s : T}, s * s = 1 → s ≠ 1 → s ∉ center T →
    (∀ a ∈ centralizer ({s} : Set T), ∀ b ∈ centralizer ({s} : Set T), a * b = b * a) →
    Nat.card (centralizer ({s} : Set T)) ≤ 8 →
    ∃ M : Subgroup T, M.index = 2 ∧ ∀ u ∈ M, u * u = 1 → u ≠ 1 →
      16 ≤ Nat.card (centralizer ({u} : Set T)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro T _ _ hcard hT h16 s hs hs1 hsz hab h8
    by_cases hcard16 : Nat.card T = 16
    · obtain ⟨M, hMindex, hMcent⟩ :=
        exists_index_two_involutions_central_of_card_sixteen hcard16 hs hsz hab h8
      refine ⟨M, hMindex, ?_⟩
      intro u hu hu2 _
      have hucent : u ∈ center T := hMcent u hu hu2
      have htop : centralizer ({u} : Set T) = ⊤ :=
        Subgroup.centralizer_eq_top_iff_subset.mpr (by rintro x rfl; exact hucent)
      rw [htop, Subgroup.card_top, hcard16]
    · haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
      obtain ⟨k, hk⟩ := hT.exists_card_eq
      have hk4 : 4 ≤ k := by
        have h : 2 ^ 4 ≤ 2 ^ k := by
          rw [← hk]
          norm_num
          exact h16
        exact (Nat.pow_le_pow_iff_right (show (1 : ℕ) < 2 by norm_num)).1 h
      have hkne4 : k ≠ 4 := by
        intro hk_eq
        exact hcard16 (by rw [hk, hk_eq]; norm_num)
      have hk5 : 5 ≤ k := by omega
      have h32 : 32 ≤ Nat.card T := by
        rw [hk]
        calc (32 : ℕ) = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ k := (Nat.pow_le_pow_iff_right (show (1 : ℕ) < 2 by norm_num)).2 hk5
      haveI : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨z, hz_center, hz_order⟩ := exists_mem_center_orderOf_eq_two hT
      have hz2 : z * z = 1 := by
        rw [← pow_two, ← hz_order]
        exact pow_orderOf_eq_one z
      have hz1 : z ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hz_order
        norm_num at hz_order
      haveI : (zpowers z).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le_of_mem hz_center)
      have hcardR : Nat.card (T ⧸ zpowers z) * 2 = Nat.card T :=
        card_quotient_zpowers (z := z) hz2 hz1
      have hR16 : 16 ≤ Nat.card (T ⧸ zpowers z) := by omega
      have hRlt : Nat.card (T ⧸ zpowers z) < n := by
        rw [← hcard]
        omega
      have hs_ne : s ≠ z := by
        rintro rfl
        exact hsz hz_center
      have hs' : (QuotientGroup.mk s : T ⧸ zpowers z) * QuotientGroup.mk s = 1 := by
        rw [← QuotientGroup.mk_mul, hs, QuotientGroup.mk_one]
      have hs1' : (QuotientGroup.mk s : T ⧸ zpowers z) ≠ 1 :=
        mk_ne_one_of_ne (z := z) hz2 hs1 hs_ne
      have hsz' : (QuotientGroup.mk s : T ⧸ zpowers z) ∉ center (T ⧸ zpowers z) :=
        mk_notMem_center (z := z) h32 hz2 hz1 h8
      have hab' : ∀ a ∈ centralizer ({(QuotientGroup.mk s : T ⧸ zpowers z)} :
            Set (T ⧸ zpowers z)),
          ∀ b ∈ centralizer ({(QuotientGroup.mk s : T ⧸ zpowers z)} :
            Set (T ⧸ zpowers z)), a * b = b * a :=
        mk_centralizer_comm (z := z) hT h32 hz2 hz1 hs hs1 hsz h8
      have h8' : Nat.card (centralizer ({(QuotientGroup.mk s : T ⧸ zpowers z)} :
            Set (T ⧸ zpowers z))) ≤ 8 :=
        (card_centralizer_quotient_le (zpowers z) s).trans h8
      obtain ⟨M, hMindex, hMcent⟩ :=
        ih (Nat.card (T ⧸ zpowers z)) hRlt (T ⧸ zpowers z) rfl
          (hT.to_quotient (zpowers z)) hR16 hs' hs1' hsz' hab' h8'
      exact lift_index_two (z := z) hz_center hz2 hz1 h16 hMindex hMcent

theorem exists_index_two_card_centralizer_ge_sixteen {T : Type*} [Group T] [Finite T]
    (hT : IsPGroup 2 T) (h16 : 16 ≤ Nat.card T) {s : T} (hs : s * s = 1) (hs1 : s ≠ 1)
    (hsz : s ∉ center T)
    (hab : ∀ a ∈ centralizer ({s} : Set T), ∀ b ∈ centralizer ({s} : Set T), a * b = b * a)
    (h8 : Nat.card (centralizer ({s} : Set T)) ≤ 8) :
    ∃ M : Subgroup T, M.index = 2 ∧ ∀ u ∈ M, u * u = 1 → u ≠ 1 →
      16 ≤ Nat.card (centralizer ({u} : Set T)) :=
  exists_index_two_card_centralizer_ge_sixteen_aux (Nat.card T) T rfl hT h16 hs hs1 hsz hab h8

end CFSG.GroupTheory.SmallFixedTwoGroup
