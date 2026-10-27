module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup CFSG.Open

theorem two_dvd_card_sylow {K : Type*} [Group K] [Finite K] (hK : Even (Nat.card K))
    (S : Sylow 2 K) : 2 ∣ Nat.card S := by
  obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
  rcases a with _ | a
  · exfalso
    have h1 : Nat.card S = 1 := by simpa using ha
    have hbot : (S : Subgroup K) = ⊥ := Subgroup.card_eq_one.mp h1
    have hidx := S.not_dvd_index
    rw [hbot, Subgroup.index_bot] at hidx
    exact hidx (even_iff_two_dvd.mp hK)
  · rw [ha, pow_succ]
    exact dvd_mul_left 2 _

theorem card_eq_two_or_four_le {K : Type*} [Group K] [Finite K] (hK : Even (Nat.card K))
    (S : Sylow 2 K) : Nat.card S = 2 ∨ 4 ≤ Nat.card S := by
  obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
  have h2 := two_dvd_card_sylow hK S
  rcases a with _ | _ | a
  · exfalso
    rw [ha] at h2
    norm_num at h2
  · left
    simpa using ha
  · right
    rw [ha]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

structure Setting (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ) : Prop where
  std : StandardSetting G L
  hn : 8 ≤ n
  iso : Nonempty (L ≃* alternatingGroup (Fin n))
  cyc : ∃ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G)))
  bal : ∀ y : G, orderOf y = 2 → CFSG.oddCore (centralizer ({y} : Set G)) = ⊥

structure Cyc {G : Type} [Group G] [Finite G] (L : Subgroup G) (Q : Subgroup G) (z : G) :
    Prop where
  le : Q ≤ centralizer (L : Set G)
  pgroup : IsPGroup 2 Q
  odd_index : ¬ 2 ∣ Q.relIndex (centralizer (L : Set G))
  cyclic : IsCyclic Q
  order : orderOf z = 2
  mem : z ∈ Q

@[expose] def AltStdBalancedOrder2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → Nat.card S = 2 →
          (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) → False

@[expose] def AltStdBalancedBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → 4 ≤ Nat.card S →
          (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) → False

end CFSG.OddStandard.AltStdBal
