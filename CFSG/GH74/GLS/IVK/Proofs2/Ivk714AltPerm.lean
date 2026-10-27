module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.IVK.GHInv
open scoped Nat

section PermInv

variable {n : ℕ}

theorem involution_cycleType_replicate {σ : Perm (Fin n)} (h : σ * σ = 1) :
    ∃ k : ℕ, σ.cycleType = Multiset.replicate k 2 :=
  ⟨_, Equiv.Perm.cycleType_of_pow_prime_eq_one (by rw [sq]; exact h)⟩

theorem involution_support_sign {σ : Perm (Fin n)} {k : ℕ} (h : σ * σ = 1)
    (hk : σ.cycleType = Multiset.replicate k 2) :
    σ.support.card = 2 * k ∧ sign σ = (-1) ^ k := by
  obtain ⟨h1, h2⟩ := involution_cycle_data h
  have hc : σ.cycleType.card = k := by rw [hk, Multiset.card_replicate]
  rw [hc] at h1 h2
  exact ⟨h1, h2⟩

theorem card_centralizer_involution_perm {σ : Perm (Fin n)} {k : ℕ}
    (hk : σ.cycleType = Multiset.replicate k 2) (hk1 : 1 ≤ k) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) = (n - 2 * k)! * 2 ^ k * k ! := by
  have hk0 : ¬ k = 0 := by omega
  rw [Equiv.Perm.nat_card_centralizer, hk, Multiset.sum_replicate, Multiset.prod_replicate]
  simp only [Multiset.toFinset_replicate, hk0, ↓reduceIte, Finset.prod_singleton,
    Multiset.count_replicate_self, Fintype.card_fin, smul_eq_mul, mul_comm k 2]

theorem seven_le_sub {n k : ℕ} (hn : n ≤ 11) (hk : 2 * k ≤ n)
    (h7 : 7 ∣ (n - 2 * k)! * 2 ^ k * k !) : 7 ≤ n - 2 * k := by
  have hp : Nat.Prime 7 := by decide
  rcases (Nat.Prime.dvd_mul hp).1 h7 with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact (Nat.Prime.dvd_factorial hp).1 h
    · have := Nat.Prime.dvd_of_dvd_pow hp h
      omega
  · have := (Nat.Prime.dvd_factorial hp).1 h
    omega

theorem altOn_support_compl_le (σ : Perm (Fin n)) :
    altOn σ.supportᶜ ≤ centralizer ({σ} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) := by
  intro g hg
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, altOn_le_alternatingGroup _ hg⟩
  exact commute_of_symOn_of_fixes (altOn_le_symOn _ hg) (fun x hx => by
    simpa [Equiv.Perm.mem_support] using hx)

theorem card_altOn_support_compl {σ : Perm (Fin n)} {k : ℕ} (h : σ * σ = 1)
    (hk : σ.cycleType = Multiset.replicate k 2) (h2 : 2 ≤ n - 2 * k) :
    Nat.card (altOn σ.supportᶜ) = (n - 2 * k)! / 2 := by
  have hs := (involution_support_sign h hk).1
  have : Nontrivial ↥σ.supportᶜ := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe, Finset.card_compl,
      Fintype.card_fin, hs]
    omega
  rw [← Nat.card_congr (altOnEquiv σ.supportᶜ).toEquiv, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs]

theorem eq_altOn_of_perfect {σ : Perm (Fin n)} {k : ℕ} (hσ : σ * σ = 1)
    (hk : σ.cycleType = Multiset.replicate k 2) (hk4 : k ≤ 4) (h5 : 5 ≤ n - 2 * k)
    {P : Subgroup (Perm (Fin n))} (hP : Group.IsPerfect P) (hPA : P ≤ alternatingGroup (Fin n))
    (hPc : ∀ x ∈ P, x * σ = σ * x) (hPn : ∀ g ∈ altOn σ.supportᶜ, ∀ x ∈ P, g * x * g⁻¹ ∈ P)
    (hP1 : P ≠ ⊥) : P = altOn σ.supportᶜ := by
  have hcard : σ.cycleType.card = k := by rw [hk, Multiset.card_replicate]
  have hs := (involution_support_sign hσ hk).1
  have hF5 : 5 ≤ (σ.supportᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin, hs]
    exact h5
  have hle : P ≤ altOn σ.supportᶜ := by
    intro x hx
    refine mem_altOn.2 ⟨fun a ha => ?_, Equiv.Perm.mem_alternatingGroup.1 (hPA hx)⟩
    have hσa : σ a ≠ a := by
      have : a ∈ σ.support := by simpa using ha
      exact Equiv.Perm.mem_support.1 this
    exact perfect_fixes_support hσ (hcard ▸ hk4) hP hPc x hx a hσa
  have : IsSimpleGroup (altOn σ.supportᶜ) := isSimpleGroup_altOn hF5
  have hnorm : (P.subgroupOf (altOn σ.supportᶜ)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    exact hPn g.1 g.2 x.1 hx
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf (altOn σ.supportᶜ)) with hbot | htop
  · exfalso
    apply hP1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : ↥(altOn σ.supportᶜ)) ∈ P.subgroupOf (altOn σ.supportᶜ) := hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · refine le_antisymm hle (fun g hg => ?_)
    have : (⟨g, hg⟩ : ↥(altOn σ.supportᶜ)) ∈ P.subgroupOf (altOn σ.supportᶜ) := by
      rw [htop]
      trivial
    exact this

end PermInv

end CFSG.GH74.GLS.IVK.Proofs2
