module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t τ ρ : G} {L : Subgroup G}

theorem card_closure_pair (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hτ2 : τ ^ 2 = 1)
    (htτ : t * τ = τ * t) (hτt : τ ∉ zpowers t) : Nat.card ↥(closure ({t, τ} : Set G)) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ1 : τ ≠ 1 := fun h => hτt (h ▸ Subgroup.one_mem (zpowers t))
  have hcl : closure ({t, τ} : Set G) = zpowers t ⊔ zpowers τ := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ zpowers τ, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_zpowers_iff] at ha hb
    obtain ⟨m, rfl⟩ := ha
    obtain ⟨n, rfl⟩ := hb
    exact Commute.zpow_zpow htτ m n
  have hcardt : Nat.card ↥(zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ht2 ht1
  have hcardτ : Nat.card ↥(zpowers τ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hτ2 hτ1
  have hinf : zpowers t ⊓ zpowers τ = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(zpowers t ⊓ zpowers τ) ∣ 2 := by
      rw [← hcardτ]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact hne ((Subgroup.card_eq_one).mp h1)
    · have heq : (zpowers t ⊓ zpowers τ) = zpowers τ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hcardτ])
      have hle : zpowers τ ≤ zpowers t := by
        rw [← heq]
        exact inf_le_left
      exact hτt (hle (Subgroup.mem_zpowers τ))
  have hprod := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers t) (zpowers τ) hcomm
  rw [hcl]
  have h := hprod.1
  rw [hcardt, hcardτ, hinf] at h
  simpa using h

theorem card_eq_of_isSylowIn {K T : Subgroup G} (hT : IsSylowIn 2 T K) :
    Nat.card T = 2 ^ (Nat.card K).factorization 2 := by
  obtain ⟨hle, hp, hndvd⟩ := hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥T)).mp hp
  haveI : Nonempty ↥T := ⟨⟨1, T.one_mem⟩⟩
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  have hrel : T.relIndex K * Nat.card ↥T = Nat.card ↥K := by
    have h := Subgroup.relIndex_mul_card T K
    rwa [inf_of_le_left hle] at h
  have hrelne : T.relIndex K ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    have : 0 < Nat.card ↥K := Nat.card_pos
    omega
  have hTne : Nat.card ↥T ≠ 0 := (Nat.card_pos (α := ↥T)).ne'
  have hfac : (Nat.card ↥K).factorization 2 = n := by
    rw [← hrel, Nat.factorization_mul hrelne hTne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd, zero_add]
    rw [hn]
    exact Nat.factorization_pow_self Nat.prime_two
  rw [hfac]
  exact hn

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
