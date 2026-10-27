module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.FourthPowerFacts

public section

namespace CFSG.EvenSporadicStandard.TwoRu

open Subgroup

theorem injective_of_ker_zpowers {L J Y : Type*} [Group L] [Finite L] [Group J] [Group Y]
    [IsSimpleGroup J] [Group.IsPerfect L] {q : L →* J} (hq : Function.Surjective q) {t : L}
    (ht : orderOf t = 2) (hker : q.ker = zpowers t) (ψ : L →* Y) (hψ : ψ t ≠ 1) :
    Function.Injective ψ := by
  have : Finite J := Finite.of_surjective q hq
  have hNq : ψ.ker ⊓ q.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxψ, hxq⟩ := mem_inf.1 hx
    rw [hker] at hxq
    rcases eq_one_or_eq_of_mem_zpowers ht hxq with h1 | h1
    · exact h1 ▸ one_mem _
    · exact absurd (h1 ▸ (MonoidHom.mem_ker.1 hxψ)) hψ
  rw [← MonoidHom.ker_eq_bot_iff]
  have hnorm : (ψ.ker.map q).Normal := Subgroup.Normal.map inferInstance q hq
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.ker.map q) with h0 | htop
  · have hle : ψ.ker ≤ q.ker := fun x hx => by
      have : q x ∈ ψ.ker.map q := ⟨x, hx, rfl⟩
      rw [h0, mem_bot] at this
      exact this
    rw [← hNq]
    exact (inf_eq_left.2 hle).symm
  · exfalso
    have hinj : Function.Injective (q.comp ψ.ker.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hxq : (x : L) ∈ q.ker := hx
      have : (x : L) ∈ ψ.ker ⊓ q.ker := mem_inf.2 ⟨x.2, hxq⟩
      rw [hNq, mem_bot] at this
      exact Subtype.ext this
    have hsurj : Function.Surjective (q.comp ψ.ker.subtype) := by
      intro j
      have : j ∈ ψ.ker.map q := by rw [htop]; trivial
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨⟨x, hx⟩, rfl⟩
    have hcardN : Nat.card ψ.ker = Nat.card J :=
      Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
    have hcardL : Nat.card L = Nat.card J * 2 := by
      rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hq).toEquiv, hker,
        Nat.card_zpowers, ht]
    have hidx : ψ.ker.index = 2 := by
      have h1 := ψ.ker.index_mul_card
      rw [hcardN, hcardL] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [mul_comm] at h1; exact h1)
    exact not_isPerfect_of_index_eq_two hidx ‹_›

end CFSG.EvenSporadicStandard.TwoRu
