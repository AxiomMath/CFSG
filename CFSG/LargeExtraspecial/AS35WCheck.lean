module

public import CFSG.LargeExtraspecial.AS35WBasic
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35W

variable {M : Type} [Group M]

theorem card_centralizer_subtype {H : Subgroup M} {d : M} (hd : d ∈ H) :
    Nat.card (centralizer ({(⟨d, hd⟩ : H)} : Set H)) =
      Nat.card (H ⊓ centralizer ({d} : Set M) : Subgroup M) := by
  have heq : (centralizer ({(⟨d, hd⟩ : H)} : Set H)).map H.subtype =
      H ⊓ centralizer ({d} : Set M) := by
    ext g
    simp only [mem_map, mem_centralizer_singleton_iff, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hgH, hg⟩
      exact ⟨⟨g, hgH⟩, Subtype.ext hg, rfl⟩
  rw [← heq, Subgroup.card_map_of_injective H.subtype_injective]

variable [DecidableEq M]

theorem W2Data.false_of_check {H : Subgroup M} {d : M} {hd : d ∈ H}
    (hz : W2Data H ⟨d, hd⟩) {KL UL : List M}
    (hK : ∀ g, g ∈ KL ↔ g ∈ H ∧ g * d = d * g) {k : ℕ}
    (hc : CFSG.ClassicalInvolution.twoConstrainedCheck KL UL k = true) {x c : M}
    (hxU : x ∈ UL) (hxd : x ≠ d) (hcH : c ∈ H) (hcx : c * d * c⁻¹ = x) : False := by
  simp only [CFSG.ClassicalInvolution.twoConstrainedCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, hmul⟩, hinv⟩, hUK⟩, hpow⟩, hnorm⟩, -⟩ := hc
  have hmul' : ∀ a ∈ UL, ∀ b ∈ UL, a * b ∈ UL := fun a ha b hb => by
    simpa using hmul a ha b hb
  have hUH : ∀ u ∈ UL, u ∈ H := fun u hu => ((hK u).1 (hUK u hu)).1
  set U := CFSG.ClassicalInvolution.subgroupOfList UL h1 hmul' hinv
  set P : Subgroup H := U.comap H.subtype
  have hxH : x ∈ H := hUH x hxU
  refine hz.false_of_conj_mem (P := P) (x := ⟨x, hxH⟩) ?_ ?_ ?_ hxU ?_ ?_
  · intro u hu
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext ((hK _).1 (hUK _ hu)).2
  · intro g hg u hu
    have hg' : (g : M) ∈ KL := (hK _).2 ⟨g.2,
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg)⟩
    show (g : M) * u * (g : M)⁻¹ ∈ UL
    simpa using hnorm _ hg' _ hu
  · intro u
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hpow _ u.2))⟩
  · intro h
    exact hxd (congrArg Subtype.val h)
  · exact isConj_iff.2 ⟨⟨c, hcH⟩, Subtype.ext hcx⟩

end AS35W

end CFSG.LargeExtraspecial
