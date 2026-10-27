module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private instance a6cKleinProd : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  inferInstanceAs (IsKleinFour (Multiplicative (ZMod 2 × ZMod 2)))

theorem a6c_relIndex_or_klein {G Γ : Type} [Group G] [Finite G] [Group Γ] (R C : Subgroup G)
    (ψ : ↥R →* Γ) (hR2 : IsPGroup 2 ↥R) (hker : ψ.ker = C.subgroupOf R)
    (hle : Nat.card ψ.range ≤ 4) (hexp : ∀ c ∈ ψ.range, c * c = 1) :
    C.relIndex R ≤ 2 ∨
      QuotEquivTo R (R ⊓ C) (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : C.relIndex R = Nat.card ψ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hrange2 : IsPGroup 2 ψ.range :=
    hR2.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hrange2.exists_card_eq
  by_cases h4 : Nat.card ψ.range = 4
  · right
    haveI : Nontrivial ψ.range := by
      rw [← Finite.one_lt_card_iff_nontrivial, h4]
      norm_num
    haveI : IsKleinFour ψ.range := by
      refine ⟨h4, ?_⟩
      rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
      intro g hg
      exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (hexp g g.2)) hg
    obtain ⟨iso⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ψ.range)
      (G₂ := Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    have hsub : (R ⊓ C).subgroupOf R = ψ.ker := by
      rw [hker, inf_comm, Subgroup.inf_subgroupOf_right]
    refine ⟨(iso : ψ.range →* _).comp ψ.rangeRestrict,
      iso.surjective.comp ψ.rangeRestrict_surjective, ?_⟩
    rw [hsub]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact (map_eq_one_iff iso iso.injective).trans
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · left
    rw [hidx]
    have hk3 : k < 3 := by
      by_contra h
      have h8 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp h)
      omega
    interval_cases k <;> omega

end CFSG.OddStandard.SmallF3.Omega
