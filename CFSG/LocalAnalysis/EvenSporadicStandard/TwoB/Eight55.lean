module

public import CFSG.Sporadic.GLQ.BTwoRank

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic

theorem exists_isElemAbelian_eight_of_B {T : Type*} [Group T]
    [Finite T] (h : Nonempty (T ≃* Carrier .B)) :
    ∃ E : Subgroup T, CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨E, hE, hcard⟩, -⟩ := CFSG.Sporadic.GLQ.b_two_rank_at_least_five T h
  obtain ⟨hc, hp⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mp hE
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 3) (G := ↥E)
    (by rw [hcard]; norm_num)
  refine ⟨F.map E.subtype, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    have h := congrArg Subtype.val (hc.is_comm.comm a b)
    exact Subtype.ext h
  · rintro _ ⟨a, ha, rfl⟩
    exact hp a a.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hF]
    norm_num

theorem exists_isElemAbelian_eight_B :
    ∃ E : Subgroup (Carrier .B), CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 :=
  haveI : Finite (Carrier .B) := inferInstanceAs (Finite CFSG.Blueprint.NativeSporadic.B)
  exists_isElemAbelian_eight_of_B ⟨MulEquiv.refl _⟩

end CFSG.EvenSporadicStandard.TwoB
