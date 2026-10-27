module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.GroupTheory

open Subgroup

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_cartan_complement (N P : Subgroup Y) [N.Normal] (hPn : P.Normal)
    (hP2 : IsPGroup 2 P) (hPodd : Odd P.index) :
    ∃ C : Subgroup Y, N ≤ C ∧ Odd (N.relIndex C) ∧ ∃ k : ℕ, C.index = 2 ^ k := by
  have hφ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  haveI : (P.map (QuotientGroup.mk' N)).Normal := hPn.map _ hφ
  obtain ⟨k, hk⟩ := (hP2.map (QuotientGroup.mk' N)).exists_card_eq
  have hodd : Odd (P.map (QuotientGroup.mk' N)).index := hPodd.of_dvd_nat (index_map_dvd P hφ)
  obtain ⟨K, hK⟩ := exists_right_complement'_of_coprime (N := P.map (QuotientGroup.mk' N))
    (by rw [hk]; exact (Nat.coprime_two_left.2 hodd).pow_left k)
  refine ⟨K.comap (QuotientGroup.mk' N), (QuotientGroup.ker_mk' N).symm.trans_le
    (MonoidHom.ker_le_comap _ K), ?_, k, ?_⟩
  · have h := relIndex_comap (⊥ : Subgroup (Y ⧸ N)) (QuotientGroup.mk' N)
      (K.comap (QuotientGroup.mk' N))
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', map_comap_eq_self_of_surjective hφ,
      relIndex_bot_left] at h
    rw [h, show Nat.card K = _ from hK.card_right]
    exact hodd
  · rw [index_comap_of_surjective K hφ, hK.index_eq_card, hk]

end CFSG.GroupTheory
