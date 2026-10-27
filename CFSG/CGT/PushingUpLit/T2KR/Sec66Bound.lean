module

public import CFSG.CGT.PushingUpLit.T2KR.GenFourMod

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

variable {G : Type} [Group G] [Finite G]

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem relIndex_Q_le {S : Subgroup G} (hSM : S ≤ M) (hS : IsPGroup 2 S) :
    (S ⊓ QM L M).relIndex S ≤ n * 2 ^ n := by
  classical
  set N : Subgroup G := S ⊓ (L ⊔ QM L M) with hNdef
  have hNS : N ≤ S := inf_le_left
  have hNLQ : N ≤ L ⊔ QM L M := inf_le_right
  have hN2 : IsPGroup 2 N := hS.to_le hNS
  have hQN : N ⊓ QM L M = S ⊓ QM L M := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxS, _⟩, hxQ⟩
      exact ⟨hxS, hxQ⟩
    · rintro ⟨hxS, hxQ⟩
      exact ⟨⟨hxS, (le_sup_right : QM L M ≤ L ⊔ QM L M) hxQ⟩, hxQ⟩
  have hidx : N.relIndex S ≤ n := H.relIndex_le_card_aut hSM hS
  obtain ⟨p, hp⟩ := H.exists_root_point_of_isPGroup N hNLQ hN2
  have hF : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n H.n_ne_zero
  have hroot : Nat.card (rootGrp p) = 2 ^ n := by rw [card_rootGrp, hF]
  have hrange : Nat.card (H.rhoOn N hNLQ).range ≤ 2 ^ n :=
    (Subgroup.card_le_of_le hp).trans (le_of_eq hroot)
  have hrel : (N ⊓ QM L M).relIndex N ≤ 2 ^ n := by
    rw [H.relIndex_eq_card_range N hNLQ]
    exact hrange
  rw [hQN] at hrel
  have hle : S ⊓ QM L M ≤ N := by
    rw [← hQN]
    exact inf_le_left
  calc (S ⊓ QM L M).relIndex S = (S ⊓ QM L M).relIndex N * N.relIndex S :=
        (Subgroup.relIndex_mul_relIndex _ _ _ hle hNS).symm
    _ ≤ 2 ^ n * n := Nat.mul_le_mul hrel hidx
    _ = n * 2 ^ n := mul_comm _ _

end MData

end CFSG.CGT.PushingUpLit.T2KR
