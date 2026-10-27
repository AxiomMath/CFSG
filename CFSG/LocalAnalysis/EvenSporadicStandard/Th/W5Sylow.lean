module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Card

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B : Subgroup G} {z : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z)

include H W

theorem ThCyc.natCard_Bp_eq : Nat.card (Bp A t) = 2 ^ 14 := by
  rw [H.natCard_Bp W, W.B_card, W.A_card]
  norm_num

theorem ThCyc.isPGroup_Bp : IsPGroup 2 (Bp A t) :=
  IsPGroup.of_card (by rw [H.natCard_Bp_eq W])

theorem ThCyc.Bp_normal {r : G} (hr : r ∈ normalizer ((W5 A t : Subgroup G) : Set G)) {b : G}
    (hb : b ∈ Bp A t) : r * b * r⁻¹ ∈ Bp A t := by
  refine ⟨mem_centralizer_iff.2 fun x hx => ?_, ?_⟩
  · have hx' : r⁻¹ * x * r ∈ A := by
      have := H.normalizer_W5_conj_mem W (inv_mem hr) hx
      simpa using this
    have := mem_centralizer_iff.1 hb.1 _ hx'
    calc x * (r * b * r⁻¹) = r * ((r⁻¹ * x * r) * b) * r⁻¹ := by group
      _ = r * (b * (r⁻¹ * x * r)) * r⁻¹ := by rw [this]
      _ = r * b * r⁻¹ * x := by group
  · have hbN : b ∈ normalizer ((W5 A t : Subgroup G) : Set G) := hb.2
    exact (normalizer _).mul_mem ((normalizer _).mul_mem hr hbN) ((normalizer _).inv_mem hr)

theorem ThCyc.S_le_normalizer : S ≤ normalizer ((W5 A t : Subgroup G) : Set G) := fun s hs => by
  have hnorm : ∀ s', s' ∈ S ↔ s * s' * s⁻¹ ∈ S := fun s' =>
    ⟨fun h => S.mul_mem (S.mul_mem hs h) (S.inv_mem hs), fun h => by
      have := S.mul_mem (S.mul_mem (S.inv_mem hs) h) hs
      simpa [mul_assoc] using this⟩
  exact H.mem_normalizer_W5_of_L W (W.S_le hs) fun x hx => W.conj_mem_A hnorm hx

end

end CFSG.EvenSporadicStandard.ThStd
