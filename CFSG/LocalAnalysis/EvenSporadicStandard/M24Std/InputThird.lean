module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.InputSecond
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic
open scoped MatrixGroups

@[expose] def LayerDisj (X : Type) [Group X] [Finite X] : Prop :=
  Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* alternatingGroup (Fin 8)) ∨
    Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃*
      alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) ∨
    Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* alternatingGroup (Fin 10)) ∨
    Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* PSL(4, GaloisField 2 2)) ∨
    IsSporadic (egaLayer (X ⧸ fusionOddCore X)) .HS

@[expose] def FFzData {G : Type} [Group G] (D : Subgroup G) (z : G) : Prop :=
  ∃ F : Subgroup G, F ≤ normalizer (D : Set G) ∧ Nat.card F = 2 ^ 10 * 315 ∧
    (∀ a ∈ F, ∀ b ∈ F, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) ∧
    ∀ a ∈ F, z * a * z⁻¹ ∈ F → a = 1

theorem wreathData_of_FFzData {G : Type} [Group G] [Finite G] {D : Subgroup G} {z : G}
    (h : FFzData D z) : WreathData z := by
  obtain ⟨F, -, hcard, hcomm, hint⟩ := h
  obtain ⟨R, hR, -, hRF⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := G) (H := ⊥) (L := F)
    (n := 10) Nat.prime_two (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hcard]; exact Dvd.intro _ rfl) bot_le
  exact ⟨R, hR, fun a ha b hb => hcomm a (hRF ha) b (hRF hb), fun a ha haz =>
    hint a (hRF ha) (hRF haz)⟩

@[expose] def Ega81Lemmas214to217Red : Prop :=
  HarrisSolomonZ2S6IsoK →
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), KLocalSections G →
      fusionZStar G = ⊥ → standardComponentIsStandard L → LocalSetting G L z →
      ∀ A B C D : Subgroup G, FirstHalfData L z A B C D → LayerDisj (egQD D) → FFzData D z

end CFSG.EvenSporadicStandard.M24Std
