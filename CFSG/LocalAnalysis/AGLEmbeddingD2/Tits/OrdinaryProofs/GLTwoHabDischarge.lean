module

public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.OvergroupLeaves

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GLTwoHabDischarge

theorem charP_two_of_two_dvd_card (F : Type) [Field F] [Finite F] (h : 2 ∣ Nat.card F) :
    CharP F 2 := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  rw [Nat.card_eq_fintype_card, hn] at h
  have h2 : 2 ∣ ringChar F := Nat.prime_two.dvd_of_dvd_pow h
  have hr : ringChar F = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  rw [← hr]
  infer_instance

theorem isMulCommutative_of_two_dvd_card_GL2 {F : Type} [Field F] [Finite F]
    (h : 2 ∣ Nat.card F) :
    ∀ S : Subgroup (GL (Fin 2) F), IsPGroup 2 S → IsMulCommutative S := by
  have : CharP F 2 := charP_two_of_two_dvd_card F h
  intro S hS
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.OvergroupLeaves.isMulCommutative_of_isPGroup_two_GL2 hS

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GLTwoHabDischarge

end
