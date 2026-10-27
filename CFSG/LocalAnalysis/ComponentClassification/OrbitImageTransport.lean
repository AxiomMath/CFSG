module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.OrbitImageTransport

theorem image_orbit {A B X Y : Type*} [Group A] [Group B] [MulAction A X] [MulAction B Y]
    (homomorphism : A →* B) (hsurjective : Function.Surjective homomorphism)
    (embedding : Y → X)
    (hequivariant : ∀ actor : A, ∀ point : Y, actor • embedding point = embedding (homomorphism actor • point))
    (point : Y) : embedding '' MulAction.orbit B point = MulAction.orbit A (embedding point) := by
  ext member
  constructor
  · rintro ⟨preimage, hpreimage, rfl⟩
    obtain ⟨actor, rfl⟩ := MulAction.mem_orbit_iff.mp hpreimage
    obtain ⟨lift, rfl⟩ := hsurjective actor
    exact MulAction.mem_orbit_iff.mpr ⟨lift, hequivariant lift point⟩
  · intro hmember
    obtain ⟨actor, rfl⟩ := MulAction.mem_orbit_iff.mp hmember
    exact ⟨homomorphism actor • point, MulAction.mem_orbit_iff.mpr ⟨homomorphism actor, rfl⟩,
      (hequivariant actor point).symm⟩

theorem card {A B X Y : Type*} [Group A] [Group B] [MulAction A X] [MulAction B Y]
    (homomorphism : A →* B) (hsurjective : Function.Surjective homomorphism)
    (embedding : Y → X) (hinjective : Function.Injective embedding)
    (hequivariant : ∀ actor : A, ∀ point : Y, actor • embedding point = embedding (homomorphism actor • point))
    (point : Y) : Nat.card ↥(MulAction.orbit B point) = Nat.card ↥(MulAction.orbit A (embedding point)) := by
  rw [← image_orbit homomorphism hsurjective embedding hequivariant point]
  exact Nat.card_congr (Equiv.Set.image embedding _ hinjective)

end CFSG.ComponentClassification.OrbitImageTransport
