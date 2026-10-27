module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NoLift4
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.DataTransport

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G X : Type} [Group G] [Group X]

@[expose] def mon4 (f : Fin 4 → G) (c : Fin 4 → ZMod 2) : G :=
  f 0 ^ (c 0).val * f 1 ^ (c 1).val * f 2 ^ (c 2).val * f 3 ^ (c 3).val

structure LiftData (L F : Subgroup G) : Prop where
  exists_data : ∃ (f : Fin 4 → G) (b₁ b₂ : G), (∀ i, f i ∈ F) ∧ (∀ x ∈ F, ∃ c, x = mon4 f c) ∧
    (∀ c c', mon4 f c = mon4 f c' → c = c') ∧ b₁ ∈ L ∧ b₂ ∈ L ∧
    (∀ x, x ∈ F ↔ b₁ * x * b₁⁻¹ ∈ F) ∧ (∀ x, x ∈ F ↔ b₂ * x * b₂⁻¹ ∈ F) ∧
    b₁ * b₁ = 1 ∧ b₂ * b₂ = 1 ∧ b₁ * b₂ = b₂ * b₁ ∧
    (∀ i, b₁ * f i * b₁⁻¹ = mon4 f (liftA1 i)) ∧ (∀ i, b₂ * f i * b₂⁻¹ = mon4 f (liftA2 i))

theorem map_mon4 (φ : X →* G) (f : Fin 4 → X) (c : Fin 4 → ZMod 2) :
    φ (mon4 f c) = mon4 (fun i => φ (f i)) c := by
  simp [mon4]

theorem LiftData.map {φ : X →* G} (hφ : Function.Injective φ) {F : Subgroup X}
    (D : LiftData (⊤ : Subgroup X) F) : LiftData φ.range (F.map φ) := by
  obtain ⟨f, b₁, b₂, hf, hspan, hind, -, -, hn1, hn2, hb1, hb2, hb12, ha1, ha2⟩ := D.exists_data
  refine ⟨⟨fun i => φ (f i), φ b₁, φ b₂, fun i => Subgroup.mem_map_of_mem φ (hf i), ?_, ?_,
    ⟨b₁, rfl⟩, ⟨b₂, rfl⟩, mem_map_iff_conj hφ hn1, mem_map_iff_conj hφ hn2, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := hspan x hx
    exact ⟨c, map_mon4 φ f c⟩
  · intro c c' h
    rw [← map_mon4, ← map_mon4] at h
    exact hind c c' (hφ h)
  · rw [← map_mul, hb1, map_one]
  · rw [← map_mul, hb2, map_one]
  · rw [← map_mul, ← map_mul, hb12]
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, ha1 i, map_mon4]
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, ha2 i, map_mon4]

end CFSG.EvenSporadicStandard.M23Std
