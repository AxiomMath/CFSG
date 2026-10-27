module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBBasis

public section

namespace CFSG.EvenSporadicStandard.M24Std.SplitB

open Subgroup CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def iotaE {L : Subgroup G} (e : L ≃* NativeSporadic.M24) : S24 →* G :=
  L.subtype.comp e.symm.toMonoidHom

theorem iotaE_apply {L : Subgroup G} (e : L ≃* NativeSporadic.M24) (y : S24) :
    iotaE e y = ((e.symm y : L) : G) := rfl

theorem iotaE_injective {L : Subgroup G} (e : L ≃* NativeSporadic.M24) :
    Function.Injective (iotaE e) :=
  fun _ _ h => e.symm.injective (Subtype.ext h)

theorem iotaE_mem {L : Subgroup G} (e : L ≃* NativeSporadic.M24) (y : S24) : iotaE e y ∈ L :=
  (e.symm y).2

theorem exists_iotaE_eq {L : Subgroup G} (e : L ≃* NativeSporadic.M24) {g : G} (hg : g ∈ L) :
    ∃ y, iotaE e y = g :=
  ⟨e ⟨g, hg⟩, by simp [iotaE]⟩

theorem iotaE_mem_B_iff {L B : Subgroup G} {e : L ≃* NativeSporadic.M24}
    (he : ∀ x : L, (x : G) ∈ B ↔ ((e x : NativeSporadic.M24) : S24) ∈ m24B0l) (y : S24) :
    iotaE e y ∈ B ↔ y ∈ m24B0l := by
  rw [iotaE_apply, he, MulEquiv.apply_symm_apply]

theorem iotaE_mem_egNL {L B : Subgroup G} (hBL : B ≤ L) {e : L ≃* NativeSporadic.M24}
    (he : ∀ x : L, (x : G) ∈ B ↔ ((e x : NativeSporadic.M24) : S24) ∈ m24B0l) {x : S24}
    (hx : NormB0 x) : iotaE e x ∈ egNL L B := by
  refine Subgroup.mem_inf.2 ⟨?_, iotaE_mem e x⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ L
  · obtain ⟨y, rfl⟩ := exists_iotaE_eq e hg
    rw [← map_inv, ← map_mul, ← map_mul, iotaE_mem_B_iff he, iotaE_mem_B_iff he]
    exact hx.mem_iff y
  · have h1 : g ∉ B := fun h => hg (hBL h)
    have h2 : iotaE e x * g * (iotaE e x)⁻¹ ∉ B := by
      intro h
      apply hg
      have e3 : g = (iotaE e x)⁻¹ * (iotaE e x * g * (iotaE e x)⁻¹) * iotaE e x := by group
      rw [e3]
      exact L.mul_mem (L.mul_mem (L.inv_mem (iotaE_mem e x)) (hBL h)) (iotaE_mem e x)
    exact iff_of_false h1 h2

theorem map_ebasis4 {X Y : Type} [Group X] [Group Y] (φ : X →* Y) (f : Fin 4 → X)
    (c : Fin 4 → ZMod 2) : φ (ebasis4 f c) = ebasis4 (fun i => φ (f i)) c := by
  simp [ebasis4]

end CFSG.EvenSporadicStandard.M24Std.SplitB
