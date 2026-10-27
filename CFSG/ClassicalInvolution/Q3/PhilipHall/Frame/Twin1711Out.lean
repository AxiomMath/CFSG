module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Defs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace Twin1711

section Out

variable {H : Type} [Group H]

@[expose] def fixAut (S : Set H) : Subgroup (MulAut H) where
  carrier := {α | ∀ s ∈ S, α s = s}
  mul_mem' := by
    intro α β hα hβ s hs
    rw [MulAut.mul_apply, hβ s hs, hα s hs]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro α hα s hs
    calc α⁻¹ s = α⁻¹ (α s) := by rw [hα s hs]
      _ = s := α.symm_apply_apply s

@[expose] def innAut (H : Type) [Group H] : Subgroup (MulAut H) :=
  (MulAut.conj : H →* MulAut H).range

instance innAut_normal : (innAut H).Normal :=
  ⟨by
    rintro _ ⟨h, rfl⟩ g
    refine ⟨g h, ?_⟩
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]⟩

theorem card_fixAut_mul_card_center_le [Finite H] (S : Set H) :
    Nat.card (fixAut S) * Nat.card (Subgroup.center H) ≤
      Nat.card (MulAut H ⧸ innAut H) * Nat.card (Subgroup.centralizer S) := by
  classical
  let A := fixAut S
  let ρ : ↥A →* MulAut H ⧸ innAut H := (QuotientGroup.mk' (innAut H)).comp A.subtype
  let ψ : ↥(Subgroup.centralizer S) →* MulAut H :=
    (MulAut.conj : H →* MulAut H).comp (Subgroup.centralizer S).subtype
  have h1 := Subgroup.card_ker_mul_card_range ρ
  have h3 := Subgroup.card_ker_mul_card_range ψ
  have h2 : Nat.card ρ.range ≤ Nat.card (MulAut H ⧸ innAut H) :=
    Nat.card_le_card_of_injective (fun x : ρ.range => (x : MulAut H ⧸ innAut H)) Subtype.val_injective
  have h4 : Nat.card ρ.ker ≤ Nat.card ψ.range := by
    refine Nat.card_le_card_of_injective
      (fun a : ρ.ker => (⟨(a : ↥A).1, ?_⟩ : ψ.range)) ?_
    · obtain ⟨⟨α, hα⟩, hρ⟩ := a
      have hI : α ∈ innAut H := by simpa [ρ] using hρ
      obtain ⟨h, rfl⟩ := hI
      refine ⟨⟨h, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have := hα s hs
      simp only [MulAut.conj_apply] at this
      calc s * h = (h * s * h⁻¹) * h := by rw [this]
        _ = h * s := by group
    · intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ψ.range => (x : MulAut H)) hab
  have h5 : Nat.card (Subgroup.center H) ≤ Nat.card ψ.ker := by
    refine Nat.card_le_card_of_injective
      (fun z : Subgroup.center H => (⟨⟨z, ?_⟩, ?_⟩ : ψ.ker)) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro s _
      exact (Subgroup.mem_center_iff.mp z.2 s)
    · rw [MonoidHom.mem_ker]
      ext x
      simp only [ψ, MonoidHom.comp_apply, Subgroup.subtype_apply, MulAut.conj_apply, MulAut.one_apply]
      have := Subgroup.mem_center_iff.mp z.2 x
      calc (z : H) * x * (z : H)⁻¹ = x * z * (z : H)⁻¹ := by rw [this]
        _ = x := by group
    · intro a b hab
      have := congrArg (fun y : ψ.ker => ((y : ↥(Subgroup.centralizer S)) : H)) hab
      exact Subtype.ext this
  calc Nat.card A * Nat.card (Subgroup.center H)
      = (Nat.card ρ.ker * Nat.card ρ.range) * Nat.card (Subgroup.center H) := by rw [h1]
    _ ≤ (Nat.card ρ.ker * Nat.card (MulAut H ⧸ innAut H)) * Nat.card (Subgroup.center H) := by
        gcongr
    _ = Nat.card (MulAut H ⧸ innAut H) * (Nat.card ρ.ker * Nat.card (Subgroup.center H)) := by ring
    _ ≤ Nat.card (MulAut H ⧸ innAut H) * (Nat.card ψ.range * Nat.card ψ.ker) := by gcongr
    _ = Nat.card (MulAut H ⧸ innAut H) * Nat.card (Subgroup.centralizer S) := by
        rw [mul_comm (Nat.card ψ.range), h3]

end Out

variable {G : Type} [Group G]

theorem fixSet_eq_fixAut (X : Subgroup G) (B : Set (Subgroup G)) :
    fixSet X B = fixAut {y : ↥X | ∃ b ∈ B, (y : G) ∈ b} := by
  ext α
  constructor
  · rintro hα y ⟨b, hb, hy⟩
    exact hα b hb y hy
  · intro hα b hb y hy
    exact hα y ⟨b, hb, hy⟩

theorem card_fixSet_mul_card_center_le [Finite G] (X : Subgroup G) (B : Set (Subgroup G)) :
    Nat.card (fixSet X B) * Nat.card (Subgroup.center ↥X) ≤
      Nat.card (MulAut ↥X ⧸ innAut ↥X) *
        Nat.card (Subgroup.centralizer {y : ↥X | ∃ b ∈ B, (y : G) ∈ b}) := by
  rw [fixSet_eq_fixAut]
  exact card_fixAut_mul_card_center_le _

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
