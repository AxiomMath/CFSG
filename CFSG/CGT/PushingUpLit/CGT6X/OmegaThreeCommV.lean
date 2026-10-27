module

public import CFSG.Quasithin.Background.Module
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem ncard_le_card_commV [Finite V] {Y : Subgroup (MulAut V)} {y : MulAut V} (hy : y ∈ Y)
    {P : Subgroup V} (hP : ∀ p ∈ P, y p ∈ P) {W : Type*} [AddCommGroup W]
    (Φ : ↥P ≃* Multiplicative W) (α : W → W)
    (hΦ : ∀ (p : ↥P) (hp : y (p : V) ∈ P),
      Φ ⟨y (p : V), hp⟩ = Multiplicative.ofAdd (α (Multiplicative.toAdd (Φ p)))) :
    Set.ncard {z : W | ∃ w, z = α w - w} ≤ Nat.card ↥(commV Y) := by
  let e : {r : ↥(commV Y) // (r : V) ∈ P} → W := fun r => Multiplicative.toAdd (Φ ⟨r.1, r.2⟩)
  have he : Function.Injective e := by
    intro r r' h
    have h' : Φ ⟨r.1, r.2⟩ = Φ ⟨r'.1, r'.2⟩ := Multiplicative.toAdd.injective h
    have h'' : (⟨r.1, r.2⟩ : ↥P) = ⟨r'.1, r'.2⟩ := Φ.injective h'
    have h3 : ((r.1 : ↥(commV Y)) : V) = ((r'.1 : ↥(commV Y)) : V) := Subtype.mk.inj h''
    exact Subtype.ext (Subtype.ext h3)
  have hsub : {z : W | ∃ w, z = α w - w} ⊆ Set.range e := by
    rintro z ⟨w, rfl⟩
    let p : ↥P := Φ.symm (Multiplicative.ofAdd w)
    have hp : y (p : V) ∈ P := hP p p.2
    have hmem : y (p : V) * (p : V)⁻¹ ∈ commV Y := Subgroup.subset_closure ⟨y, hy, p, rfl⟩
    refine ⟨⟨⟨y (p : V) * (p : V)⁻¹, hmem⟩, P.mul_mem hp (P.inv_mem p.2)⟩, ?_⟩
    have hΦp : Φ p = Multiplicative.ofAdd w := Φ.apply_symm_apply _
    have hprod : (⟨y (p : V) * (p : V)⁻¹, P.mul_mem hp (P.inv_mem p.2)⟩ : ↥P) =
        ⟨y (p : V), hp⟩ * p⁻¹ := rfl
    show Multiplicative.toAdd (Φ ⟨y (p : V) * (p : V)⁻¹, _⟩) = α w - w
    rw [hprod, map_mul, map_inv, hΦ p hp, hΦp]
    simp [sub_eq_add_neg]
  calc Set.ncard {z : W | ∃ w, z = α w - w} ≤ Set.ncard (Set.range e) :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card {r : ↥(commV Y) // (r : V) ∈ P} := by
        rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective he]
    _ ≤ Nat.card ↥(commV Y) := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

end CFSG.CGT.PushingUpLit.CGT6X
