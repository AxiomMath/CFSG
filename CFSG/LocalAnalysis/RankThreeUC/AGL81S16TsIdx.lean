module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16NatU
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16TsModel

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem U4NatData.ts_index {n : ℕ} {L V : Subgroup G} (d : U4NatData G n L V) (hn : 1 ≤ n) :
    ∀ W : Subgroup G, W ≤ V → (∀ w ∈ W, w ≠ 1 → d.sing w) → 2 ^ (4 * n) ≤ W.relIndex V := by
  intro W hWV hsing
  obtain ⟨S, hSmem⟩ : ∃ S : AddSubgroup (Fin 4 → d.F),
      ∀ x : Fin 4 → d.F, x ∈ S ↔ ∃ w : ↥V, (w : G) ∈ W ∧ Multiplicative.toAdd (d.φ w) = x :=
    ⟨{ carrier := {x | ∃ w : ↥V, (w : G) ∈ W ∧ Multiplicative.toAdd (d.φ w) = x}
       add_mem' := by
         rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
         exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, by rw [map_mul, toAdd_mul]⟩
       zero_mem' := ⟨1, W.one_mem, by rw [map_one, toAdd_one]⟩
       neg_mem' := by
         rintro _ ⟨w, hw, rfl⟩
         exact ⟨w⁻¹, W.inv_mem hw, by rw [map_inv, toAdd_inv]⟩ }, fun _ => Iff.rfl⟩
  have hmemS : ∀ w : ↥W, Multiplicative.toAdd (d.φ ⟨(w : G), hWV w.2⟩) ∈ S :=
    fun w => (hSmem _).2 ⟨⟨(w : G), hWV w.2⟩, w.2, rfl⟩
  have hbij : Function.Bijective
      (fun w : ↥W => (⟨Multiplicative.toAdd (d.φ ⟨(w : G), hWV w.2⟩), hmemS w⟩ : ↥S)) := by
    refine ⟨?_, ?_⟩
    · intro w w' h
      have h1 : Multiplicative.toAdd (d.φ ⟨(w : G), hWV w.2⟩)
          = Multiplicative.toAdd (d.φ ⟨(w' : G), hWV w'.2⟩) := congrArg Subtype.val h
      have h2 : (⟨(w : G), hWV w.2⟩ : ↥V) = ⟨(w' : G), hWV w'.2⟩ :=
        d.φ_bij.injective (Multiplicative.toAdd.injective h1)
      exact Subtype.ext (Subtype.mk.inj h2)
    · rintro ⟨s, hs⟩
      obtain ⟨w, hw, hws⟩ := (hSmem s).1 hs
      exact ⟨⟨(w : G), hw⟩, Subtype.ext hws⟩
  have hcard : Nat.card S = Nat.card W :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  have hSsing : ∀ x ∈ S, x ≠ 0 → ∑ i, x i ^ (2 ^ n + 1) = 0 := by
    intro x hx hx0
    obtain ⟨w, hw, rfl⟩ := (hSmem x).1 hx
    have hw1 : (w : G) ≠ 1 := by
      intro h1
      apply hx0
      have hw' : w = 1 := Subtype.ext h1
      rw [hw', map_one, toAdd_one]
    obtain ⟨hV, h⟩ : ∃ hV : (w : G) ∈ V,
        ∑ i, (Multiplicative.toAdd (d.φ ⟨(w : G), hV⟩)) i ^ (2 ^ n + 1) = 0 :=
      hsing _ hw hw1
    exact h
  have hle : Nat.card W ≤ 2 ^ (4 * n) := by
    rw [← hcard]
    exact totally_singular_card_le hn d.card_F S hSsing
  have hmul : W.relIndex V * Nat.card W = Nat.card V := by
    have h := Subgroup.relIndex_mul_card (H := W) (K := V)
    rw [inf_eq_left.mpr hWV] at h
    exact h
  have hpos : 0 < 2 ^ (4 * n) := by positivity
  have hsq : 2 ^ (4 * n) * 2 ^ (4 * n) = 2 ^ (8 * n) := by
    rw [← pow_add]
    congr 1
    omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc 2 ^ (4 * n) * 2 ^ (4 * n) = 2 ^ (8 * n) := hsq
    _ = Nat.card V := d.card_V.symm
    _ = W.relIndex V * Nat.card W := hmul.symm
    _ ≤ W.relIndex V * 2 ^ (4 * n) := Nat.mul_le_mul le_rfl hle

end CFSG.LocalAnalysis.RankThreeUC
