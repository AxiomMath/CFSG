module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ExtA

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

@[expose] def cenMod {G : Type*} [Group G] (H N : Subgroup G) (y : G)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) : Subgroup G where
  carrier := {h | h ∈ H ∧ y * h * y⁻¹ * h⁻¹ ∈ N}
  one_mem' := ⟨H.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
        (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact N.mul_mem ha' (hN a ha _ hb')
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have e : y * a⁻¹ * y⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by group
    rw [e]
    exact hN a⁻¹ (H.inv_mem ha) _ (N.inv_mem ha')

theorem mem_cenMod {G : Type*} [Group G] {H N : Subgroup G} {y : G}
    {hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N} {g : G} :
    g ∈ cenMod H N y hN ↔ g ∈ H ∧ y * g * y⁻¹ * g⁻¹ ∈ N := Iff.rfl

theorem card_cenMod_le {G : Type} [Group G] [Finite G] (h9 : IG_9_16) {H N : Subgroup G}
    (hNH : N ≤ H) (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) {x : G} (hx : x ∈ H) :
    Nat.card (cenMod H N x hN) ≤ Nat.card N * Nat.card ↥(H ⊓ centralizer ({x} : Set G)) := by
  classical
  let N' : Subgroup ↥H := N.subgroupOf H
  have hnorm : N'.Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : ↥H) : G) ∈ N
    simpa using hN g g.2 n hn⟩
  let x' : ↥H := ⟨x, hx⟩
  have h9' := @h9 ↥H _ _ N' hnorm x'
  let C : Subgroup (↥H ⧸ N') := centralizer ({(x' : ↥H ⧸ N')} : Set (↥H ⧸ N'))
  let K' : Subgroup ↥H := C.comap (QuotientGroup.mk' N')
  have hK'card : Nat.card K' = Nat.card N' * Nat.card C := by
    have h1 := Subgroup.card_mul_index K'
    have h2 : K'.index = C.index :=
      Subgroup.index_comap_of_surjective C (QuotientGroup.mk'_surjective N')
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    have h4 := Subgroup.card_mul_index C
    have hpos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card K' * C.index = Nat.card K' * K'.index := by rw [h2]
      _ = Nat.card ↥H := h1
      _ = Nat.card (↥H ⧸ N') * Nat.card N' := h3
      _ = (Nat.card C * C.index) * Nat.card N' := by rw [h4]
      _ = Nat.card N' * Nat.card C * C.index := by ring
  have hmem : ∀ g : ↥H, g ∈ K' ↔ (g : G) ∈ cenMod H N x hN := by
    intro g
    show (QuotientGroup.mk' N') g ∈ C ↔ _
    rw [mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [mem_cenMod]
    refine ⟨fun hc => ⟨g.2, ?_⟩, fun hc => ?_⟩
    · have h1 : ⁅(QuotientGroup.mk' N') x', (QuotientGroup.mk' N') g⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 hc
      rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      simp only [commutatorElement_def] at h1
      exact h1
    · have h1 : ⁅x', g⁆ ∈ N' := by
        simp only [commutatorElement_def]
        exact hc.2
      have h2 : (QuotientGroup.mk' N') ⁅x', g⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
      rw [map_commutatorElement] at h2
      exact commutatorElement_eq_one_iff_mul_comm.1 h2
  have hcm : Nat.card (cenMod H N x hN) = Nat.card K' :=
    Nat.card_congr
      { toFun := fun g => ⟨⟨g.1, g.2.1⟩, (hmem _).2 g.2⟩
        invFun := fun k => ⟨k.1.1, (hmem k.1).1 k.2⟩
        left_inv := fun g => rfl
        right_inv := fun k => rfl }
  have hN'card : Nat.card N' = Nat.card N := Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv
  have hC : Nat.card ↥(centralizer ({x'} : Set ↥H)) ≤ Nat.card ↥(H ⊓ centralizer ({x} : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun g : ↥(centralizer ({x'} : Set ↥H)) => (⟨g.1.1, g.1.2, ?_⟩ : ↥(H ⊓ centralizer ({x} : Set G)))) ?_
    · have := mem_centralizer_iff.1 g.2 x' rfl
      show g.1.1 ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact congrArg Subtype.val this
    · intro a b hab
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun z : ↥(H ⊓ centralizer ({x} : Set G)) => (z : G)) hab
  rw [hcm, hK'card, hN'card]
  exact Nat.mul_le_mul_left _ (le_trans h9' hC)

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
