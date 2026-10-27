module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type*} [Group G]

@[expose] noncomputable def centB (p : ℕ) (B L : Subgroup G) : Subgroup G :=
  ((barAut p L).ker ⊓ (B ⊓ Subgroup.normalizer (L : Set G)).subgroupOf
    (Subgroup.normalizer (L : Set G))).map (Subgroup.normalizer (L : Set G)).subtype

theorem mem_centB {p : ℕ} {B L : Subgroup G} {b : G} :
    b ∈ centB p B L ↔
      ∃ hb : b ∈ Subgroup.normalizer (L : Set G), b ∈ B ∧ barAut p L ⟨b, hb⟩ = 1 := by
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨x.2, ?_, hx1⟩
    exact (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 hx2)).1
  · rintro ⟨hb, hbB, h1⟩
    exact ⟨⟨b, hb⟩, ⟨h1, (Subgroup.mem_subgroupOf).2 (Subgroup.mem_inf.2 ⟨hbB, hb⟩)⟩, rfl⟩

theorem centB_le (p : ℕ) (B L : Subgroup G) : centB p B L ≤ B := fun _ hb =>
  (mem_centB.1 hb).choose_spec.1

variable [Finite G]

theorem card_B_eq (p : ℕ) (B L : Subgroup G) :
    Nat.card B = (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B *
      (Nat.card (autBar p B L) * Nat.card (centB p B L)) := by
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hN
  set N' : Subgroup ↥N := (B ⊓ N).subgroupOf N with hN'
  have h1 : (B ⊓ N).relIndex B * Nat.card ↥((B ⊓ N) ⊓ B) = Nat.card B :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.2 (inf_le_left : B ⊓ N ≤ B)] at h1
  have h2 : (barAut p L).ker.relIndex N' * Nat.card ↥((barAut p L).ker ⊓ N') = Nat.card N' :=
    Subgroup.relIndex_mul_card _ _
  rw [Subgroup.relIndex_ker] at h2
  have h3 : Nat.card N' = Nat.card ↥(B ⊓ N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : B ⊓ N ≤ N)).toEquiv
  have h4 : Nat.card (centB p B L) = Nat.card ↥((barAut p L).ker ⊓ N') :=
    Subgroup.card_map_of_injective N.subtype_injective
  have h5 : Nat.card (autBar p B L) = Nat.card ↥(N'.map (barAut p L)) := rfl
  rw [← h1, ← h3, ← h2, h4, h5]

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
