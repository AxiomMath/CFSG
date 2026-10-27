module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21g
public import CFSG.GH74.GLS.Bg.TwoGroups.A44Facts6
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21d

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup

open A44

theorem phi_val_of_isPhi {B : Type} [CommGroup B] (e : B ≃* Z4Z4) {z : B} (hz : z ∈ ZB B)
    (hz1 : z ≠ 1) {φ : MulAut B} (hφ : IsPhi B z φ) :
    (phiB e φ).1 = M4.phiOf (vec e z) := by
  have hvz0 : vec e z ≠ 0 := fun h => hz1 ((vec_eq_zero_iff e z).mp h)
  have hvz2 : vec e z + vec e z = 0 := (mem_ZB_iff e z).mp hz
  exact M4.phiOf_unique _ hvz0 hvz2 _ (phiB e φ).2 ((isPhi_iff e hz φ).mp hφ)

theorem A'_iff {B : Type} [CommGroup B] (e : B ≃* Z4Z4) {x d : MulAut B} (hx : orderOf x = 3)
    (hd : IsDd B x d) (φ : B → MulAut B)
    (hφ : ∀ z ∈ ZB B, z ≠ 1 → IsPhi B z (φ z)) (u : MulAut B) :
    u ∈ ({d, d * iotaB B} ∪ {u | ∃ z ∈ ZB B, z ≠ 1 ∧ u = φ z} : Set (MulAut B)) ↔
      (phiB e u).1 ∈ A'list := by
  have hdd := IsDd_phi e hx hd
  have hdι : (phiB e (d * iotaB B)).1 = M4.mul (phiB e d).1 iota := by
    rw [map_mul, G96.val_mul, phiB_iota]
  constructor
  · rintro ((rfl | rfl) | ⟨z, hz, hz1, rfl⟩)
    · rcases hdd with h | h <;> simp [h, A'list]
    · rw [hdι]
      rcases hdd with h | h
      · rw [h]; simp [A'list]
      · rw [h, dd_iota_iota]; simp [A'list]
    · rw [phi_val_of_isPhi e hz hz1 (hφ z hz hz1)]
      exact phiOf_mem_A' _ (fun h => hz1 ((vec_eq_zero_iff e z).mp h)) ((mem_ZB_iff e z).mp hz)
  · intro h
    rcases A'_cases _ h with h1 | h1 | ⟨vy, hvy0, hvy2, h1⟩
    · rcases hdd with h2 | h2
      · left; left; exact (phiB e).injective (Subtype.ext (h1.trans h2.symm))
      · left; right
        apply (phiB e).injective; apply Subtype.ext
        rw [hdι, h2, dd_iota_iota]; exact h1
    · rcases hdd with h2 | h2
      · left; right
        apply (phiB e).injective; apply Subtype.ext
        rw [hdι, h2]; exact h1
      · left; left; exact (phiB e).injective (Subtype.ext (h1.trans h2.symm))
    · right
      have hvecy : vec e (e.symm (Multiplicative.ofAdd vy)) = vy := by simp [vec]
      have hy : e.symm (Multiplicative.ofAdd vy) ∈ ZB B := by
        rw [mem_ZB_iff e, hvecy]; exact hvy2
      have hy1 : e.symm (Multiplicative.ofAdd vy) ≠ 1 := by
        intro h'; apply hvy0; rw [← hvecy, h', vec_one]
      refine ⟨e.symm (Multiplicative.ofAdd vy), hy, hy1, ?_⟩
      apply (phiB e).injective; apply Subtype.ext
      rw [phi_val_of_isPhi e hy hy1 (hφ _ hy hy1), hvecy, h1]

theorem invOnlyZ_iff {B : Type} [CommGroup B] (e : B ≃* Z4Z4) (u : MulAut B) :
    (∀ b : B, u b = b⁻¹ → b ^ 2 = 1) ↔ InvOnlyZ (phiB e u).1 := by
  constructor
  · intro h w hw
    obtain ⟨b, rfl⟩ := vec_surjective e w
    have h1 : u b = b⁻¹ := by
      apply vec_injective e
      rw [vec_phi, vec_inv]; exact hw
    exact (A44.sq_eq_one_iff e b).mp (h b h1)
  · intro h b hb
    rw [A44.sq_eq_one_iff]
    apply h
    rw [← vec_phi, hb, vec_inv]

theorem iv2_2_1_f1 : IV2_2_1_f1 := by
  intro B _ ⟨e⟩ x hx d hd φ hφ
  have hA0 : ∀ φ : MulAut B, φ ∈ A0 B ↔ (phiB e φ).1.IsA0 := fun φ => by
    rw [mem_A0_iff e, M4.isA0_iff]
  intro A'
  refine ⟨?_, ?_⟩
  · intro u hu
    have := (A'_iff e hx hd φ hφ u).mp hu
    exact (hA0 u).mpr (A'_isA0 _ this)
  · intro u hu hu1
    rw [show u ∈ A' ↔ _ from A'_iff e hx hd φ hφ u, invOnlyZ_iff e u]
    apply A'_char _ (phiB e u).2 ((hA0 u).mp hu)
    intro h
    apply hu1
    apply (phiB e).injective
    apply Subtype.ext
    rw [map_one, G96.val_one]; exact h

end CFSG.GH74.GLS.Bg.TwoGroups
