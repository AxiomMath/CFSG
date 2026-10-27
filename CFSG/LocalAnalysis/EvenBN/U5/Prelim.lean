module

public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.Factorization
public import CFSG.LinearAlgebra.SL2MinimalFaithfulSection
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Prelim

theorem inv_eq_self_of_mem {V : Subgroup G} (hV : IsElementaryAbelian 2 V) {v : G}
    (hv : v ∈ V) : v⁻¹ = v := by
  have h := @CFSG.elemPow_eq_one_of_isElementaryAbelian 2 G _ V hV v hv
  exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h)

theorem mul_comm_of_mem {V : Subgroup G} (hV : IsElementaryAbelian 2 V) {v w : G} (hv : v ∈ V)
    (hw : w ∈ V) : v * w = w * v :=
  congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : V) ⟨w, hw⟩)

theorem conj_mem_of_mem_normalizer {V : Subgroup G} {a w : G} (ha : a ∈ normalizer (V : Set G))
    (hw : w ∈ V) : a⁻¹ * w * a ∈ V := by
  have := (mem_normalizer_iff.mp (inv_mem ha) w).mp hw
  rwa [inv_inv] at this

end Prelim

namespace Prelim

@[expose] def commMap {V : Subgroup G} (hV : IsElementaryAbelian 2 V) {z : G}
    (hz : z ∈ normalizer (V : Set G)) : V →* V :=
  MonoidHom.mk' (fun w => ⟨z⁻¹ * w * z * (w : G)⁻¹,
    V.mul_mem (conj_mem_of_mem_normalizer hz w.2) (V.inv_mem w.2)⟩) (by
    intro a b
    apply Subtype.ext
    simp only [coe_mul]
    have h2 : z⁻¹ * (b : G) * z ∈ V := conj_mem_of_mem_normalizer hz b.2
    have hc : (a : G)⁻¹ * (z⁻¹ * b * z) = z⁻¹ * b * z * (a : G)⁻¹ :=
      mul_comm_of_mem hV (V.inv_mem a.2) h2
    have hc' : (b : G)⁻¹ * (a : G)⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ :=
      mul_comm_of_mem hV (V.inv_mem b.2) (V.inv_mem a.2)
    calc z⁻¹ * ((a : G) * b) * z * ((a : G) * b)⁻¹
        = (z⁻¹ * a * z) * ((z⁻¹ * b * z) * ((b : G)⁻¹ * (a : G)⁻¹)) := by group
      _ = (z⁻¹ * a * z) * ((z⁻¹ * b * z) * ((a : G)⁻¹ * (b : G)⁻¹)) := by rw [hc']
      _ = (z⁻¹ * a * z) * (((z⁻¹ * b * z) * (a : G)⁻¹) * (b : G)⁻¹) := by
          simp only [mul_assoc]
      _ = (z⁻¹ * a * z) * (((a : G)⁻¹ * (z⁻¹ * b * z)) * (b : G)⁻¹) := by rw [hc]
      _ = z⁻¹ * a * z * (a : G)⁻¹ * (z⁻¹ * b * z * (b : G)⁻¹) := by simp only [mul_assoc])

end Prelim

theorem yamada_sup_eq [Finite G] {p : ℕ} [Fact p.Prime] {A X : Subgroup G} (hA : IsPGroup p A)
    (hX : ¬ p ∣ Nat.card X) (hXA : X ≤ normalizer (A : Set G))
    (hn : A ≤ normalizer ((A ⊓ centralizer (X : Set G) : Subgroup G) : Set G)) :
    (A ⊓ centralizer (X : Set G)) ⊔ ⁅X, A⁆ = A ∧
      ⁅X, A⁆ ≤ centralizer ((A ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hfac, hle, hcen⟩ := U4.yamada_central_product hA hX hXA hn
  refine ⟨le_antisymm (sup_le inf_le_left hle) fun a ha => ?_, hcen⟩
  obtain ⟨d, hd, c, hc, rfl⟩ := hfac a ha
  exact mul_mem (mem_sup_right hd) (mem_sup_left hc)

namespace Prelim

theorem inf_centralizer_ne_bot_of_pow_mem [Finite G] {A Y : Subgroup G} (hA : IsPGroup 2 A)
    (hA1 : A ≠ ⊥) (hYA : Y ≤ normalizer (A : Set G))
    (hY : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ centralizer (A : Set G)) :
    A ⊓ centralizer (Y : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := SL2MinimalFaithful.conjAction hYA
  have hR : IsPGroup 2 ρ.range := by
    rintro ⟨_, y, rfl⟩
    obtain ⟨k, hk⟩ := hY y y.2
    refine ⟨k, Subtype.ext ?_⟩
    ext a
    change ((ρ y ^ 2 ^ k) a : G) = a
    rw [← map_pow, SL2MinimalFaithful.conjAction_apply]
    change (y : G) ^ 2 ^ k * a * ((y : G) ^ 2 ^ k)⁻¹ = a
    rw [(mem_centralizer_iff.mp hk a a.2).symm, mul_inv_cancel_right]
  have h2A : 2 ∣ Nat.card A := by
    obtain ⟨n, hn, hcard⟩ := hA.nontrivial_iff_card.mp
      ((nontrivial_iff_ne_bot A).mpr hA1)
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  have h1 : (1 : A) ∈ MulAction.fixedPoints ρ.range A := fun r => map_one (r : MulAut A)
  obtain ⟨b, hb, hb1⟩ := hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point A h2A h1
  intro hbot
  have hbmem : (b : G) ∈ A ⊓ centralizer (Y : Set G) := by
    refine ⟨b.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have := congrArg Subtype.val (hb ⟨ρ ⟨y, hy⟩, ⟨y, hy⟩, rfl⟩)
    change (y : G) * b * y⁻¹ = b at this
    calc y * (b : G) = y * b * y⁻¹ * y := by group
      _ = b * y := by rw [this]
  rw [hbot, mem_bot] at hbmem
  exact hb1 (Subtype.ext hbmem.symm)

theorem normalizer_le_normalizer_centralizer (B : Subgroup G) :
    normalizer (B : Set G) ≤ normalizer (centralizer (B : Set G) : Set G) := by
  intro h hh
  refine mem_normalizer_iff.mpr fun g => ?_
  constructor
  · intro hg
    rw [mem_centralizer_iff] at hg ⊢
    intro b hbB
    have hb' : h⁻¹ * b * h ∈ B := by
      have := (mem_normalizer_iff.mp (inv_mem hh) b).mp hbB
      rwa [inv_inv] at this
    have := hg _ hb'
    calc b * (h * g * h⁻¹) = h * (h⁻¹ * b * h * g) * h⁻¹ := by group
      _ = h * (g * (h⁻¹ * b * h)) * h⁻¹ := by rw [this]
      _ = h * g * h⁻¹ * b := by group
  · intro hg
    rw [mem_centralizer_iff] at hg ⊢
    intro b hbB
    have hbB' : h * b * h⁻¹ ∈ B := (mem_normalizer_iff.mp hh b).mp hbB
    have := hg (h * b * h⁻¹) hbB'
    calc b * g = h⁻¹ * (h * b * h⁻¹ * (h * g * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * g * h⁻¹ * (h * b * h⁻¹)) * h := by rw [this]
      _ = g * b := by group

theorem normal_centralizer_subgroupOf {B H : Subgroup G} (hH : H ≤ normalizer (B : Set G)) :
    ((centralizer (B : Set G)).subgroupOf H).Normal :=
  normal_subgroupOf_of_le_normalizer (hH.trans (normalizer_le_normalizer_centralizer B))

end Prelim

end CFSG.LocalAnalysis.EvenBN.U5
