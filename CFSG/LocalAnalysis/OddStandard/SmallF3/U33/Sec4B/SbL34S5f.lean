module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem card_le_mul_of_decomp (Z Q D : Subgroup G)
    (hdec : ∀ z ∈ Z, ∃ q ∈ Z ⊓ Q, ∃ d ∈ Z ⊓ D, z = q * d) :
    Nat.card Z ≤ Nat.card ↥(Z ⊓ Q) * Nat.card ↥(Z ⊓ D) := by
  classical
  let f : ↥(Z ⊓ Q) × ↥(Z ⊓ D) → ↥Z := fun x =>
    ⟨(x.1 : G) * (x.2 : G),
      Z.mul_mem (Subgroup.mem_inf.mp x.1.2).1 (Subgroup.mem_inf.mp x.2.2).1⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨q, hq, d, hd, hzqd⟩ := hdec z hz
    exact ⟨(⟨q, hq⟩, ⟨d, hd⟩), Subtype.ext hzqd.symm⟩
  have h1 := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at h1

theorem normalizes_of_sup (Q P : Subgroup G) (a b : G)
    (hP : ∀ p ∈ P, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q) (ha : ∀ q ∈ Q, a * q * a⁻¹ ∈ Q)
    (hb : ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) :
    ∀ g ∈ P ⊔ closure ({a, b} : Set G), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
  have hPN : P ≤ Subgroup.normalizer (Q : Set G) := fun p hp =>
    Subgroup.mem_normalizer_fintype fun n hn => hP p hp n hn
  have haN : a ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.mem_normalizer_fintype fun n hn => ha n hn
  have hbN : b ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.mem_normalizer_fintype fun n hn => hb n hn
  have hclN : closure ({a, b} : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      exacts [haN, hbN]
  have hsupN : P ⊔ closure ({a, b} : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hPN hclN
  intro g hg q hq
  exact (Subgroup.mem_normalizer_iff.mp (hsupN hg) q).mp hq

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
