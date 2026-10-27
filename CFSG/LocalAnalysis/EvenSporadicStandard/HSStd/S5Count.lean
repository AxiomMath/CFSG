module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

theorem card_subtype_comp_surj {A B : Type*} [Group A] [Group B] [Finite A] (g : A →* B)
    (hg : Function.Surjective g) (p : B → Prop) :
    Nat.card {a : A // p (g a)} = Nat.card g.ker * Nat.card {b : B // p b} := by
  classical
  have : Finite B := Finite.of_surjective g hg
  have : Fintype A := Fintype.ofFinite A
  have : Fintype B := Fintype.ofFinite B
  have hfib : ∀ b : B, Fintype.card {a : A // g a = b} = Nat.card g.ker := by
    intro b
    obtain ⟨a₀, rfl⟩ := hg b
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ?_
    exact
      { toFun := fun a => ⟨a₀⁻¹ * a.1, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, a.2, inv_mul_cancel]⟩
        invFun := fun k => ⟨a₀ * k.1, by
          rw [map_mul, MonoidHom.mem_ker.1 k.2, mul_one]⟩
        left_inv := fun a => by ext; simp
        right_inv := fun k => by ext; simp }
  have h1 : Nat.card {a : A // p (g a)} =
      ∑ b ∈ Finset.univ.filter p, Fintype.card {a : A // g a = b} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ.filter p)
      (fun a ha => by simpa using ha)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Fintype.card_subtype]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [h]; simpa using hb, h⟩
  have h2 : Nat.card {b : B // p b} = (Finset.univ.filter p).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, Finset.sum_congr rfl fun b _ => hfib b, Finset.sum_const, smul_eq_mul, mul_comm, h2]

theorem card_subtype_comp {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B) (q : B → Prop) :
    Nat.card {a : A // q (f a)} = Nat.card f.ker * Nat.card {b : f.range // q b.1} := by
  have := card_subtype_comp_surj f.rangeRestrict f.rangeRestrict_surjective (fun b => q b.1)
  simpa [MonoidHom.ker_rangeRestrict] using this

theorem card_sq_eq_conj {G : Type*} [Group G] (S : Subgroup G) {n : G}
    (hn : n ∈ normalizer (S : Set G)) (a : G) :
    Nat.card {x : S // (x : G) * x = a} = Nat.card {x : S // (x : G) * x = n * a * n⁻¹} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (S.normalizerMonoidHom ⟨n, hn⟩).toEquiv ?_)
  intro x
  have h1 : ((S.normalizerMonoidHom ⟨n, hn⟩ x : S) : G) = n * x * n⁻¹ := rfl
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1]
  have : n * (x : G) * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
  rw [this]
  constructor
  · rintro rfl; rfl
  · intro h
    have := mul_left_cancel (mul_right_cancel h)
    exact this

end CFSG.EvenSporadicStandard.HSStd
