module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.A8Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.LineGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.TableAt

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open Equiv Equiv.Perm CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem A8Emb.orderOf_φ_eq_prime (E : A8Emb a z) {u : alternatingGroup (Fin 8)} {p : ℕ}
    [Fact p.Prime] (h : u ^ p = 1) (h1 : u ≠ 1) : orderOf (E.φ u) = p := by
  rw [E.orderOf_φ]
  exact orderOf_eq_prime h h1

theorem A8Emb.orderOf_φ_eq_six (E : A8Emb a z) {u : alternatingGroup (Fin 8)} (h6 : u ^ 6 = 1)
    (h2 : u ^ 2 ≠ 1) (h3 : u ^ 3 ≠ 1) : orderOf (E.φ u) = 6 := by
  rw [E.orderOf_φ]
  exact orderOf_eq_six h6 h2 h3

theorem A8Emb.mem_orb4B (E : A8Emb a z) {β ξ : alternatingGroup (Fin 8)} (hξ : TT ξ)
    (h : TT ((β * ξ) ^ 2)) : E.φ ξ ∈ orb4B a (E.φ β) :=
  ⟨E.isConj_a hξ, by rw [← map_mul, ← map_pow]; exact E.isConj_a h⟩

theorem A8Emb.mem_orb6A (E : A8Emb a z) {β ξ : alternatingGroup (Fin 8)} (hξ : TT ξ)
    (h6 : (β * ξ) ^ 6 = 1) (h2 : (β * ξ) ^ 2 ≠ 1) (h3 : (β * ξ) ^ 3 ≠ 1)
    (hc : TT ((β * ξ) ^ 3)) : E.φ ξ ∈ orb6A a (E.φ β) := by
  refine ⟨E.isConj_a hξ, ?_, ?_⟩
  · rw [← map_mul]
    exact E.orderOf_φ_eq_six h6 h2 h3
  · rw [← map_mul, ← map_pow]
    exact E.isConj_a hc

theorem A8Emb.mem_oddSet (E : A8Emb a z) {β ξ : alternatingGroup (Fin 8)} (hξ : TT ξ)
    (hne : ξ ≠ β) (hodd : Odd (orderOf (β * ξ))) : E.φ ξ ∈ oddSet a (E.φ β) := by
  refine ⟨E.isConj_a hξ, fun h => hne (E.injective h), ?_, a, IsConj.refl a, ?_⟩
  · rw [← map_mul, E.orderOf_φ]
    exact hodd
  · exact mem_Gxy.2 ⟨mem_Gx.2 (E.comm β).symm, mem_Gx.2 (E.comm ξ).symm⟩

theorem A8Emb.mem_orb5A (E : A8Emb a z) (hL : F5Local G a z) {β ξ s : alternatingGroup (Fin 8)}
    (hβ : TT β) (hξ : TT ξ) (hne : ξ ≠ β) (h5 : (β * ξ) ^ 5 = 1) (h1 : β * ξ ≠ 1)
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (hsβ : s * β = β * s) (hsξ : s * ξ = ξ * s) :
    E.φ ξ ∈ orb5A a (E.φ β) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho5 : orderOf (β * ξ) = 5 := orderOf_eq_prime h5 h1
  have hodd : Odd (orderOf (β * ξ)) := by rw [ho5]; decide
  refine mem_orb5A_of_exists_order_three hL (E.isConj_a hβ) (E.mem_oddSet hξ hne hodd)
    (by rw [← map_mul, E.orderOf_φ, ho5]) ⟨E.φ s, ?_, E.orderOf_φ_eq_prime hs3 hs1⟩
  refine mem_Gxy.2 ⟨mem_Gx.2 ?_, mem_Gx.2 ?_⟩
  · rw [← map_mul, ← map_mul, hsβ]
  · rw [← map_mul, ← map_mul, hsξ]

theorem A8Emb.a_mul_a_mul (E : A8Emb a z) (hF : IsF5Type a z) (u w : alternatingGroup (Fin 8)) :
    (a * E.φ u) * (a * E.φ w) = E.φ (u * w) := by
  have haa : a * a = 1 := mul_self_of_isConj hF (IsConj.refl a)
  calc a * E.φ u * (a * E.φ w) = a * (E.φ u * a) * E.φ w := by group
    _ = a * (a * E.φ u) * E.φ w := by rw [← E.comm u]
    _ = (a * a) * E.φ u * E.φ w := by group
    _ = E.φ (u * w) := by rw [haa, one_mul, map_mul]

theorem A8Emb.vertex_mul_a_mul (E : A8Emb a z) (β t : alternatingGroup (Fin 8)) :
    E.φ β * (a * E.φ t) = a * E.φ (β * t) := by
  rw [map_mul, ← mul_assoc, ← E.comm β, mul_assoc]

theorem A8Emb.sq_a_mul (E : A8Emb a z) (hF : IsF5Type a z) (u : alternatingGroup (Fin 8)) :
    (a * E.φ u) ^ 2 = E.φ (u ^ 2) := by
  rw [sq, E.a_mul_a_mul hF, ← sq]

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
