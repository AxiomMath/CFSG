module

public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Norm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open

theorem apply_mem_closure_mul_inv_of_mem_normalizer {V : Type*} [Group V] {Q : Subgroup (MulAut V)}
    {p : MulAut V} (hp : p ∈ normalizer (Q : Set (MulAut V))) {r : V}
    (hr : r ∈ Subgroup.closure {u : V | ∃ q ∈ Q, ∃ w : V, u = q w * w⁻¹}) :
    p r ∈ Subgroup.closure {u : V | ∃ q ∈ Q, ∃ w : V, u = q w * w⁻¹} := by
  induction hr using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨q, hq, w, rfl⟩ := hu
    refine Subgroup.subset_closure ⟨p * q * p⁻¹, (mem_normalizer_iff.1 hp q).1 hq, p w, ?_⟩
    rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem odd_eq_bot_of_fixed {V : Type*} [Group V] [Finite V] (hVc : ∀ a b : V, a * b = b * a)
    (hV2 : ∀ v : V, v * v = 1) (Q P : Subgroup (MulAut V)) (hQ : Odd (Nat.card Q))
    (hP : IsPGroup 2 P) (hPQ : P ≤ normalizer (Q : Set (MulAut V)))
    (hfix : ∀ v : V, (∀ p ∈ P, p v = v) → ∀ q ∈ Q, q v = v) : Q = ⊥ := by
  set R : Subgroup V := Subgroup.closure {u : V | ∃ q ∈ Q, ∃ w : V, u = q w * w⁻¹}
  by_cases hRb : R = ⊥
  ·
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    ext w
    have h : q w * w⁻¹ ∈ R := Subgroup.subset_closure ⟨q, hq, w, rfl⟩
    rw [hRb, Subgroup.mem_bot, mul_inv_eq_one] at h
    rw [MulAut.one_apply]
    exact h
  ·
    exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : MulAction P R :=
      { smul := fun p r => ⟨(p : MulAut V) r, apply_mem_closure_mul_inv_of_mem_normalizer (hPQ p.2) r.2⟩
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl }
    have h2R : IsPGroup 2 R := fun r => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hV2 r)⟩
    have hdvd : 2 ∣ Nat.card R :=
      h2R.card_eq_or_dvd.resolve_left fun h => hRb (Subgroup.card_eq_one.1 h)
    have h1 : (1 : R) ∈ MulAction.fixedPoints P R := fun p => Subtype.ext (map_one (p : MulAut V))
    obtain ⟨b, hb, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point R hdvd h1
    have hbP : ∀ p ∈ P, p (b : V) = b := fun p hp => congrArg Subtype.val (hb ⟨p, hp⟩)
    exact hne (Subtype.ext (fixed_commutator_eq_one hVc hV2 Q hQ (hfix b hbP) b.2).symm)

theorem eq_of_odd_free {Γ : Type*} [Group Γ] [Finite Γ] {D C₀ W : Subgroup Γ}
    (hSyl : fusionIsSylowIn 2 W C₀) (hWD : W ≤ D) (hDC : D ≤ C₀)
    (hfree : ∀ c ∈ D, ∀ p : ℕ, p.Prime → p ≠ 2 → orderOf c = p → c = 1) : D = W := by
  refine hSyl.2.2 D hDC (IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)) hWD
  intro p hp hpd
  by_contra hp2
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpd
  have h1 : (g : Γ) = 1 := hfree g g.2 p hp hp2 ((Subgroup.orderOf_coe g).trans hg)
  rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hg
  exact hp.one_lt.ne hg

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
