module

public import CFSG.GroupTheory.CoprimeQuotientNormalizer

public section

namespace CFSG.GroupTheory.SteinbergBS

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {N : Subgroup G} [N.Normal]

omit [N.Normal] in
theorem inf_eq_bot_of_isPGroup_of_not_dvd (hN : ¬ p ∣ Nat.card N) {Q : Subgroup G}
    (hQ : IsPGroup p Q) : Q ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxN⟩ := mem_inf.1 hx
  obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
  have h1 : orderOf x ∣ p ^ k := by
    rw [← orderOf_mk x hxQ]
    exact orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card N := by
    rw [← orderOf_mk x hxN]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)
  rw [mem_bot, ← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hcop h1 h2

theorem injective_mk'_comp_subtype (hN : ¬ p ∣ Nat.card N) {Q : Subgroup G}
    (hQ : IsPGroup p Q) : Function.Injective ((QuotientGroup.mk' N).comp Q.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff (x : G)).1 hx
  have h := mem_inf.2 ⟨x.2, hxN⟩
  rw [inf_eq_bot_of_isPGroup_of_not_dvd hN hQ, mem_bot] at h
  exact Subtype.ext h

theorem centralizer_map_mk'_eq [Finite G] (hN : ¬ p ∣ Nat.card N) {Q : Subgroup G}
    (hQ : IsPGroup p Q) :
    centralizer ((Q.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
      (centralizer (Q : Set G)).map (QuotientGroup.mk' N) := by
  have hinj := injective_mk'_comp_subtype hN hQ
  have hnorm := normal_coprime_quotient_normalizer p N hN Q hQ
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hgN := centralizer_le_normalizer _ hx
    rw [← hnorm] at hgN
    obtain ⟨h, hh, hhg⟩ := hgN
    refine ⟨h, mem_centralizer_iff.2 fun y hy => ?_, hhg⟩
    have hhy : h * y * h⁻¹ ∈ Q := (mem_normalizer_iff.1 hh y).1 hy
    have hc := mem_centralizer_iff.1 hx (QuotientGroup.mk' N y) (mem_map_of_mem _ hy)
    have heq : (QuotientGroup.mk' N).comp Q.subtype ⟨h * y * h⁻¹, hhy⟩ =
        (QuotientGroup.mk' N).comp Q.subtype ⟨y, hy⟩ := by
      change QuotientGroup.mk' N (h * y * h⁻¹) = QuotientGroup.mk' N y
      rw [map_mul, map_mul, map_inv, hhg, ← hc, mul_inv_cancel_right]
    have h4 : h * y * h⁻¹ = y := congrArg Subtype.val (hinj heq)
    calc y * h = h * y * h⁻¹ * h := by rw [h4]
      _ = h * y := by group
  · rw [coe_map]
    exact map_centralizer_le_centralizer_image _ _

theorem prime_to_p_quotient_normalizer_centralizer_lifting [Finite G] (hN : ¬ p ∣ Nat.card N)
    {Q : Subgroup G} (hQ : IsPGroup p Q) :
    Function.Injective ((QuotientGroup.mk' N).comp Q.subtype) ∧
      normalizer ((Q.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
        (normalizer (Q : Set G)).map (QuotientGroup.mk' N) ∧
      centralizer ((Q.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
        (centralizer (Q : Set G)).map (QuotientGroup.mk' N) :=
  ⟨injective_mk'_comp_subtype hN hQ, (normal_coprime_quotient_normalizer p N hN Q hQ).symm,
    centralizer_map_mk'_eq hN hQ⟩

end CFSG.GroupTheory.SteinbergBS
