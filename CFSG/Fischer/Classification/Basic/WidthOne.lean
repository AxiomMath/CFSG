module

public import CFSG.Fischer.Classification.Basic.Small
public import CFSG.Fischer.Classification.Basic.Center
public import CFSG.LocalAnalysis.ZStar
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X : Type} [Group X] {E : Set X}

section Solvable

theorem eq_bot_of_isSolvable (hZ : Subgroup.center X = ⊥) (hs : IsSimpleGroup (commutator X))
    (hna : ¬ ∀ a b : commutator X, a * b = b * a) {N : Subgroup X} [N.Normal]
    (hN : Group.IsSolvable N) : N = ⊥ := by
  by_contra hne
  have hle := commutator_le_of_normal hZ hs hne
  have : Group.IsSolvable (commutator X) := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  exact hna (IsSimpleGroup.comm_iff_isSolvable.2 this)

end Solvable

section WidthOne

theorem Pair.exists_ne_commute (hP : Pair X E) (hs : IsSimpleGroup (commutator X))
    (hna : ¬ ∀ a b : commutator X, a * b = b * a) :
    ∃ d ∈ E, ∃ e ∈ E, d ≠ e ∧ d * e = e * d := by
  by_contra! hall
  have := Pair.finite hP
  let := Fintype.ofFinite X
  obtain ⟨d, hd⟩ := Pair.nonempty hP
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar X d (Pair.ne_one hP hd)
    (Pair.mul_self hP hd) fun g hg => by
      by_contra hne
      exact hall _ (Pair.conj_mem hP hd g) d hd hne hg
  have := hNn
  have hEN : ∀ e ∈ E, ∀ f ∈ E, f * e⁻¹ ∈ N := by
    intro e he f hf
    obtain ⟨a, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
    obtain ⟨b, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd hf)
    have := N.mul_mem (hN b) (N.inv_mem (hN a))
    rwa [show b * d * b⁻¹ * d⁻¹ * (a * d * a⁻¹ * d⁻¹)⁻¹ = b * d * b⁻¹ * (a * d * a⁻¹)⁻¹ by
      group] at this
  have hle := Pair.commutator_le_of_forall hP hEN
  have hsolN : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have : Group.IsSolvable (commutator X) := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  exact hna (IsSimpleGroup.comm_iff_isSolvable.2 this)

end WidthOne

section Abelian

theorem isSwap_iff_orderOf_eq_two (σ : Equiv.Perm (Fin 3)) : σ.IsSwap ↔ orderOf σ = 2 := by
  have key : ∀ τ : Equiv.Perm (Fin 3), τ.support.card = 2 ↔ (τ ≠ 1 ∧ τ * τ = 1) := by decide
  rw [← Equiv.Perm.card_support_eq_two, key]
  constructor
  · rintro ⟨h1, h2⟩
    exact orderOf_eq_prime (by rw [sq, h2]) h1
  · intro h
    refine ⟨fun h1 => ?_, by rw [← sq, ← h, pow_orderOf_eq_one]⟩
    rw [h1, orderOf_one] at h
    exact absurd h (by norm_num)

theorem Pair.exists_mulEquiv_perm_three (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hs : IsSimpleGroup (commutator X)) (hab : ∀ a b : commutator X, a * b = b * a) :
    ∃ φ : X ≃* Equiv.Perm (Fin 3), ∀ g, g ∈ E ↔ (φ g).IsSwap := by
  have := Pair.finite hP
  set K := commutator X with hKdef
  obtain ⟨d, hd, e, he, hde⟩ := Pair.exists_not_commute hP hZ
  obtain ⟨hne, hded, hdede, -⟩ := Pair.line_ne hP hd he hde
  have hxK : d * e ∈ K := by
    have := Pair.mul_inv_mem_commutator hP he hd
    rwa [Pair.inv_eq hP he] at this
  have hx3 : orderOf (d * e) = 3 := Pair.orderOf_mul_eq_three hP hd he hde
  have hKcard : Nat.card K = 3 := by
    have : IsMulCommutative K := ⟨⟨hab⟩⟩
    have hp : (Nat.card K).Prime := Group.is_simple_iff_prime_card.1 hs
    have hx3' : orderOf (⟨d * e, hxK⟩ : K) = 3 := by rw [← Subgroup.orderOf_coe]; exact hx3
    have hdvd : 3 ∣ Nat.card K := hx3' ▸ orderOf_dvd_natCard _
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hdvd).symm
  have hKz : Subgroup.zpowers (d * e) = K := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hxK) ?_
    rw [Nat.card_zpowers, hx3, hKcard]
  have hidx : K.index = 2 := by
    have h1 : K.index ≤ 2 := Pair.index_commutator_le_two hP
    have h2 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h3 : K.index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      apply hde
      have := hab ⟨d, htop ▸ Subgroup.mem_top d⟩ ⟨e, htop ▸ Subgroup.mem_top e⟩
      exact congrArg Subtype.val this
    omega
  have hXcard : Nat.card X = 6 := by rw [← Subgroup.card_mul_index K, hKcard, hidx]
  have hcoset : ∀ g : X, g * d ∈ K → g = d ∨ g = d * e * d ∨ g = e := by
    intro g hg
    rw [← hKz] at hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hmod : (d * e) ^ (k % 3) = (d * e) ^ k := by
      have := zpow_mod_orderOf (d * e) k
      rwa [hx3, Nat.cast_ofNat] at this
    have hg' : g = (d * e) ^ (k % 3) * d := by
      rw [hmod, hk, mul_assoc, Pair.mul_self hP hd, mul_one]
    have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hr with h | h | h <;> rw [h] at hg'
    · left
      simpa using hg'
    · right; left
      simpa using hg'
    · right; right
      rw [hg']
      calc (d * e) ^ (2 : ℤ) * d = d * e * d * e * d := by rw [zpow_two]; simp only [mul_assoc]
        _ = e * d * e * e * d := by rw [Pair.mul_mul_eq hP hd he hde]
        _ = e := by
          rw [mul_assoc (e * d) e e, Pair.mul_self hP he, mul_one, mul_assoc,
            Pair.mul_self hP hd, mul_one]
  have hnotK : ∀ g : X, orderOf g = 2 → g ∉ K := by
    intro g hg hgK
    have h3 : orderOf (⟨g, hgK⟩ : K) ∣ 3 := hKcard ▸ orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe] at h3
    change orderOf g ∣ 3 at h3
    rw [hg] at h3
    exact absurd h3 (by norm_num)
  have hE : ∀ g, g ∈ E ↔ orderOf g = 2 := by
    intro g
    refine ⟨Pair.orderOf_eq_two hP, fun hg => ?_⟩
    have hgd : g * d ∈ K := (Subgroup.mul_mem_iff_of_index_two hidx).2
      (iff_of_false (hnotK g hg) (hnotK d (Pair.orderOf_eq_two hP hd)))
    rcases hcoset g hgd with rfl | rfl | rfl
    · exact hd
    · exact Pair.mul_mul_mem hP hd he
    · exact he
  have hEcard : Nat.card E = 3 := by
    have hset : E = {d, d * e * d, e} := by
      ext g
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hg
        have := Pair.mul_inv_mem_commutator hP hd hg
        rw [Pair.inv_eq hP hd] at this
        exact hcoset g this
      · rintro (rfl | rfl | rfl)
        · exact hd
        · exact Pair.mul_mul_mem hP hd he
        · exact he
    rw [Nat.card_coe_set_eq, Set.ncard_eq_three]
    exact ⟨d, d * e * d, e, hded.symm, hne, hdede, hset⟩
  have hbij : Function.Bijective (Pair.conjPerm hP) :=
    (Pair.conjPerm_injective hP hZ).bijective_of_nat_card_le (by
      rw [Nat.card_perm, hEcard, hXcard]
      decide)
  let φ : X ≃* Equiv.Perm (Fin 3) := (MulEquiv.ofBijective (Pair.conjPerm hP) hbij).trans
    (Equiv.permCongrHom ((Finite.equivFin E).trans (finCongr hEcard)))
  refine ⟨φ, fun g => ?_⟩
  rw [hE g, isSwap_iff_orderOf_eq_two, MulEquiv.orderOf_eq]

end Abelian

end CFSG.Fischer.Classification
