module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E2Pair
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E2Sect
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E2SL2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CrossParts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Transfer

theorem sl2_not_isPGroup {F : Type} [Field F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : (2 : F) ≠ 0) : ¬ IsPGroup p SL(2, F) := by
  intro h
  obtain ⟨k, hk⟩ := h (slU * slV)
  exact false_of_pow_six hp hp2 slW_pow_six (slW_pow_three_ne_one h2) hk

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} {a : Γ}

theorem closure_pair_generates {Γ : Type} [Group Γ] (a b : Γ) :
    Subgroup.closure ({⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
      ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩} :
        Set ↥(Subgroup.closure ({a, b} : Set Γ))) = ⊤ := by
  have h1 : Subtype.val ⁻¹' ({a, b} : Set Γ) =
      ({⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
        ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩} :
          Set ↥(Subgroup.closure ({a, b} : Set Γ))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
    · rintro (h | h)
      · left; rw [h]
      · right; rw [h]
  rw [← h1]
  exact Subgroup.closure_closure_coe_preimage

theorem exists_smaller_pair (hf : Hyp89 p ρ K a) {k : Γ} {J : Subgroup Γ}
    (haJ : a ∈ J) (hbJ : k * a * k⁻¹ ∈ J) (hJle : J ≤ K ⊔ zpowers a)
    (hgen : Subgroup.closure ({⟨a, haJ⟩, ⟨k * a * k⁻¹, hbJ⟩} : Set ↥J) = ⊤)
    (N : Subgroup ↥J) [N.Normal] {F : Type} [Field F] [Finite F] (e : (↥J ⧸ N) ≃* SL(2, F))
    (hF : (∃ n : ℕ, 2 ≤ n ∧ Nat.card F = p ^ n) ∨ (p = 3 ∧ Nat.card F = 5)) :
    ∃ k' ∈ K, ¬ IsPGroup p ↥(Subgroup.closure ({a, k' * a * k'⁻¹} : Set Γ)) ∧
      Nat.card ↥(Subgroup.closure ({a, k' * a * k'⁻¹} : Set Γ)) < Nat.card ↥J := by
  classical
  have : Fact p.Prime := ⟨hf.prime⟩
  set b : Γ := k * a * k⁻¹ with hb
  let a' : ↥J := ⟨a, haJ⟩
  let b' : ↥J := ⟨b, hbJ⟩
  let π : ↥J →* ↥J ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hapow : a' ^ p = 1 := Subtype.ext (by simpa using hf.pow_prime)
  have hbpow : b' ^ p = 1 := Subtype.ext (by
    show b ^ p = 1
    rw [hb, conj_pow, hf.pow_prime, mul_one, mul_inv_cancel])
  have hxp : π a' ^ p = 1 := by rw [← map_pow, hapow, map_one]
  have h2F : (2 : F) ≠ 0 := by
    intro h
    have hc : ∃ q : ℕ, q.Prime ∧ CharP F q := by
      obtain ⟨q, hq⟩ := CharP.exists F
      exact ⟨q, CharP.char_is_prime F q, hq⟩
    obtain ⟨q, hq, hqF⟩ := hc
    have h2q : q ∣ 2 := (CharP.cast_eq_zero_iff F q 2).mp (by simpa using h)
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2q
    subst hq2
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨m, hm, hFm⟩ := FiniteField.card F 2
    have hcard : Nat.card F = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hFm]
    rcases hF with ⟨n, hn, hFn⟩ | ⟨-, hF5⟩
    · have hpd : p ∣ 2 ^ (m : ℕ) := by
        rw [← hcard, hFn]
        exact dvd_pow_self p (by omega)
      have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow hpd)
      exact hf.odd this
    · rw [hF5] at hcard
      have : (2 : ℕ) ∣ 5 := by
        rw [hcard]
        exact dvd_pow_self 2 m.ne_zero
      omega
  have hx1 : π a' ≠ 1 := by
    intro h1
    apply sl2_not_isPGroup (F := F) hf.prime hf.odd h2F
    have hclos : Subgroup.closure ({π a', π b'} : Set (↥J ⧸ N)) = ⊤ := by
      have := congrArg (Subgroup.map π) hgen
      rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top_of_surjective _ hπ] at this
      exact this
    have hbp : π b' ^ p = 1 := by rw [← map_pow, hbpow, map_one]
    have hP : IsPGroup p (↥J ⧸ N) := by
      have h3 : IsPGroup p ↥(Subgroup.closure ({1, π b'} : Set (↥J ⧸ N))) :=
        isPGroup_closure_one_pair_of_pow hf.prime hbp
      rw [h1] at hclos
      rw [hclos] at h3
      exact h3.of_equiv Subgroup.topEquiv
    exact hP.of_equiv e
  obtain ⟨z, hz1, hz2⟩ := exists_proper_pair_sl2 hf.prime hf.odd hF e hx1 hxp
  obtain ⟨j', rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨i, k₀, hk₀, hj⟩ := mem_sup_zpowers_decomp hf.norm (hJle j'.2)
  have hk' : a ^ i * k₀ * a ^ (-i) ∈ K := by
    have h1 : a ^ i ∈ normalizer (K : Set Γ) := Subgroup.zpow_mem _ hf.norm i
    have := (Subgroup.mem_normalizer_iff.mp h1 k₀).mp hk₀
    simpa [zpow_neg] using this
  have hconj : (j' : Γ) * a * (j' : Γ)⁻¹ =
      (a ^ i * k₀ * a ^ (-i)) * a * (a ^ i * k₀ * a ^ (-i))⁻¹ := by
    rw [hj]
    simp only [zpow_neg, mul_inv_rev, inv_inv]
    group
  refine ⟨a ^ i * k₀ * a ^ (-i), hk', ?_⟩
  set k' : Γ := a ^ i * k₀ * a ^ (-i) with hk'def
  set Q : Subgroup ↥J := Subgroup.closure ({a', j' * a' * j'⁻¹} : Set ↥J) with hQ
  have hQmap : Q.map J.subtype = Subgroup.closure ({a, k' * a * k'⁻¹} : Set Γ) := by
    rw [hQ, MonoidHom.map_closure, Set.image_pair]
    have : J.subtype (j' * a' * j'⁻¹) = k' * a * k'⁻¹ := by
      rw [← hconj]
      rfl
    rw [this]
    rfl
  have hQπ : Q.map π = Subgroup.closure ({π a', QuotientGroup.mk j' * π a' *
      (QuotientGroup.mk j')⁻¹} : Set (↥J ⧸ N)) := by
    rw [hQ, MonoidHom.map_closure, Set.image_pair, map_mul, map_mul, map_inv]
    rfl
  have hQtop : Q ≠ ⊤ := by
    intro h
    apply hz1
    rw [← hQπ, h, Subgroup.map_top_of_surjective _ hπ]
  have hcardQ : Nat.card Q < Nat.card ↥J := by
    have hdvd : Nat.card Q ∣ Nat.card ↥J := Subgroup.card_subgroup_dvd_card Q
    have hle : Nat.card Q ≤ Nat.card ↥J := Nat.le_of_dvd Nat.card_pos hdvd
    refine lt_of_le_of_ne hle fun h => hQtop ?_
    exact (Subgroup.card_eq_iff_eq_top Q).mp h
  have hcardJ' : Nat.card ↥(Subgroup.closure ({a, k' * a * k'⁻¹} : Set Γ)) = Nat.card Q := by
    rw [← hQmap]
    exact Nat.card_congr (Q.equivMapOfInjective J.subtype J.subtype_injective).symm.toEquiv
  refine ⟨?_, by rw [hcardJ']; exact hcardQ⟩
  intro hP
  apply hz2
  have hQp : IsPGroup p ↥Q := by
    rw [← hQmap] at hP
    exact hP.of_equiv (Q.equivMapOfInjective J.subtype J.subtype_injective).symm
  rw [← hQπ]
  exact hQp.map π

end Transfer

section Main


theorem crossE2_thm : CrossE2 := by
  classical
  intro p Γ _ _ V _ _ _ ρ K a hf
  have : Fact p.Prime := ⟨hf.prime⟩
  obtain ⟨k₀, hk₀, hJ₀⟩ := exists_nonPGroup_pair hf
  have hex : ∃ m : ℕ, ∃ k ∈ K, ¬ IsPGroup p ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) ∧
      Nat.card ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) = m :=
    ⟨_, k₀, hk₀, hJ₀, rfl⟩
  obtain ⟨k, hk, hJ, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ k' ∈ K, ¬ IsPGroup p ↥(Subgroup.closure ({a, k' * a * k'⁻¹} : Set Γ)) →
      Nat.card ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) ≤
        Nat.card ↥(Subgroup.closure ({a, k' * a * k'⁻¹} : Set Γ)) := by
    intro k' hk' hJ'
    rw [hcard]
    exact Nat.find_min' hex ⟨k', hk', hJ', rfl⟩
  refine ⟨k, hk, hJ, hmin, ?_⟩
  obtain ⟨N, hN, -, F, _, _, hFcard, ⟨e⟩⟩ := sl2Quot_of_nonPGroup_pair hf hJ
  refine ⟨N, hN, ?_⟩
  have haJ : a ∈ Subgroup.closure ({a, k * a * k⁻¹} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbJ : k * a * k⁻¹ ∈ Subgroup.closure ({a, k * a * k⁻¹} : Set Γ) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hJle : Subgroup.closure ({a, k * a * k⁻¹} : Set Γ) ≤ K ⊔ zpowers a := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) (Subgroup.inv_mem _
          (Subgroup.mem_sup_left hk))
  have hgen := closure_pair_generates a (k * a * k⁻¹)
  rcases hFcard with ⟨n, hn, hFn⟩ | hF5
  · by_cases hn1 : n = 1
    · subst hn1
      refine ⟨F, inferInstance, inferInstance, by rw [hFn, pow_one], ⟨e.trans
        (specialLinearGroupEquivStatedSL 2 F)⟩⟩
    · exfalso
      obtain ⟨k', hk', hJ', hlt⟩ := exists_smaller_pair hf haJ hbJ hJle hgen N e
        (Or.inl ⟨n, by omega, hFn⟩)
      exact absurd (hmin k' hk' hJ') (not_le.mpr hlt)
  · exfalso
    obtain ⟨k', hk', hJ', hlt⟩ := exists_smaller_pair hf haJ hbJ hJle hgen N e (Or.inr hF5)
    exact absurd (hmin k' hk' hJ') (not_le.mpr hlt)

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
