module

import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCentralExt
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCentralExtOne
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSevenPrime
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2

namespace AltCentralExtThree

theorem exists_lift_pow_three_eq_one {J A : Type*} [Group J] [Group A] (ψ : J →* A)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J) {a g : A}
    (ha : a ^ 3 = 1) (hg : g * a * g⁻¹ = a⁻¹) : ∃ x : J, ψ x = a ∧ x ^ 3 = 1 := by
  obtain ⟨x₀, rfl⟩ := hψ a
  obtain ⟨w, rfl⟩ := hψ g
  have hzk : x₀ ^ 3 ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow]; exact ha
  have huk : x₀ * (w * x₀ * w⁻¹) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hg]
    exact mul_inv_cancel _
  have hconj : w * x₀ * w⁻¹ = x₀⁻¹ * (x₀ * (w * x₀ * w⁻¹)) := (inv_mul_cancel_left _ _).symm
  have hzz : x₀ ^ 3 * x₀ ^ 3 = (x₀ * (w * x₀ * w⁻¹)) ^ 3 := by
    have h1 : w * x₀ ^ 3 * w⁻¹ = x₀ ^ 3 := by
      rw [Subgroup.mem_center_iff.1 (hker hzk) w, mul_inv_cancel_right]
    have h2 : (w * x₀ * w⁻¹) ^ 3 = x₀⁻¹ ^ 3 * (x₀ * (w * x₀ * w⁻¹)) ^ 3 := by
      conv_lhs => rw [hconj]
      exact Commute.mul_pow (Subgroup.mem_center_iff.1 (hker huk) x₀⁻¹) 3
    rw [conj_pow, h1, inv_pow] at h2
    exact eq_inv_mul_iff_mul_eq.1 h2
  have hvk : x₀ ^ 3 * (x₀ * (w * x₀ * w⁻¹))⁻¹ ∈ ψ.ker := mul_mem hzk (inv_mem huk)
  have hv : (x₀ ^ 3 * (x₀ * (w * x₀ * w⁻¹))⁻¹) ^ 3 = x₀ ^ 3 := by
    rw [Commute.mul_pow (Subgroup.mem_center_iff.1 (hker (inv_mem huk)) (x₀ ^ 3)) 3, inv_pow,
      ← hzz]
    group
  refine ⟨x₀ * (x₀ ^ 3 * (x₀ * (w * x₀ * w⁻¹))⁻¹)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, MonoidHom.mem_ker.1 hvk, inv_one, mul_one]
  · rw [Commute.mul_pow (Subgroup.mem_center_iff.1 (hker (inv_mem hvk)) x₀) 3, inv_pow, hv]
    group

theorem exists_commuting_lifts {J : Type*} [Group J] {n : ℕ} (ψ : J →* alternatingGroup (Fin n))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J) (h3 : IsPGroup 3 ψ.ker)
    (c : Fin 3 → alternatingGroup (Fin n)) (hc : ∀ i, (c i : Equiv.Perm (Fin n)).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (c i : Equiv.Perm (Fin n)).support (c j : Equiv.Perm (Fin n)).support) :
    ∃ x : Fin 3 → J, (∀ i, ψ (x i) = c i) ∧ (∀ i, x i ^ 3 = 1) ∧ ∀ i j, Commute (x i) (x j) := by
  have hpow3 : ∀ i, c i ^ 3 = 1 := fun i => by
    have := pow_orderOf_eq_one (c i : Equiv.Perm (Fin n))
    rw [(hc i).orderOf] at this
    exact Subtype.ext this
  have hdisj' : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (c i : Equiv.Perm (Fin n)) (c j) :=
    fun i j hij => Equiv.Perm.disjoint_iff_disjoint_support.2 (hdisj i j hij)
  have hlift : ∀ i, ∃ x : J, ψ x = c i ∧ x ^ 3 = 1 := by
    intro i
    obtain ⟨j, k, hji, hki, hjk⟩ : ∃ j k : Fin 3, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
      revert i; decide
    obtain ⟨g, -, hg⟩ := AltCentralExtOne.exists_inverting_alt (x := c j) (y := c i) (z := c k)
      (hc i) (hc k) (hdisj j i hji) (hdisj j k hjk) (hdisj i k hki.symm)
    exact exists_lift_pow_three_eq_one ψ hψ hker (hpow3 i) hg
  choose x hxψ hx3 using hlift
  refine ⟨x, hxψ, hx3, fun i j => ?_⟩
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    revert i j; decide
  obtain ⟨g, hg1, hg2⟩ := AltCentralExtOne.exists_inverting_alt (x := c i) (y := c j) (z := c k)
    (hc j) (hc k) (hdisj i j hij) (hdisj i k hki.symm) (hdisj j k hkj.symm)
  exact AltCentralExt.commute_of_inverted ψ hψ hker h3 (by rw [hxψ]; exact hg1)
    (by rw [hxψ]; exact hg2) (by rw [hxψ, hxψ]; exact Subtype.ext (hdisj' i j hij).commute.eq)

theorem exists_orderOf_eq_three {J A : Type*} [Group J] [Finite J] [Group A] (ψ : J →* A)
    (hker : ψ.ker ≤ Subgroup.center J) (h3 : IsPGroup 3 ψ.ker) (hne : ψ.ker ≠ ⊥) :
    ∃ u : J, ψ u = 1 ∧ orderOf u = 3 ∧ ∀ y : J, Commute y u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ : ∃ u : ψ.ker, orderOf u = 3 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 h3
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq _ (by simpa using hm))
    exact exists_prime_orderOf_dvd_card' 3 (by rw [hm]; exact dvd_pow_self 3 hm0)
  rw [← Subgroup.orderOf_coe] at hu
  exact ⟨u, u.2, hu, fun y => Subgroup.mem_center_iff.1 (hker u.2) y⟩

section Perm

open Equiv

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem injective_prod_pow_three {c : Fin 3 → Perm α} (hc : ∀ i, (c i).IsThreeCycle)
    (hd : ∀ i j, i ≠ j → Perm.Disjoint (c i) (c j)) :
    Function.Injective fun q : Fin 3 × Fin 3 × Fin 3 =>
      c 0 ^ (q.1 : ℕ) * c 1 ^ (q.2.1 : ℕ) * c 2 ^ (q.2.2 : ℕ) := by
  have hD : ∀ a b : Fin 3, a ≠ b → ∀ m n : ℕ, Perm.Disjoint (c a ^ m) (c b ^ n) :=
    fun a b hab m n => (hd a b hab).pow_disjoint_pow m n
  have hpow : ∀ (m : Fin 3) (a b : Fin 3), c m ^ (a : ℕ) = c m ^ (b : ℕ) → a = b := by
    intro m a b hab
    have := pow_eq_pow_iff_modEq.1 hab
    rw [(hc m).orderOf] at this
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt this a.2 b.2)
  have d2 : ∀ a b d : ℕ, Perm.Disjoint (c 0 ^ a * c 1 ^ b) (c 2 ^ d) := fun a b d =>
    (hD 0 2 (by decide) a d).mul_left (hD 1 2 (by decide) b d)
  have d1 : ∀ a b : ℕ, Perm.Disjoint (c 0 ^ a) (c 1 ^ b) := fun a b => hD 0 1 (by decide) a b
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  obtain ⟨h01, hk⟩ := AltCentralExtOne.eq_of_mul_eq_mul_of_perm_disjoint h (d2 _ _ _) (d2 _ _ _)
    (d2 _ _ _) (d2 _ _ _)
  obtain ⟨hi, hj⟩ := AltCentralExtOne.eq_of_mul_eq_mul_of_perm_disjoint h01 (d1 _ _) (d1 _ _)
    (d1 _ _) (d1 _ _)
  exact Prod.ext (hpow 0 _ _ hi) (Prod.ext (hpow 1 _ _ hj) (hpow 2 _ _ hk))

end Perm

universe u

theorem le_pRank_comap_of_central_sylow {J : Type u} [Group J] [Finite J] {A : Type*} [Group A]
    (ψ : J →* A) (hψ : Function.Surjective ψ) (U : Sylow 3 ψ.ker)
    (hU : ∀ u : ψ.ker, u ∈ U → (u : J) ∈ Subgroup.center J) (hUne : (U : Subgroup ψ.ker) ≠ ⊥)
    (Z : Subgroup A) {k : ℕ}
    (H : ∀ (J' : Type u) [Group J'] [Finite J'] (ψ' : J' →* A), Function.Surjective ψ' →
      ψ'.ker ≤ Subgroup.center J' → IsPGroup 3 ψ'.ker → ψ'.ker ≠ ⊥ →
      k ≤ Open.pRank 3 (Z.comap ψ')) :
    k ≤ Open.pRank 3 (Z.comap ψ) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Subgroup.normalizer (U : Subgroup ψ.ker) ≤ Subgroup.centralizer (U : Set ψ.ker) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hU u hu) g.1).symm
  let φ : ψ.ker →* U := MonoidHom.transferSylow U hP
  have hcompl := MonoidHom.ker_transferSylow_isComplement' U hP
  have hO3 : ¬ 3 ∣ Nat.card φ.ker := MonoidHom.not_dvd_card_ker_transferSylow U hP
  let O : Subgroup J := φ.ker.map ψ.ker.subtype
  have hmem : ∀ y : ψ.ker, y ∈ φ.ker ↔ Nat.Coprime (orderOf y) 3 := by
    intro y
    constructor
    · intro hy
      have h1 := Subgroup.orderOf_dvd_natCard φ.ker hy
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => hO3 (h3.trans h1)).symm
    · intro hy
      obtain ⟨k, hk⟩ := U.isPGroup' (φ y)
      have h1 : orderOf (φ y) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
      have h2 : orderOf (φ y) ∣ orderOf y :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hy.symm) h1 h2)
  have hOmem : ∀ x : J, x ∈ O ↔ x ∈ ψ.ker ∧ Nat.Coprime (orderOf x) 3 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by
        change (orderOf (y : J)).Coprime 3
        rw [Subgroup.orderOf_coe]
        exact (hmem y).1 hy⟩
    · rintro ⟨hx, hcop⟩
      refine ⟨⟨x, hx⟩, (hmem ⟨x, hx⟩).2 ?_, rfl⟩
      rw [← Subgroup.orderOf_coe]
      exact hcop
  have hOn : O.Normal := ⟨fun x hx g => by
    rw [hOmem] at hx ⊢
    refine ⟨Subgroup.Normal.conj_mem (MonoidHom.normal_ker ψ) x hx.1 g, ?_⟩
    have := (MulAut.conj g).orderOf_eq x
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hx.2⟩
  have hOker : O ≤ ψ.ker := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let ψ' : J ⧸ O →* A := QuotientGroup.lift O ψ hOker
  have hψ' : Function.Surjective ψ' := by
    intro y
    obtain ⟨g, rfl⟩ := hψ y
    exact ⟨g, QuotientGroup.lift_mk O hOker g⟩
  have hform : ∀ q ∈ ψ'.ker, ∃ u : ψ.ker, u ∈ U ∧ q = (QuotientGroup.mk (u : J) : J ⧸ O) := by
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.lift_mk O hOker g).symm.trans hq
    obtain ⟨⟨⟨o, ho⟩, ⟨u, hu⟩⟩, hou, -⟩ :=
      (Subgroup.isComplement_iff_existsUnique.1 (Subgroup.isComplement'_def.1 hcompl)) ⟨g, hg⟩
    refine ⟨u, hu, ?_⟩
    have hgou : g = (o : J) * (u : J) := (congrArg Subtype.val hou).symm
    have hoO : QuotientGroup.mk (o : J) = (1 : J ⧸ O) :=
      (QuotientGroup.eq_one_iff _).2 ⟨o, ho, rfl⟩
    rw [hgou, QuotientGroup.mk_mul, hoO, one_mul]
  have hcenter : ψ'.ker ≤ Subgroup.center (J ⧸ O) := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := hform q hq
    rw [Subgroup.mem_center_iff]
    intro q'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hU u hu) g]
  have hp : IsPGroup 3 ψ'.ker := by
    intro q
    obtain ⟨u, hu, hq⟩ := hform q q.2
    obtain ⟨k, hk⟩ := U.isPGroup' ⟨u, hu⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (u : J) ^ 3 ^ k = 1 := congrArg (fun z : U => ((z : ψ.ker) : J)) hk
    change (q : J ⧸ O) ^ 3 ^ k = 1
    rw [hq, ← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  have hne : ψ'.ker ≠ ⊥ := by
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUne
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    obtain ⟨k, hk⟩ := U.isPGroup' ⟨u, hu⟩
    have h1 : (u : J) ^ 3 ^ k = 1 := congrArg (fun z : U => ((z : ψ.ker) : J)) hk
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨QuotientGroup.mk (u : J), ?_⟩, fun h => ?_⟩
    · rw [MonoidHom.mem_ker]
      exact (QuotientGroup.lift_mk O hOker (u : J)).trans u.2
    · have hO : (u : J) ∈ O := (QuotientGroup.eq_one_iff (u : J)).1 (congrArg Subtype.val h)
      have hord : orderOf (u : J) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k ((hOmem _).1 hO).2)
          (orderOf_dvd_of_pow_eq_one h1)
      exact hu1' (Subtype.ext (orderOf_eq_one_iff.1 hord))
  have h4 := H (J ⧸ O) ψ' hψ' hcenter hp hne
  have hOcard : ¬ 3 ∣ Nat.card (QuotientGroup.mk' O).ker := by
    rwa [QuotientGroup.ker_mk', Subgroup.card_map_of_injective ψ.ker.subtype_injective]
  have hcomp : (Z.comap ψ').comap (QuotientGroup.mk' O) = Z.comap ψ := by
    ext x
    simp only [Subgroup.mem_comap, QuotientGroup.mk'_apply]
    rw [show ψ' (QuotientGroup.mk x) = ψ x from QuotientGroup.lift_mk O hOker x]
  rw [← hcomp]
  exact h4.trans (AltSevenPrime.pRank_le_pRank_comap (QuotientGroup.mk' O)
    (QuotientGroup.mk'_surjective O) hOcard _)

end AltCentralExtThree

theorem four_le_pRank_comap_of_central_three_of_ne_bot {J : Type*} [Group J] [Finite J] {n : ℕ}
    (ψ : J →* alternatingGroup (Fin n)) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center J) (h3 : IsPGroup 3 ψ.ker) (hne : ψ.ker ≠ ⊥)
    (c : Fin 3 → alternatingGroup (Fin n)) (hc : ∀ i, (c i : Equiv.Perm (Fin n)).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (c i : Equiv.Perm (Fin n)).support (c j : Equiv.Perm (Fin n)).support) :
    4 ≤ Open.pRank 3 ((Subgroup.closure (Set.range c)).comap ψ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdisj' : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (c i : Equiv.Perm (Fin n)) (c j) :=
    fun i j hij => Equiv.Perm.disjoint_iff_disjoint_support.2 (hdisj i j hij)
  obtain ⟨x, hxψ, hx3, hcomm⟩ := AltCentralExtThree.exists_commuting_lifts ψ hψ hker h3 c hc hdisj
  obtain ⟨u, huψ, hu_ord, hcen⟩ := AltCentralExtThree.exists_orderOf_eq_three ψ hker h3 hne
  have hu3 : u ^ 3 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu_ord] at this
  let S : Set J := Set.range x ∪ {u}
  have hS : S.Pairwise Commute := by
    rintro _ (⟨i, rfl⟩ | rfl) _ (⟨j, rfl⟩ | rfl) -
    · exact hcomm i j
    · exact hcen _
    · exact (hcen _).symm
    · exact Commute.refl _
  have hgen : ∀ y ∈ S, y ^ 3 = 1 := by
    rintro _ (⟨i, rfl⟩ | rfl)
    · exact hx3 i
    · exact hu3
  have hCH : Subgroup.closure S ≤ (Subgroup.closure (Set.range c)).comap ψ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨i, rfl⟩ | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, hxψ]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, huψ]
      exact one_mem _
  have hSmem : ∀ y ∈ S, y ∈ Subgroup.closure S := fun y hy => Subgroup.subset_closure hy
  have hgenmem : ∀ (i : Fin 3) (e : ℕ), x i ^ e ∈ Subgroup.closure S := fun i e =>
    Subgroup.pow_mem _ (hSmem _ (Or.inl (Set.mem_range_self i))) e
  have humem : ∀ e : ℕ, u ^ e ∈ Subgroup.closure S := fun e =>
    Subgroup.pow_mem _ (hSmem _ (Or.inr rfl)) e
  let ν : Fin 3 × Fin 3 × Fin 3 × Fin 3 → Subgroup.closure S := fun q =>
    ⟨x 0 ^ (q.1 : ℕ) * x 1 ^ (q.2.1 : ℕ) * x 2 ^ (q.2.2.1 : ℕ) * u ^ (q.2.2.2 : ℕ),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hgenmem 0 _) (hgenmem 1 _))
        (hgenmem 2 _)) (humem _)⟩
  have hν : Function.Injective ν := by
    rintro ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩ h
    have h1 : x 0 ^ (i : ℕ) * x 1 ^ (j : ℕ) * x 2 ^ (k : ℕ) * u ^ (l : ℕ) =
        x 0 ^ (i' : ℕ) * x 1 ^ (j' : ℕ) * x 2 ^ (k' : ℕ) * u ^ (l' : ℕ) :=
      congrArg Subtype.val h
    have h2 := congrArg (fun y => ((ψ y : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) h1
    simp only [map_mul, map_pow, hxψ, huψ, one_pow, mul_one, Subgroup.coe_mul,
      Subgroup.coe_pow] at h2
    have h3' := AltCentralExtThree.injective_prod_pow_three
      (c := fun i => (c i : Equiv.Perm (Fin n))) hc hdisj' (a₁ := (i, j, k)) (a₂ := (i', j', k'))
      h2
    obtain ⟨rfl, rfl, rfl⟩ : i = i' ∧ j = j' ∧ k = k' := by
      simpa only [Prod.mk.injEq] using h3'
    have h4 : u ^ (l : ℕ) = u ^ (l' : ℕ) := mul_left_cancel h1
    have h5 := pow_eq_pow_iff_modEq.1 h4
    rw [hu_ord] at h5
    rw [Fin.ext (Nat.ModEq.eq_of_lt_of_lt h5 l.2 l'.2)]
  have hcard : 3 ^ 4 ≤ Nat.card (Subgroup.closure S) := by
    calc 3 ^ 4 = Nat.card (Fin 3 × Fin 3 × Fin 3 × Fin 3) := by simp
      _ ≤ _ := Nat.card_le_card_of_injective ν hν
  exact (AltFiveRankTools.le_pRank_closure_of_pairwise_commute hS hgen hcard).trans
    (SectionRank.pRank_mono (by norm_num) hCH)

theorem four_le_pRank_comap_of_central_sylow_three {J : Type*} [Group J] [Finite J] {n : ℕ}
    (ψ : J →* alternatingGroup (Fin n)) (hψ : Function.Surjective ψ) (U : Sylow 3 ψ.ker)
    (hU : ∀ u : ψ.ker, u ∈ U → (u : J) ∈ Subgroup.center J) (hUne : (U : Subgroup ψ.ker) ≠ ⊥)
    (c : Fin 3 → alternatingGroup (Fin n)) (hc : ∀ i, (c i : Equiv.Perm (Fin n)).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (c i : Equiv.Perm (Fin n)).support (c j : Equiv.Perm (Fin n)).support) :
    4 ≤ Open.pRank 3 ((Subgroup.closure (Set.range c)).comap ψ) :=
  AltCentralExtThree.le_pRank_comap_of_central_sylow ψ hψ U hU hUne _
    fun _ _ _ ψ' hψ' hcenter hp hne =>
      four_le_pRank_comap_of_central_three_of_ne_bot ψ' hψ' hcenter hp hne c hc hdisj

end CFSG.AGLEmbeddingD2
