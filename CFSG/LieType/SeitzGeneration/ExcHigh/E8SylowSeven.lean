module

public import CFSG.HardMathSupport.Lang.AnisoE8.D8Conj
public import CFSG.Sporadic.He.Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open CFSG.LieType.Universal CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Lang.AnisoE8

theorem factorization_pow_two_mul_sub_one_seven {q : ℕ} (hq : 7 ∣ q + 1) {k : ℕ} (hk : k ≠ 0) :
    (q ^ (2 * k) - 1).factorization 7 = (q + 1).factorization 7 + k.factorization 7 := by
  have hq7 : (q : ZMod 7) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hq
    rw [Nat.cast_add, Nat.cast_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hord : orderOf (q : ZMod 7) = 2 := by
    rw [hq7]
    exact orderOf_eq_prime (by decide) (by decide)
  have hsq : (q ^ 2 - 1).factorization 7 = (q + 1).factorization 7 := by
    have h1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [(by omega : 1 ≤ q), Nat.one_le_pow 2 q (by omega)]
      ring
    rw [h1, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 7 ∣ q - 1), zero_add]
  have h := ordProj_pow_sub_one_of_dvd (by norm_num) (by norm_num) (by omega) (by omega) hord hk
  rw [hsq, ← pow_add] at h
  exact Nat.pow_right_injective (by norm_num) h

private theorem prod_pow_two_mul_sub_one_ne_zero {q : ℕ} (hq : 2 ≤ q) {ks : List ℕ}
    (hks : ∀ k ∈ ks, k ≠ 0) : (ks.map fun k => q ^ (2 * k) - 1).prod ≠ 0 :=
  List.prod_ne_zero fun h => by
    obtain ⟨k, hk, hk0⟩ := List.mem_map.1 h
    exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by have := hks k hk; omega) (by omega)) hk0

private theorem factorization_prod_pow_two_mul_sub_one_seven {q : ℕ} (hq : 7 ∣ q + 1)
    (ks : List ℕ) (hks : ∀ k ∈ ks, k ≠ 0 ∧ ¬ 7 ∣ k) :
    (ks.map fun k => q ^ (2 * k) - 1).prod.factorization 7 =
      ks.length * (q + 1).factorization 7 := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨hk0, hk7⟩ := hks k List.mem_cons_self
    have hks' : ∀ j ∈ ks, j ≠ 0 ∧ ¬ 7 ∣ j := fun j hj => hks j (List.mem_cons_of_mem _ hj)
    rw [List.map_cons, List.prod_cons,
      Nat.factorization_mul (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) (by omega)))
        (prod_pow_two_mul_sub_one_ne_zero (by omega) fun j hj => (hks' j hj).1),
      Finsupp.add_apply, factorization_pow_two_mul_sub_one_seven hq hk0,
      Nat.factorization_eq_zero_of_not_dvd hk7, ih hks', List.length_cons]
    ring

private theorem factorization_pow_mul_prod_mul_seven {q : ℕ} (hq : 7 ∣ q + 1) (a : ℕ)
    (ks : List ℕ) (hks : ∀ k ∈ ks, k ≠ 0 ∧ ¬ 7 ∣ k) :
    (q ^ a * (ks.map fun k => q ^ (2 * k) - 1).prod * (q ^ 14 - 1)).factorization 7 =
      (ks.length + 1) * (q + 1).factorization 7 + 1 := by
  have hP := prod_pow_two_mul_sub_one_ne_zero (q := q) (by omega) fun j hj => (hks j hj).1
  have ha : q ^ a ≠ 0 := pow_ne_zero _ (by omega)
  have h14 : (q ^ 14 - 1).factorization 7 = (q + 1).factorization 7 + 1 := by
    have h := factorization_pow_two_mul_sub_one_seven hq (k := 7) (by norm_num)
    rwa [Nat.Prime.factorization_self (by norm_num)] at h
  rw [Nat.factorization_mul (mul_ne_zero ha hP)
      (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by norm_num) (by omega))),
    Nat.factorization_mul ha hP, Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 7 ∣ q), smul_zero,
    zero_add, factorization_prod_pow_two_mul_sub_one_seven hq ks hks, h14]
  ring

theorem factorization_N8_seven {q : ℕ} (hq : 7 ∣ q + 1) :
    (N8 q).factorization 7 = 8 * (q + 1).factorization 7 + 1 := by
  have e : N8 q =
      q ^ 56 * ([4, 1, 2, 3, 4, 5, 6].map fun k => q ^ (2 * k) - 1).prod * (q ^ 14 - 1) := by
    rw [N8_eq]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Nat.reduceMul]
    ring
  rw [e, factorization_pow_mul_prod_mul_seven hq _ _ (by decide)]
  rfl

theorem factorization_ordE8_seven {q : ℕ} (hq : 7 ∣ q + 1) :
    (ordE8 q).factorization 7 = 8 * (q + 1).factorization 7 + 1 := by
  have e : ordE8 q =
      q ^ 120 * ([15, 12, 10, 9, 6, 4, 1].map fun k => q ^ (2 * k) - 1).prod * (q ^ 14 - 1) := by
    simp only [ordE8, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Nat.reduceMul]
    ring
  rw [e, factorization_pow_mul_prod_mul_seven hq _ _ (by decide)]
  rfl

theorem factorization_card_proj_eq_N8 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (Nat.card (StatedProj (StatedOmega (StatedQuadPlus 8 K)))).factorization p =
      (N8 (Nat.card K)).factorization p := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := h2 ▸ ringChar.charP K
    have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K)
      (n := 8) (by norm_num)
    rw [← cast_N8 Nat.card_pos] at h
    have h' : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 8 K))) = N8 (Nat.card K) := by
      exact_mod_cast h
    rw [h']
  · rw [CFSG.ClassicalInvolution.card_statedProj_statedOmega_quadPlus_eq_ordD hℓ h2 hK (n := 8)
      (by norm_num), ← hK]
    set q := Nat.card K
    have hdef : ordD 8 q = N8 q / Nat.gcd 4 (q ^ 8 - 1) := rfl
    have hg : Nat.gcd 4 (q ^ 8 - 1) ∣ N8 q := by
      refine (Nat.gcd_dvd_right _ _).trans ?_
      rw [N8]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _
    have hgf : (Nat.gcd 4 (q ^ 8 - 1)).factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun hdv => hp2 ?_
      have h4 : p ∣ 2 ^ 2 := hdv.trans (Nat.gcd_dvd_left 4 _)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4)
    rw [hdef, Nat.factorization_div hg, Finsupp.coe_tsub, Pi.sub_apply, hgf, Nat.sub_zero]

theorem exists_conj_le_of_factorization_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (X : Subgroup G)
    (hv : (Nat.card G).factorization p ≤ (Nat.card X).factorization p) {E₀ : Subgroup G}
    (hE₀ : IsPGroup p E₀) : ∃ g : G, E₀.map (MulAut.conj g).toMonoidHom ≤ X := by
  obtain ⟨Sx⟩ : Nonempty (Sylow p X) := inferInstance
  set Q : Subgroup G := (Sx : Subgroup X).map X.subtype with hQ
  have hXG : (Nat.card X).factorization p ≤ (Nat.card G).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_subgroup_dvd_card X) p
  have hQc : Nat.card Q = p ^ (Nat.card G).factorization p := by
    rw [hQ, Subgroup.card_map_of_injective X.subtype_injective, Sylow.card_eq_multiplicity,
      le_antisymm hXG hv]
  obtain ⟨S₀, hS₀⟩ := hE₀.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ (Sylow.ofCard Q hQc)
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h : MulAut.conj g • x ∈ ((g • S₀ : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS₀ hx)
  rw [hg, Sylow.coe_ofCard] at h
  obtain ⟨y, -, hy⟩ := h
  change MulAut.conj g • x ∈ X
  rw [← hy]
  exact y.2

section SylowSeven


theorem factorization_card_E8_le_card_range_seven {K : Type} [Field K] [Finite K]
    (hpq : 7 ∣ Nat.card K + 1) (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K))) :
    (Nat.card (adjointGroup .E8 K)).factorization 7 ≤ (Nat.card Ψ.range).factorization 7 := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, factorization_ordE8_seven hpq,
    ← factorization_N8_seven hpq, ← factorization_card_proj_eq_N8 (by norm_num) (by norm_num)]
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
    (card_statedProj_dvd_card_range Ψ hker) 7

theorem exists_conj_le_range_of_sylow_E8_seven {K : Type} [Field K] [Finite K]
    (hpq : 7 ∣ Nat.card K + 1) (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)))
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀ : ∀ x ∈ E₀, x ^ 7 = 1) :
    ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ Ψ.range := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_conj_le_of_factorization_le Ψ.range
    (factorization_card_E8_le_card_range_seven hpq Ψ hker)
    fun x => ⟨1, Subtype.ext (by simpa using hE₀ x x.2)⟩

end SylowSeven

end CFSG.LieType.SeitzGeneration.ExcHigh
