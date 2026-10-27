module

import CFSG.LocalAnalysis.PreuniquenessRankFour.GeneratorRank
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.E2

open Subgroup

open CFSG.PreuniquenessRankFour.Helpers in
theorem ord_mul_pRank_le_rank {A X : Type*} [Group A] [Finite A] [Group X] [Finite X]
    [MulDistribMulAction A X] (hX : IsPGroup 2 X)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut A X)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    orderOf (2 : ZMod p) * CFSG.Open.pRank p (⊤ : Subgroup A) ≤ Group.rank X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hcard⟩ := pRank_attained p hp (⊤ : Subgroup A)
  have : IsMulCommutative E := hE.1
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hEp : IsPGroup p E := IsPGroup.of_card hcard
  have hfaithfulE : Function.Injective (MulDistribMulAction.toMulAut E X) := by
    intro a b hab
    apply Subtype.ext
    apply hfaithful
    apply MulEquiv.ext
    intro q
    exact congrArg (fun f : MulAut X => f q) hab
  have hcop : ¬ p ∣ Nat.card (frattini X) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hX.to_subgroup (frattini X))
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  let : IsMulCommutative (X ⧸ frattini X) := pGroup_frattini_quotient_isMulCommutative 2 hX
  let : CommGroup (X ⧸ frattini X) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module hX
  let := characteristic_quotient_mulDistribMulAction (acting := E) (frattini X)
  have hfaithfulQ := faithful_coprime_pGroup_action_on_frattini_quotient p hEp hcop hfaithfulE
  have hbound := faithful_binary_elementary_linear_action_order_dimension_bound p _ hp2 hcard
    (fun a => Subtype.ext (hE.2 a a.2))
    (multiplicative_action_zmod_linear_aut (acting := E) (source := X ⧸ frattini X) 2)
    (faithful_multiplicative_action_zmod_linear_aut 2 hfaithfulQ)
  have hdim := twoGroup_frattini_finrank_eq_group_rank hX
  rw [hdim] at hbound
  exact hbound

theorem ord_mul_card_le_rank_hom {A X : Type*} [Group A] [Finite A] [Group X] [Finite X]
    (hX : IsPGroup 2 X) (φ : A →* MulAut X) (hφ : Function.Injective φ) {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1)
    (hcard : Nat.card A = p ^ r) : orderOf (2 : ZMod p) * r ≤ Group.rank X := by
  let : MulDistribMulAction A X := MulDistribMulAction.compHom X φ
  have hinj : Function.Injective (MulDistribMulAction.toMulAut A X) := by
    intro a b hab
    apply hφ
    have h1 : ∀ c, MulDistribMulAction.toMulAut A X c = φ c := fun c => MulEquiv.ext fun x => rfl
    rw [← h1, ← h1]
    exact hab
  have h1 := ord_mul_pRank_le_rank (A := A) (X := X) hX hinj hp hp2
  have hE : CFSG.Open.IsElemAbelian p (⊤ : Subgroup A) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x _ => hpow x⟩
    exact hcomm a.1 b.1
  have hr : r ≤ CFSG.Open.pRank p (⊤ : Subgroup A) := by
    unfold CFSG.Open.pRank
    refine le_csSup ?_ ⟨⊤, le_rfl, hE, ?_⟩
    · refine ⟨Nat.card A, ?_⟩
      rintro k ⟨E, -, -, hk⟩
      exact (Nat.lt_pow_self hp.one_lt).le.trans (hk ▸ E.card_le_card_group)
    · rw [Subgroup.card_top, hcard]
  exact (Nat.mul_le_mul_left _ hr).trans h1

@[expose] noncomputable def conjAction {G : Type*} [Group G] (A X : Subgroup G)
    (hnorm : A ≤ normalizer (X : Set G)) : A →* MulAut X :=
  (X.normalizerMonoidHom).comp (Subgroup.inclusion hnorm)

theorem conjAction_apply {G : Type*} [Group G] {A X : Subgroup G}
    (hnorm : A ≤ normalizer (X : Set G)) (a : A) (x : X) :
    ((conjAction A X hnorm a x : X) : G) = (a : G) * x * (a : G)⁻¹ := rfl

theorem ord_mul_card_le_rank {G : Type*} [Group G] [Finite G] {A X : Subgroup G}
    (hX : IsPGroup 2 X) (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : ∀ a ∈ A, (∀ x ∈ X, a * x * a⁻¹ = x) → a = 1)
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hpow : ∀ a ∈ A, a ^ p = 1) (hcard : Nat.card A = p ^ r) :
    orderOf (2 : ZMod p) * r ≤ Group.rank X := by
  let : MulDistribMulAction A X := MulDistribMulAction.compHom X (conjAction A X hnorm)
  have hinj : Function.Injective (MulDistribMulAction.toMulAut A X) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    rw [Subgroup.coe_one]
    apply hfaith a a.2
    intro x hx
    have h2 := congrArg (fun f : MulAut X => ((f ⟨x, hx⟩ : X) : G)) ha
    have h3 : (((MulDistribMulAction.toMulAut A X a : MulAut X) ⟨x, hx⟩ : X) : G) =
        (a : G) * x * (a : G)⁻¹ := rfl
    rw [h3] at h2
    simpa using h2
  have h1 := ord_mul_pRank_le_rank (A := A) (X := X) hX hinj hp hp2
  have hE : CFSG.Open.IsElemAbelian p (⊤ : Subgroup A) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x _ => ?_⟩
    · exact hcomm a.1.1 a.1.2 b.1.1 b.1.2
    · exact Subtype.ext (hpow x.1 x.2)
  have hr : r ≤ CFSG.Open.pRank p (⊤ : Subgroup A) := by
    unfold CFSG.Open.pRank
    refine le_csSup ?_ ⟨⊤, le_rfl, hE, ?_⟩
    · refine ⟨Nat.card A, ?_⟩
      rintro k ⟨E, -, -, hk⟩
      exact (Nat.lt_pow_self hp.one_lt).le.trans (hk ▸ E.card_le_card_group)
    · rw [Subgroup.card_top, hcard]
  exact (Nat.mul_le_mul_left _ hr).trans h1

theorem le_normalizer_of_normalizes {G : Type*} [Group G] {A V : Subgroup G}
    (h : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V) : A ≤ normalizer (V : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro v
  refine ⟨fun hv => h a ha v hv, fun hv => ?_⟩
  have h1 := h a⁻¹ (inv_mem ha) _ hv
  have h2 : a⁻¹ * (a * v * a⁻¹) * a⁻¹⁻¹ = v := by group
  rwa [h2] at h1

theorem orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  have h1 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have h2 : (2 : ZMod 3) ≠ 1 := by decide
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h1 h2

theorem three_le_orderOf_two_zmod {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    3 ≤ orderOf (2 : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  exact CFSG.PreuniquenessRankFour.Helpers.binary_prime_order_at_least_three_of_ne_three p hp2 hp3

theorem five_le_orderOf_two_zmod {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    5 ≤ orderOf (2 : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  have hpos : 0 < orderOf (2 : ZMod p) := by
    have hne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h0)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    exact orderOf_pos_iff.mpr (isUnit_iff_ne_zero.mpr hne).isOfFinOrder
  have hk := pow_orderOf_eq_one (2 : ZMod p)
  generalize orderOf (2 : ZMod p) = k at hpos hlt hk
  have hdvd : p ∣ 2 ^ k - 1 := by
    have h1 : (((2 ^ k - 1 : ℕ)) : ZMod p) = 0 := by
      have h2 : ((2 ^ k : ℕ) : ZMod p) = 1 := by push_cast; exact hk
      have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [Nat.cast_sub h3, h2]; simp
    exact (ZMod.natCast_eq_zero_iff _ p).mp h1
  have hle : p ≤ 15 := by
    have h15 : 2 ^ k - 1 ≤ 15 := by
      have : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (Nat.le_of_dvd (by
      have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hpos
      omega) hdvd).trans h15
  interval_cases k <;> interval_cases p <;> first | omega | (revert hdvd hp; norm_num)

theorem rank_bounds {p r d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : orderOf (2 : ZMod p) * r ≤ d)
    (hd : d ≤ 4) : r ≤ 2 ∧ (5 ≤ p → r ≤ 1) ∧ (11 ≤ p → r = 0) := by
  have h2 : 2 ≤ orderOf (2 : ZMod p) := by
    have : Fact p.Prime := ⟨hp⟩
    exact CFSG.PreuniquenessRankFour.Helpers.binary_prime_order_at_least_two p hp2
  refine ⟨?_, fun h5 => ?_, fun h11 => ?_⟩
  · nlinarith
  · have := three_le_orderOf_two_zmod hp h5
    nlinarith
  · have := five_le_orderOf_two_zmod hp h11
    nlinarith

end CFSG.GH74.E2
