module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.Assembly.LowTwoRank

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    [IsElementaryAbelian p G] : IsElementaryAbelian p H :=
  CFSG.IsElementaryAbelian.of_mulEquiv e inferInstance

theorem card_le_four_of_odd_psl_two {X : Type*} [Group X] {K : Type} [Field K] [Finite K]
    (hq : Odd (Nat.card K)) (e : X ≃* StatedProj (StatedSL 2 K)) (E : Subgroup X)
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEl := (OutcomeLocal.odd_projective_linear_two_elementary_two_sections hq).2.2.1
  have : IsElementaryAbelian 2 (E.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  have hbound := hEl (E.map e.toMonoidHom) ⊥
    (isElementaryAbelian_of_mulEquiv QuotientGroup.quotientBot.symm)
  rwa [Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
    Subgroup.card_map_of_injective e.injective] at hbound

theorem not_odd_psl_two_of_elementary {X : Type*} [Group X] (E : Subgroup X)
    [IsElementaryAbelian 2 E] (hE : 4 < Nat.card E) {K : Type} [Field K] [Finite K]
    (hq : Odd (Nat.card K)) : IsEmpty (X ≃* StatedProj (StatedSL 2 K)) :=
  ⟨fun e => absurd (card_le_four_of_odd_psl_two hq e E) (not_le.mpr hE)⟩

theorem card_psl_two_mul_gcd (K : Type) [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 2 K)) * Nat.gcd 2 (Nat.card K - 1) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 2)]
  have h1 : 2 * (2 - 1) / 2 = 1 := by norm_num
  rw [h1, pow_one, Finset.Icc_self, Finset.prod_singleton]
  refine Nat.div_mul_cancel ((Nat.gcd_dvd_right 2 _).trans ?_)
  refine Dvd.dvd.mul_left ?_ _
  have h2 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    rcases Nat.eq_zero_or_pos (Nat.card K) with h | h
    · rw [h]
      rfl
    · cases hk : Nat.card K with
      | zero => omega
      | succ k =>
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
  rw [h2]
  exact Dvd.intro _ rfl

theorem two_mul_card_psl_two_of_odd (K : Type) [Field K] [Finite K] (hq : Odd (Nat.card K)) :
    Nat.card (StatedProj (StatedSL 2 K)) * 2 = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h := card_psl_two_mul_gcd K
  have hg : Nat.gcd 2 (Nat.card K - 1) = 2 := by
    obtain ⟨k, hk⟩ := hq
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  rwa [hg] at h

theorem card_psl_two_of_even (K : Type) [Field K] [Finite K] (hq : Even (Nat.card K)) :
    Nat.card (StatedProj (StatedSL 2 K)) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h := card_psl_two_mul_gcd K
  have hg : Nat.gcd 2 (Nat.card K - 1) = 1 := by
    obtain ⟨k, hk⟩ := hq
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at hk
      exact absurd hk Nat.card_pos.ne'
    · rw [hk, show k + k - 1 = 2 * (k - 1) + 1 by omega]
      simp
  rwa [hg, mul_one] at h

theorem card_psl_three_four (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (StatedProj (StatedSL 3 K)) = 20160 := by
  rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hK]
  decide

theorem card_alternating_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_card_alternatingGroup (α := Fin 7)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  have h7 : Nat.factorial 7 = 5040 := rfl
  omega

theorem exists_elementary_psl_two_even (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ E : Subgroup (StatedProj (StatedSL 2 K)), IsElementaryAbelian 2 E ∧
      Nat.card E = Nat.card K := by
  have hinj : Function.Injective (SectionRank.OddCover.stU K) :=
    (SectionRank.OddCover.pslEquiv K).injective.comp SectionRank.OddCover.pslU_injective
  have hE : IsElementaryAbelian 2 (SectionRank.OddCover.stU K).range := by
    refine { toIsMulCommutative := isMulCommutative_iff.mpr ?_, exponent_dvd_p := ?_ }
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      change SectionRank.OddCover.stU K a * SectionRank.OddCover.stU K b =
        SectionRank.OddCover.stU K b * SectionRank.OddCover.stU K a
      rw [← map_mul, ← map_mul, mul_comm a b]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, a, rfl⟩ := x
      apply Subtype.ext
      change SectionRank.OddCover.stU K a ^ 2 = 1
      rw [← map_pow, pow_two, ← ofAdd_toAdd a, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero,
        map_one]
  refine ⟨(SectionRank.OddCover.stU K).range, hE, ?_⟩
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd]

theorem cubeSub_lt_cubeSub {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have h1 : a ^ 2 - 1 < b ^ 2 - 1 := by
    have : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
    have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
    omega
  calc a * (a ^ 2 - 1) ≤ a * (b ^ 2 - 1) := Nat.mul_le_mul_left _ h1.le
    _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hab (by omega)

theorem eq_of_cubeSub_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (cubeSub_lt_cubeSub ha hab).ne
  · exact hab
  · exact absurd h (cubeSub_lt_cubeSub hb hab).ne'

theorem cubeSub_le_cubeSub {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) := by
  rcases Nat.eq_or_lt_of_le hab with rfl | h
  · exact le_rfl
  · exact (cubeSub_lt_cubeSub ha h).le

theorem cubeSub_ne_of_between {a N : ℕ} (ha : 1 ≤ a) (h1 : a * (a ^ 2 - 1) < N)
    (h2 : N < (a + 1) * ((a + 1) ^ 2 - 1)) (t : ℕ) : t * (t ^ 2 - 1) ≠ N := by
  intro ht
  rcases Nat.lt_or_ge a t with hat | hat
  · have := cubeSub_le_cubeSub (show 1 ≤ a + 1 by omega) (show a + 1 ≤ t by omega)
    omega
  · rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp at ht
      omega
    · have := cubeSub_le_cubeSub ht0 hat
      omega

theorem two_dvd_cubeSub (t : ℕ) : 2 ∣ t * (t ^ 2 - 1) := by
  rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact Dvd.dvd.mul_right ⟨k, by omega⟩ _
  · refine Dvd.dvd.mul_left ⟨2 * k ^ 2 + 2 * k, ?_⟩ _
    rw [hk]
    ring_nf
    omega

theorem prime_pow_inj {p f l g : ℕ} (hp : p.Prime) (hl : l.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (h : p ^ f = l ^ g) : p = l ∧ f = g := by
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj hp hl h
  exact ⟨h1, by rw [h2]⟩

theorem two_pow_dvd_of_dvd_mul_odd {k a m : ℕ} (hm : Odd m) (h : 2 ^ k ∣ 2 ^ a * m) :
    k ≤ a := by
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h)

end CFSG.ComponentClassification.UnbalancingLocal
