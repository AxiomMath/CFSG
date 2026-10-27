module

public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34HeldCenter

open CFSG Subgroup

variable {J : Type*} [Group J] [Finite J]

theorem not_two_dvd_card_pPrimeCore : ¬ 2 ∣ Nat.card (pPrimeCore 2 J) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card

theorem eq_one_of_mem_pPrimeCore {x : J} (hx : x ∈ pPrimeCore 2 J) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x = 1 := by
  obtain ⟨i, -, hix⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have h2 : orderOf x ∣ Nat.card (pPrimeCore 2 J) := Subgroup.orderOf_dvd_natCard _ hx
  cases i with
  | zero => rwa [pow_zero, orderOf_eq_one_iff] at hix
  | succ i =>
    rw [hix] at h2
    exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero i)).trans h2) not_two_dvd_card_pPrimeCore

theorem mem_of_center_of_odd {v : J}
    (hc : QuotientGroup.mk' (pPrimeCore 2 J) v ∈ center (J ⧸ pPrimeCore 2 J))
    (hv : Odd (orderOf v)) : v ∈ pPrimeCore 2 J := by
  set x := QuotientGroup.mk' (pPrimeCore 2 J) v with hx
  have hN : (zpowers x).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    rw [mem_center_iff.1 (zpow_mem hc k) g, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers x) k⟩
  have hcop : Nat.Coprime 2 (Nat.card (zpowers x)) := by
    rw [Nat.card_zpowers, Nat.coprime_two_left]
    exact hv.of_dvd_nat (orderOf_map_dvd _ v)
  have hle : zpowers x ≤ pPrimeCore 2 (J ⧸ pPrimeCore 2 J) :=
    le_sSup (show zpowers x ∈ {K : Subgroup (J ⧸ pPrimeCore 2 J) | K.Normal ∧
      Nat.Coprime 2 (Nat.card K)} from ⟨hN, hcop⟩)
  rw [pPrimeCore_quotient_eq_bot Nat.prime_two] at hle
  have h1 : x = 1 := mem_bot.1 (hle (mem_zpowers x))
  rw [hx, QuotientGroup.mk'_apply] at h1
  exact (QuotientGroup.eq_one_iff v).1 h1

theorem exists_orderOf_four {u : J}
    (hc : QuotientGroup.mk' (pPrimeCore 2 J) u ∈ center (J ⧸ pPrimeCore 2 J))
    (hu : u * u ∉ pPrimeCore 2 J) :
    ∃ w : J, QuotientGroup.mk' (pPrimeCore 2 J) w ∈ center (J ⧸ pPrimeCore 2 J) ∧
      orderOf w = 4 ∧ w * w ∉ pPrimeCore 2 J := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos u).ne'
  have h2k : 2 ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hv : u ^ 2 ^ k ∈ pPrimeCore 2 J := by
    refine mem_of_center_of_odd (by rw [map_pow]; exact pow_mem hc _) ?_
    rw [orderOf_pow_of_dvd h2k (hn ▸ dvd_mul_right _ _), hn, Nat.mul_div_cancel_left _
      (Nat.pos_of_ne_zero h2k)]
    exact hm
  set w₀ := u ^ m with hw₀
  have hw₀o : orderOf w₀ = 2 ^ k := by
    rw [hw₀, orderOf_pow_of_dvd hm.pos.ne' (hn ▸ dvd_mul_left _ _), hn,
      Nat.mul_div_cancel _ hm.pos]
  have hw₀2 : w₀ * w₀ ∉ pPrimeCore 2 J := by
    intro h
    apply hu
    set x := QuotientGroup.mk' (pPrimeCore 2 J) u with hx
    have h1 : x ^ (2 * m) = 1 := by
      have h' : QuotientGroup.mk' (pPrimeCore 2 J) (w₀ * w₀) = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).2 h
      rw [map_mul, hw₀, map_pow, ← pow_add] at h'
      rwa [two_mul]
    have h2 : x ^ 2 ^ k = 1 := by
      rw [hx, ← map_pow, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).2 hv
    have hd : orderOf x ∣ 2 := by
      obtain ⟨i, -, hix⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2)
      have hcop : Nat.Coprime (orderOf x) m := by
        rw [hix]
        exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
      exact hcop.dvd_of_dvd_mul_right (orderOf_dvd_of_pow_eq_one h1)
    have hx2 : x * x = 1 := by
      rw [← sq]
      exact orderOf_dvd_iff_pow_eq_one.1 hd
    rw [hx, ← map_mul, QuotientGroup.mk'_apply] at hx2
    exact (QuotientGroup.eq_one_iff _).1 hx2
  have hk : 2 ≤ k := by
    by_contra hk
    apply hw₀2
    have h1 : w₀ * w₀ = 1 := by
      rw [← sq, ← orderOf_dvd_iff_pow_eq_one, hw₀o]
      have h2 := pow_dvd_pow 2 (show k ≤ 1 by omega)
      rwa [pow_one] at h2
    rw [h1]
    exact one_mem _
  set w := w₀ ^ 2 ^ (k - 2) with hw
  have hdvd : 2 ^ (k - 2) ∣ orderOf w₀ := by
    rw [hw₀o]
    exact pow_dvd_pow 2 (Nat.sub_le k 2)
  have hwo : orderOf w = 4 := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hw₀o,
      Nat.pow_div (Nat.sub_le k 2) two_pos, show k - (k - 2) = 2 by omega]
    norm_num
  refine ⟨w, ?_, hwo, ?_⟩
  · rw [hw, hw₀, map_pow, map_pow]
    exact pow_mem (pow_mem hc _) _
  · intro h
    have h4 : (w * w) ^ 2 ^ 1 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← sq,
        orderOf_pow_of_dvd two_ne_zero (by rw [hwo]; norm_num), hwo]
      norm_num
    have h1 := eq_one_of_mem_pPrimeCore h h4
    have h' := orderOf_dvd_of_pow_eq_one (show w ^ 2 = 1 by rw [sq, h1])
    rw [hwo] at h'
    exact absurd h' (by decide)

theorem exists_comm_lift {w : J} (hw : IsPGroup 2 (zpowers w))
    (hc : QuotientGroup.mk' (pPrimeCore 2 J) w ∈ center (J ⧸ pPrimeCore 2 J)) (g : J) :
    ∃ c : J, c * w = w * c ∧
      QuotientGroup.mk' (pPrimeCore 2 J) c = QuotientGroup.mk' (pPrimeCore 2 J) g := by
  classical
  set f := QuotientGroup.mk' (pPrimeCore 2 J) with hf
  have hconj : ∀ a ∈ zpowers w, ∀ c : J, f (a * c * a⁻¹) = f c := by
    intro a ha c
    have hac : f a ∈ center (J ⧸ pPrimeCore 2 J) := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
      rw [map_zpow]
      exact zpow_mem hc k
    rw [map_mul, map_mul, map_inv, ← mem_center_iff.1 hac (f c), mul_inv_cancel_right]
  let F := {c : J // f c = f g}
  let act : MulAction (zpowers w) F :=
    { smul := fun a c => ⟨(a : J) * c.1 * (a : J)⁻¹, (hconj a a.2 c.1).trans c.2⟩
      one_smul := fun c => Subtype.ext (by
        change ((1 : zpowers w) : J) * c.1 * ((1 : zpowers w) : J)⁻¹ = c.1
        simp)
      mul_smul := fun a b c => Subtype.ext (by
        change ((a * b : zpowers w) : J) * c.1 * ((a * b : zpowers w) : J)⁻¹ =
          (a : J) * ((b : J) * c.1 * (b : J)⁻¹) * (a : J)⁻¹
        simp [mul_assoc]) }
  let e : F ≃ pPrimeCore 2 J :=
    { toFun := fun c => ⟨g⁻¹ * c.1,
        QuotientGroup.eq.1 (show (g : J ⧸ pPrimeCore 2 J) = c.1 from c.2.symm)⟩
      invFun := fun o => ⟨g * o, by
        show ((g * o : J) : J ⧸ pPrimeCore 2 J) = g
        rw [QuotientGroup.eq]
        simp⟩
      left_inv := fun c => Subtype.ext (by simp)
      right_inv := fun o => Subtype.ext (by simp) }
  have hcard : ¬ 2 ∣ Nat.card F := by
    rw [Nat.card_congr e]
    exact not_two_dvd_card_pPrimeCore
  obtain ⟨c, hcfix⟩ := hw.nonempty_fixed_point_of_prime_not_dvd_card F hcard
  refine ⟨c.1, ?_, c.2⟩
  have h := congrArg Subtype.val ((MulAction.mem_fixedPoints).1 hcfix ⟨w, mem_zpowers w⟩)
  change w * c.1 * w⁻¹ = c.1 at h
  calc c.1 * w = w * c.1 * w⁻¹ * w := by rw [h]
    _ = w * c.1 := by group

theorem exists_five_comm {w : J} (hw : IsPGroup 2 (zpowers w))
    (hc : QuotientGroup.mk' (pPrimeCore 2 J) w ∈ center (J ⧸ pPrimeCore 2 J))
    (h5 : 5 ∣ Nat.card (J ⧸ pPrimeCore 2 J)) :
    ∃ v : J, v * w = w * v ∧ v ∉ pPrimeCore 2 J ∧ ∃ e : ℕ, orderOf v = 5 ^ e := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 J) y
  obtain ⟨c, hcw, hcg⟩ := exists_comm_lift hw hc g
  obtain ⟨e, r, hr, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 5 (by norm_num)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr (dvd_zero 5)
  refine ⟨c ^ r, (Commute.pow_left hcw r).eq, ?_, e, ?_⟩
  · intro h
    apply hr
    rw [← hy, orderOf_dvd_iff_pow_eq_one, ← hcg, ← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 h
  · rw [orderOf_pow_of_dvd hr0 (hn ▸ dvd_mul_left _ _), hn, Nat.mul_div_cancel _
      (Nat.pos_of_ne_zero hr0)]

end CFSG.ComponentClassification.GrSLit.L34HeldCenter
