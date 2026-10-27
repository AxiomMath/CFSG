module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.CGT.Timmesfeld75

lemma irr_card_dvd_sub_one {P X : Type*} [Group P] [Finite P] [MulAction P X] [Finite X]
    (x₀ : X) (hx₀ : ∀ p : P, p • x₀ = x₀)
    (hfree : ∀ (p : P) (x : X), p ≠ 1 → p • x = x → x = x₀) :
    Nat.card P ∣ Nat.card X - 1 := by
  classical
  have hFP : Fintype P := Fintype.ofFinite P
  have hFX : Fintype X := Fintype.ofFinite X
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P X
  have h1 : ∀ p : P, p ≠ 1 → Fintype.card (MulAction.fixedBy X p) = 1 := by
    intro p hp
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨x₀, hx₀ p⟩, ?_⟩
    rintro ⟨x, hx⟩
    exact Subtype.ext (hfree p x hp hx)
  have h2 : Fintype.card (MulAction.fixedBy X (1 : P)) = Fintype.card X :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv (fun x => by simp))
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : P))] at hB
  rw [Finset.sum_congr rfl (fun p hp => h1 p (Finset.ne_of_mem_erase hp)), h2] at hB
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    smul_eq_mul, mul_one] at hB
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x₀⟩
  have hP : 0 < Fintype.card P := Fintype.card_pos
  have hdvd : Fintype.card P ∣ Fintype.card X - 1 + Fintype.card P :=
    ⟨Fintype.card (Quotient (MulAction.orbitRel P X)), by rw [mul_comm, ← hB]; omega⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Nat.dvd_add_self_right.mp hdvd

lemma irr_card_dvd_natCard_sub_one {Y : Type*} [Group Y] (N₁ P : Subgroup Y) [N₁.Normal]
    [Finite P] [Finite N₁]
    (hfree : ∀ y ∈ P, y ≠ 1 → ∀ n ∈ N₁, y * n * y⁻¹ = n → n = 1) :
    Nat.card P ∣ Nat.card N₁ - 1 := by
  let _ : MulAction P N₁ :=
    MulAction.compHom N₁ ((MulAut.conjNormal : Y →* MulAut N₁).comp P.subtype)
  have hsmul : ∀ (p : P) (x : N₁), ((p • x : N₁) : Y) = (p : Y) * x * (p : Y)⁻¹ :=
    fun p x => MulAut.conjNormal_apply (p : Y) x
  refine irr_card_dvd_sub_one (1 : N₁) (fun p => ?_) (fun p x hp hx => ?_)
  · apply Subtype.ext
    rw [hsmul]
    simp
  · have hx' : (p : Y) * x * (p : Y)⁻¹ = x := by
      rw [← hsmul, hx]
    exact Subtype.ext (hfree p p.2 (fun h => hp (Subtype.ext h)) x x.2 hx')

lemma irr_prime_pow_dvd_natCard_sub_one {Y : Type*} [Group Y] [Finite Y]
    (N N₁ : Subgroup Y) [N.Normal] [N₁.Normal] (hle : N₁ ≤ N) (hN : IsPGroup 2 N)
    (hfpf : ∀ y : Y, Odd (orderOf (QuotientGroup.mk y : Y ⧸ N)) →
      (QuotientGroup.mk y : Y ⧸ N) ≠ 1 → ∀ n ∈ N, y * n * y⁻¹ = n → n = 1)
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : r ^ k ∣ Nat.card Y) :
    r ^ k ∣ Nat.card N₁ - 1 := by
  have hrf : Fact r.Prime := ⟨hr⟩
  obtain ⟨P⟩ : Nonempty (Sylow r Y) := inferInstance
  have hPcard : Nat.card (P : Subgroup Y) = r ^ (Nat.card Y).factorization r :=
    P.card_eq_multiplicity
  have hkP : r ^ k ∣ Nat.card (P : Subgroup Y) := by
    rw [hPcard]
    exact pow_dvd_pow r ((hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hk)
  refine hkP.trans (irr_card_dvd_natCard_sub_one N₁ (P : Subgroup Y) ?_)
  intro y hyP hy1 n hn hfix
  have hcop : Nat.Coprime (Nat.card (P : Subgroup Y)) (Nat.card N) := by
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hN
    rw [hPcard, hb]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hord : orderOf y ∣ Nat.card (P : Subgroup Y) := Subgroup.orderOf_dvd_natCard _ hyP
  have hodd : Odd (orderOf (QuotientGroup.mk y : Y ⧸ N)) := by
    have hPodd : Odd (Nat.card (P : Subgroup Y)) := by
      rw [hPcard]
      exact (hr.odd_of_ne_two hr2).pow
    exact (hPodd.of_dvd_nat hord).of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' N) y)
  have hne : (QuotientGroup.mk y : Y ⧸ N) ≠ 1 := by
    intro h
    have hyN : y ∈ N := (QuotientGroup.eq_one_iff y).mp h
    have h1 : orderOf y = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hord (Subgroup.orderOf_dvd_natCard N hyN)
    exact hy1 (orderOf_eq_one_iff.mp h1)
  exact hfpf y hodd hne n (hle hn) hfix

lemma irr_dvd_natCard_sub_one {Y : Type*} [Group Y] [Finite Y]
    (N N₁ : Subgroup Y) [N.Normal] [N₁.Normal] (hle : N₁ ≤ N) (hN : IsPGroup 2 N)
    (hfpf : ∀ y : Y, Odd (orderOf (QuotientGroup.mk y : Y ⧸ N)) →
      (QuotientGroup.mk y : Y ⧸ N) ≠ 1 → ∀ n ∈ N, y * n * y⁻¹ = n → n = 1)
    {d : ℕ} (hd : Odd d) (hdY : d ∣ Nat.card Y) : d ∣ Nat.card N₁ - 1 := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr
        ((dvd_pow_self 2 hk.ne').trans hpk))
    exact irr_prime_pow_dvd_natCard_sub_one N N₁ hle hN hfpf hp hp2 (hpk.trans hdY)

lemma irr_two_pow_ne_one {g j : ℕ} (hj0 : 0 < j) (hj : j < 2 * g) :
    (2 : ZMod (2 ^ g + 1)) ^ j ≠ 1 := by
  intro h
  have hg : (2 : ZMod (2 ^ g + 1)) ^ g = -1 := by
    have h0 : ((2 ^ g + 1 : ℕ) : ZMod (2 ^ g + 1)) = 0 := ZMod.natCast_self _
    push_cast at h0
    linear_combination h0
  rcases le_or_gt j g with hjg | hjg
  · have h1 : ((2 ^ j - 1 : ℕ) : ZMod (2 ^ g + 1)) = 0 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      rw [h, sub_self]
    have h2 : 2 ^ g + 1 ∣ 2 ^ j - 1 := (ZMod.natCast_eq_zero_iff _ _).mp h1
    have h3 : 2 ^ j ≤ 2 ^ g := Nat.pow_le_pow_right two_pos hjg
    have h4 : 1 < 2 ^ j := Nat.one_lt_two_pow hj0.ne'
    have h5 := Nat.le_of_dvd (by omega) h2
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, j = g + t := ⟨j - g, by omega⟩
    have h1 : ((2 ^ t + 1 : ℕ) : ZMod (2 ^ g + 1)) = 0 := by
      push_cast
      rw [pow_add, hg] at h
      linear_combination -h
    have h2 : 2 ^ g + 1 ∣ 2 ^ t + 1 := (ZMod.natCast_eq_zero_iff _ _).mp h1
    have h3 : 2 ^ t < 2 ^ g := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h5 := Nat.le_of_dvd (Nat.succ_pos _) h2
    omega

lemma irr_two_mul_le_of_dvd {g a : ℕ} (ha : 0 < a) (h : 2 ^ g + 1 ∣ 2 ^ a - 1) : 2 * g ≤ a := by
  have h1 : ((2 ^ a - 1 : ℕ) : ZMod (2 ^ g + 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_sub Nat.one_le_two_pow] at h1
  push_cast at h1
  have h2 : (2 : ZMod (2 ^ g + 1)) ^ a = 1 := sub_eq_zero.mp h1
  have h3 : 0 < orderOf (2 : ZMod (2 ^ g + 1)) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨a, ha, h2⟩)
  have h4 : orderOf (2 : ZMod (2 ^ g + 1)) ≤ a := orderOf_le_of_pow_eq_one ha h2
  by_contra hlt
  exact irr_two_pow_ne_one h3 (by omega) (pow_orderOf_eq_one _)

theorem two_pow_two_mul_le_natCard_of_fpf {Y : Type*} [Group Y] [Finite Y]
    (N N₁ : Subgroup Y) [N.Normal] [N₁.Normal] (hle : N₁ ≤ N) (hN : IsPGroup 2 N)
    (g : ℕ) (hg : 0 < g) (hcard : Nat.card (Y ⧸ N) = 2 ^ g * ((2 ^ g) ^ 2 - 1))
    (hfpf : ∀ y : Y, Odd (orderOf (QuotientGroup.mk y : Y ⧸ N)) →
      (QuotientGroup.mk y : Y ⧸ N) ≠ 1 → ∀ n ∈ N, y * n * y⁻¹ = n → n = 1)
    (hne : N₁ ≠ ⊥) : 2 ^ (2 * g) ≤ Nat.card N₁ := by
  have hdY : 2 ^ g + 1 ∣ Nat.card Y := by
    rw [← Subgroup.card_mul_index N, Subgroup.index_eq_card, hcard]
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    have hsq := Nat.sq_sub_sq (2 ^ g) 1
    rw [one_pow] at hsq
    rw [hsq]
    exact Dvd.intro _ rfl
  have hodd : Odd (2 ^ g + 1) := (Nat.even_pow.mpr ⟨even_two, hg.ne'⟩).add_one
  have hdvd := irr_dvd_natCard_sub_one N N₁ hle hN hfpf hodd hdY
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hN.to_le hle)
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using ha)) hne
    · exact h
  rw [ha] at hdvd ⊢
  exact Nat.pow_le_pow_right two_pos (irr_two_mul_le_of_dvd ha0 hdvd)

end CFSG.CGT.Timmesfeld75
