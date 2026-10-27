module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec10D_odd_lift {X : Type} [Group X] [Finite X] {c : X} (hc1 : c ≠ 1) (hc2 : c * c = 1)
    (hcc : ∀ x : X, x * c = c * x) [(zpowers c).Normal] {N : Subgroup (X ⧸ zpowers c)}
    [N.Normal] (hN : Odd (Nat.card N)) :
    ∃ Y : Subgroup X, Y.Normal ∧ Odd (Nat.card Y) ∧
      ∀ x : X, (x : X ⧸ zpowers c) ∈ N → ∃ y ∈ Y, x = y ∨ x = c * y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : X →* X ⧸ zpowers c := QuotientGroup.mk' (zpowers c)
  let M : Subgroup X := N.comap π
  have hMn : M.Normal := Subgroup.Normal.comap inferInstance π
  have hcM : c ∈ M := by
    show π c ∈ N
    have : π c = 1 := (QuotientGroup.eq_one_iff c).mpr (Subgroup.mem_zpowers c)
    rw [this]
    exact N.one_mem
  have hordc : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  have hcardM : Nat.card M = 2 * Nat.card N := by
    have h1 := Subgroup.card_mul_index M
    have h2 := Subgroup.card_mul_index N
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers c)
    have h4 : M.index = N.index :=
      Subgroup.index_comap_of_surjective N (QuotientGroup.mk'_surjective (zpowers c))
    have h5 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [Nat.card_zpowers, hordc] at h3
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h5)
    calc Nat.card M * N.index = Nat.card M * M.index := by rw [h4]
      _ = Nat.card X := h1
      _ = Nat.card (X ⧸ zpowers c) * 2 := h3
      _ = (Nat.card N * N.index) * 2 := by rw [h2]
      _ = 2 * Nat.card N * N.index := by ring
  let c' : ↥M := ⟨c, hcM⟩
  have hc'c : ∀ m : ↥M, m * c' = c' * m := fun m => Subtype.ext (hcc m)
  have hc'sq : c' * c' = 1 := Subtype.ext hc2
  haveI hnorm : (zpowers c').Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcomm : Commute m (c' ^ i) := (show Commute m c' from hc'c m).zpow_right i
    have : m * c' ^ i * m⁻¹ = c' ^ i := by rw [hcomm.eq]; group
    rw [this]
    exact Subgroup.zpow_mem_zpowers c' i
  have hordc' : orderOf c' = 2 := by
    have : c' ≠ 1 := fun h => hc1 (by simpa [c'] using congrArg Subtype.val h)
    exact orderOf_eq_prime (by rw [pow_two]; exact hc'sq) this
  have hcardZ : Nat.card (zpowers c') = 2 := by rw [Nat.card_zpowers, hordc']
  have hindex : (zpowers c').index = Nat.card N := by
    have h := Subgroup.card_mul_index (zpowers c')
    rw [hcardZ, hcardM] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h
  have hcop : Nat.Coprime (Nat.card (zpowers c')) (zpowers c').index := by
    rw [hcardZ, hindex]
    exact Nat.coprime_two_left.mpr hN
  obtain ⟨Y', hY'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hdecomp : ∀ m : ↥M, ∃ a ∈ zpowers c', ∃ b ∈ Y', a * b = m := by
    intro m
    have : m ∈ zpowers c' ⊔ Y' := by
      rw [hY'.sup_eq_top]
      trivial
    exact Subgroup.mem_sup_of_normal_left.mp this
  have hdisj : Disjoint (zpowers c') Y' := hY'.disjoint
  have hcardY' : Nat.card Y' = Nat.card N := by
    have h := hY'.card_mul
    rw [hcardZ, hcardM] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h
  let Y : Subgroup X := Y'.map M.subtype
  have hYmem : ∀ b : ↥M, b ∈ Y' → (b : X) ∈ Y := fun b hb => ⟨b, hb, rfl⟩
  have hYodd : Odd (Nat.card Y) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hcardY']
    exact hN
  have hYM : ∀ y ∈ Y, y ∈ M := by
    rintro _ ⟨b, _, rfl⟩
    exact b.2
  have hodd_mem : ∀ p : X, p ∈ M → Odd (orderOf p) → p ∈ Y := by
    intro p hpM hpodd
    obtain ⟨a, ha, b, hb, hab⟩ := hdecomp ⟨p, hpM⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hk : (⟨p, hpM⟩ : ↥M) ^ orderOf p = 1 := by
      apply Subtype.ext
      simpa using pow_orderOf_eq_one p
    rw [← hab] at hk
    have hcomm : Commute (c' ^ i) b := ((show Commute b c' from hc'c b).zpow_right i).symm
    rw [hcomm.mul_pow] at hk
    have hc'i : c' ^ i * c' ^ i = 1 := by
      rw [← (Commute.refl c').mul_zpow, hc'sq, one_zpow]
    obtain ⟨m, hm⟩ := hpodd
    have hpow : (c' ^ i) ^ orderOf p = c' ^ i := by
      rw [hm, pow_succ, pow_mul, pow_two, hc'i, one_pow, one_mul]
    rw [hpow] at hk
    have h1 : c' ^ i ∈ Y' := by
      have : c' ^ i = (b ^ orderOf p)⁻¹ := eq_inv_of_mul_eq_one_left hk
      rw [this]
      exact Y'.inv_mem (Y'.pow_mem hb _)
    have h2 : c' ^ i = 1 := by
      have := hdisj.le_bot ⟨Subgroup.zpow_mem_zpowers c' i, h1⟩
      simpa using this
    rw [h2, one_mul] at hab
    have hp : p = (b : X) := by rw [hab]
    rw [hp]
    exact hYmem b hb
  have hYn : Y.Normal := by
    refine ⟨fun y hy x => ?_⟩
    have hyM : y ∈ M := hYM y hy
    have hyodd : Odd (orderOf y) := hYodd.of_dvd_nat (Y.orderOf_dvd_natCard hy)
    have hxyM : x * y * x⁻¹ ∈ M := hMn.conj_mem y hyM x
    have hord : orderOf (x * y * x⁻¹) = orderOf y := by
      have h := (MulAut.conj x).orderOf_eq y
      rw [MulAut.conj_apply] at h
      exact h
    exact hodd_mem _ hxyM (hord ▸ hyodd)
  refine ⟨Y, hYn, hYodd, ?_⟩
  intro x hx
  have hxM : x ∈ M := hx
  obtain ⟨a, ha, b, hb, hab⟩ := hdecomp ⟨x, hxM⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hxeq : x = (c ^ i) * (b : X) := by
    have := congrArg Subtype.val hab
    simpa [c'] using this.symm
  refine ⟨b, hYmem b hb, ?_⟩
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' i
  · left
    rw [hxeq, hk, zpow_mul, zpow_two, hc2, one_zpow, one_mul]
  · right
    rw [hxeq, hk, zpow_add, zpow_mul, zpow_two, hc2, one_zpow, one_mul, zpow_one]

end CFSG.OddStandard.SmallF3.Omega
