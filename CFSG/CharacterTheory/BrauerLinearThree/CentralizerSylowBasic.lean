module

public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.BrauerLinearThree

open CFSG.Open

theorem exists_odd_eq_two_pow_factorization_mul {n : ℕ} (hn : n ≠ 0) :
    ∃ u, Odd u ∧ n = 2 ^ n.factorization 2 * u := by
  refine ⟨n / 2 ^ n.factorization 2, ?_, (Nat.ordProj_mul_ordCompl_eq_self n 2).symm⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact Nat.not_dvd_ordCompl Nat.prime_two hn

theorem semidihedral_arith {q : ℕ} (hq : q % 4 = 3) :
    2 ≤ (q + 1).factorization 2 ∧
      (∃ j, q = 2 ^ ((q + 1).factorization 2 + 1) * j + (2 ^ (q + 1).factorization 2 - 1)) ∧
      2 ^ ((q + 1).factorization 2 + 1) ∣ q ^ 2 - 1 ∧
      ∃ w, Odd w ∧ q * (q - 1) ^ 2 * (q + 1) = 2 ^ ((q + 1).factorization 2 + 2) * w := by
  set m := (q + 1).factorization 2 with hm
  obtain ⟨v, hv, hqv⟩ := exists_odd_eq_two_pow_factorization_mul (n := q + 1) (by omega)
  rw [← hm] at hqv
  obtain ⟨u, hu⟩ : ∃ u, q - 1 = 2 * (2 * u + 1) := ⟨(q - 3) / 4, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm, ← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  · obtain ⟨j, rfl⟩ := hv
    refine ⟨j, ?_⟩
    have h1 : 2 ^ m * (2 * j + 1) = 2 * (2 ^ m * j) + 2 ^ m := by ring
    have h2 : 2 ^ (m + 1) * j = 2 * (2 ^ m * j) := by ring
    have h3 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  · have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      have : (r + 1) ^ 2 = (r + 1 - 1) * (r + 1 + 1) + 1 := by rw [Nat.add_sub_cancel]; ring
      omega
    rw [e, hu, hqv]
    exact ⟨(2 * u + 1) * v, by ring⟩
  · refine ⟨q * (2 * u + 1) ^ 2 * v, ?_, ?_⟩
    · exact ((Nat.odd_iff.mpr (by omega)).mul ((odd_two_mul_add_one u).pow)).mul hv
    · rw [hu, hqv]
      ring

theorem wreathed_arith {q : ℕ} (hq : q % 4 = 1) (hq1 : 1 < q) :
    2 ≤ (q - 1).factorization 2 ∧ 2 ^ (q - 1).factorization 2 ∣ q - 1 ∧
      ∃ w, Odd w ∧ q * (q - 1) ^ 2 * (q + 1) = 2 ^ (2 * (q - 1).factorization 2 + 1) * w := by
  set k := (q - 1).factorization 2 with hk
  obtain ⟨u, hu, hqu⟩ := exists_odd_eq_two_pow_factorization_mul (n := q - 1) (by omega)
  rw [← hk] at hqu
  obtain ⟨v, hv⟩ : ∃ v, q + 1 = 2 * (2 * v + 1) := ⟨(q - 1) / 4, by omega⟩
  refine ⟨?_, ⟨u, hqu⟩, ?_⟩
  · rw [hk, ← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  · refine ⟨q * u ^ 2 * (2 * v + 1), ?_, ?_⟩
    · exact ((Nat.odd_iff.mpr (by omega)).mul hu.pow).mul (odd_two_mul_add_one v)
    · rw [hqu, hv]
      ring

theorem exists_sylow_map_subtype_eq {G : Type*} [Group G] {H P : Subgroup G} (hPH : P ≤ H)
    {a z w : ℕ} (hP : Nat.card P = 2 ^ a) (hw : Odd w) (hH : Nat.card H * z = 2 ^ a * w) :
    ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' := P.subgroupOf H with hP'
  have hcard : Nat.card P' = 2 ^ a := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  have hp : IsPGroup 2 P' := IsPGroup.of_card hcard
  have hidx : ¬ 2 ∣ P'.index := by
    have h1 := Subgroup.card_mul_index P'
    rw [hcard] at h1
    rw [← h1, mul_assoc] at hH
    have h3 : P'.index * z = w := Nat.eq_of_mul_eq_mul_left (by positivity) hH
    intro h2
    have : 2 ∣ w := h3 ▸ Dvd.dvd.mul_right h2 z
    exact (Nat.not_even_iff_odd.mpr hw) (even_iff_two_dvd.mpr this)
  refine ⟨hp.toSylow hidx, ?_⟩
  rw [IsPGroup.toSylow_coe, hP', Subgroup.subgroupOf_map_subtype, inf_of_le_left hPH]

theorem eq_one_of_mem_odd_of_pow_two_pow {H : Type*} [Group H] {Z : Subgroup H}
    (hZodd : Odd (Nat.card Z)) {x : H} (hx : x ∈ Z) {j : ℕ} (hxj : x ^ 2 ^ j = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hxj
  have h2 : orderOf x ∣ Nat.card Z := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ j) (Nat.card Z) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hZodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem units_eq_neg_one_of_orderOf_eq_two {K : Type*} [Field K] {x : Kˣ} (hx : orderOf x = 2) :
    x = -1 := by
  have h2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have h1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hK : (x : K) * (x : K) = 1 := by
    rw [← Units.val_mul, ← sq, h2, Units.val_one]
  rcases mul_self_eq_one_iff.mp hK with h | h
  · exact absurd (Units.ext h) h1
  · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])

theorem exists_orderOf_eq_of_dvd_natCard {α : Type*} [Group α] [Finite α] [IsCyclic α] {d : ℕ}
    (hd : d ∣ Nat.card α) : ∃ a : α, orderOf a = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := α)
  have hpos : 0 < Nat.card α := Nat.card_pos
  obtain ⟨e, he⟩ := hd
  have he0 : e ≠ 0 := by rintro rfl; rw [mul_zero] at he; omega
  refine ⟨g ^ e, ?_⟩
  rw [orderOf_pow_of_dvd he0 ⟨d, by rw [hg, he, mul_comm]⟩, hg, he,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero he0)]

theorem semidihedral_sup_zpowers {P : Type*} [Group P] {m : ℕ} (hm : 2 ≤ m) {h t : P}
    (hh : orderOf h = 2 ^ (m + 1)) (ht : t ^ 2 = 1) (hconj : t * h * t⁻¹ = h ^ (2 ^ m - 1)) :
    Nat.card (Subgroup.zpowers h ⊔ Subgroup.zpowers t : Subgroup P) = 2 ^ (m + 2) ∧
      ∃ e : SemidihedralGroup (m + 2) ≃* (Subgroup.zpowers h ⊔ Subgroup.zpowers t : Subgroup P),
        (e (CFSG.Semidihedral.r (m + 2)) : P) = h ∧
          (e (CFSG.Semidihedral.s (m + 2)) : P) = t := by
  set H : Subgroup P := Subgroup.zpowers h ⊔ Subgroup.zpowers t with hH
  let f : SemidihedralGroup (m + 2) →* P := PresentedGroup.toGroup (f := ![h, t]) (by
    intro w hw
    simp only [semidihedralRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero]
      rw [show m + 2 - 1 = m + 1 by omega, ← hh, pow_orderOf_eq_one]
    · simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
        Matrix.cons_val_zero] using ht
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [show m + 2 - 2 = m by omega, hconj, mul_inv_cancel])
  have hf0 : f (CFSG.Semidihedral.r (m + 2)) = h := by simp [f]
  have hf1 : f (CFSG.Semidihedral.s (m + 2)) = t := by simp [f]
  have hrange : f.range = H := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
        Subgroup.closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      fin_cases i
      · exact Subgroup.mem_sup_left (by simp [f])
      · exact Subgroup.mem_sup_right (by simp [f])
    · exact sup_le (Subgroup.zpowers_le.mpr ⟨_, hf0⟩) (Subgroup.zpowers_le.mpr ⟨_, hf1⟩)
  have : Finite (SemidihedralGroup (m + 2)) :=
    CFSG.Semidihedral.presentation_finite (m + 2) (by omega)
  have hSD : Nat.card (SemidihedralGroup (m + 2)) = 2 ^ (m + 2) :=
    CFSG.Semidihedral.card (m + 2) (by omega)
  have hle : Nat.card f.range ≤ 2 ^ (m + 2) := by
    rw [← hSD]
    exact Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have : Finite H := hrange ▸ this
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have htnot : t ∉ Subgroup.zpowers h := by
    intro htm
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp htm
    have hc : h ^ j * h * (h ^ j)⁻¹ = h := by
      rw [(Commute.zpow_self h j).eq, mul_inv_cancel_right]
    rw [hc] at hconj
    have h1 : h ^ (2 ^ m - 2) = 1 := by
      rw [show 2 ^ m - 1 = (2 ^ m - 2) + 1 by omega, pow_succ] at hconj
      exact mul_eq_right.mp hconj.symm
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hh] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    rw [pow_succ] at this
    omega
  have hcardH : Nat.card H = 2 ^ (m + 2) := by
    have hzle : Subgroup.zpowers h ≤ H := le_sup_left
    obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hzle
    rw [Nat.card_zpowers, hh] at hj
    have hHle : Nat.card H ≤ 2 ^ (m + 2) := hrange ▸ hle
    have hj1 : j ≠ 1 := by
      rintro rfl
      apply htnot
      have heq : Subgroup.zpowers h = H := Subgroup.eq_of_le_of_card_ge hzle (by
        rw [hj, mul_one, Nat.card_zpowers, hh])
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hj
      exact (Nat.card_pos (α := H)).ne' hj
    have hj2 : j ≤ 2 := by
      rw [hj, pow_succ 2 (m + 1)] at hHle
      exact Nat.le_of_mul_le_mul_left hHle (by positivity)
    rw [hj, show j = 2 by omega, ← pow_succ]
  have hinj : Function.Injective f := by
    have hbij : Function.Bijective f.rangeRestrict :=
      ⟨(Function.Surjective.bijective_of_nat_card_le f.rangeRestrict_surjective
        (by rw [hSD, hrange, hcardH])).1, f.rangeRestrict_surjective⟩
    intro x y hxy
    exact hbij.1 (Subtype.ext hxy)
  refine ⟨hcardH, (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), ?_, ?_⟩
  · simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
    exact hf0
  · simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
    exact hf1

end CFSG.BrauerLinearThree
