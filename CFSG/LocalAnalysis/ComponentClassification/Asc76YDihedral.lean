module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YThm3

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G]

structure IsDihedralRot (U R : Subgroup G) : Prop where
  le : U ≤ R
  isCyclic : IsCyclic U
  relIndex_eq : U.relIndex R = 2
  four_le : 4 ≤ Nat.card U
  isPGroup : IsPGroup 2 R
  mul_self : ∀ x ∈ R, x ∉ U → x * x = 1
  conj_eq : ∀ x ∈ R, x ∉ U → ∀ u ∈ U, x * u * x⁻¹ = u⁻¹

theorem dihedralGroup_r_or_sr {m : ℕ} (x : DihedralGroup m) :
    (∃ i, x = DihedralGroup.r i) ∨ ∃ i, x = DihedralGroup.sr i := by
  rcases x with i | i
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

theorem exists_isDihedralRot [Finite G] {R : Subgroup G} (hR : IsDihedralTwoGroup R)
    (hRc : ¬ IsMulCommutative R) : ∃ U, IsDihedralRot U R := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hR
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn2 : n = 2 := by omega
    subst hn2
    have : IsMulCommutative (DihedralGroup (2 ^ (2 - 1))) :=
      DihedralGroup.commutative_iff.mpr (Or.inr rfl)
    exact hRc (isMulCommutative_of_mulEquiv e)
  set m := 2 ^ (n - 1) with hm
  have hm4 : 4 ≤ m := by
    rw [hm]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero m := ⟨by omega⟩
  set r₁ : R := e.symm (DihedralGroup.r 1) with hr₁
  set ρ : G := (r₁ : G) with hρ
  have hρR : ρ ∈ R := r₁.2
  have hord : orderOf ρ = m := by
    rw [hρ, Subgroup.orderOf_coe, hr₁, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hcardR : Nat.card R = 2 * m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hUR : zpowers ρ ≤ R := (zpowers_le).mpr hρR
  have hcardU : Nat.card (zpowers ρ) = m := by rw [Nat.card_zpowers, hord]
  have hsr : ∀ x (hx : x ∈ R), x ∉ zpowers ρ → ∃ i, e ⟨x, hx⟩ = DihedralGroup.sr i := by
    intro x hx hxU
    rcases dihedralGroup_r_or_sr (e ⟨x, hx⟩) with ⟨i, hi⟩ | hi
    · exfalso
      apply hxU
      have hx' : (⟨x, hx⟩ : R) = r₁ ^ i.val := by
        rw [hr₁, ← map_pow, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val, ← hi,
          e.symm_apply_apply]
      refine ⟨(i.val : ℤ), ?_⟩
      have := congrArg Subtype.val hx'
      simp only [Subgroup.coe_pow] at this
      simp only [zpow_natCast]
      rw [hρ, this]
    · exact hi
  refine ⟨zpowers ρ, hUR, inferInstance, ?_, by omega, ?_, ?_, ?_⟩
  · have h1 := Subgroup.relIndex_mul_card (zpowers ρ) R
    rw [inf_eq_left.mpr hUR, hcardU, hcardR] at h1
    have hm0 : 0 < m := by omega
    exact Nat.eq_of_mul_eq_mul_right hm0 h1
  · apply IsPGroup.of_card (n := n)
    rw [hcardR, hm, ← pow_succ']
    congr 1
    omega
  · intro x hx hxU
    obtain ⟨i, hi⟩ := hsr x hx hxU
    have h1 : (⟨x, hx⟩ : R) * ⟨x, hx⟩ = 1 := by
      apply e.injective
      rw [map_mul, hi, DihedralGroup.sr_mul_sr, sub_self, map_one, DihedralGroup.r_zero]
    exact congrArg Subtype.val h1
  · intro x hx hxU u hu
    obtain ⟨i, hi⟩ := hsr x hx hxU
    have h1 : (⟨x, hx⟩ : R) * r₁ * (⟨x, hx⟩ : R)⁻¹ = r₁⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, hi, hr₁, e.apply_symm_apply,
        DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_r]
      congr 1
      ring
    have h2 : x * ρ * x⁻¹ = ρ⁻¹ := congrArg Subtype.val h1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← conj_zpow, h2, inv_zpow]

namespace IsDihedralRot

variable {U R : Subgroup G}

theorem card_eq (h : IsDihedralRot U R) : Nat.card R = 2 * Nat.card U := by
  have h1 := Subgroup.relIndex_mul_card U R
  rw [inf_eq_left.mpr h.le, h.relIndex_eq] at h1
  exact h1.symm

theorem mem_of_mul_self_ne_one (h : IsDihedralRot U R) {x : G} (hx : x ∈ R)
    (hx1 : x * x ≠ 1) : x ∈ U := by
  by_contra hxU
  exact hx1 (h.mul_self x hx hxU)

theorem exists_gen (h : IsDihedralRot U R) : ∃ ρ : G, zpowers ρ = U ∧ orderOf ρ = Nat.card U := by
  obtain ⟨ρ, hρ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top U).mp h.isCyclic
  refine ⟨ρ, hρ, ?_⟩
  rw [← hρ, Nat.card_zpowers]

theorem commute_of_mem (h : IsDihedralRot U R) {u v : G} (hu : u ∈ U) (hv : v ∈ U) :
    u * v = v * u := by
  obtain ⟨ρ, hρ, -⟩ := h.exists_gen
  rw [← hρ] at hu hv
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← zpow_add, ← zpow_add, add_comm]

theorem mul_mem_of_not_mem (h : IsDihedralRot U R) {x y : G} (hx : x ∈ R) (hy : y ∈ R)
    (hxU : x ∉ U) (hyU : y ∉ U) : x * y ∈ U := by
  have hidx : (U.subgroupOf R).index = 2 := h.relIndex_eq
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
    (iff_of_false (by simpa [Subgroup.mem_subgroupOf] using hxU)
      (by simpa [Subgroup.mem_subgroupOf] using hyU))
  simpa [Subgroup.mem_subgroupOf] using this

theorem exists_not_mem (h : IsDihedralRot U R) : ∃ s ∈ R, s ∉ U := by
  have hle : ¬ R ≤ U := by
    intro hle
    have h1 := h.relIndex_eq
    rw [Subgroup.relIndex_eq_one.mpr hle] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨s, hsR, hsU⟩ := Set.not_subset.mp hle
  exact ⟨s, hsR, hsU⟩

theorem gen_mul_self_ne_one (h : IsDihedralRot U R) {ρ : G} (hρ : orderOf ρ = Nat.card U) :
    ρ * ρ ≠ 1 := by
  intro h1
  have h2 : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
  have := Nat.le_of_dvd (by norm_num) h2
  have := h.four_le
  omega

theorem eq_of_isCyclic (h : IsDihedralRot U R) {U' : Subgroup G} (hle : U' ≤ R)
    (hcyc : IsCyclic U') (hidx : U'.relIndex R = 2) : U' = U := by
  have hcard : Nat.card U' = Nat.card U := by
    have h1 := Subgroup.relIndex_mul_card U' R
    rw [inf_eq_left.mpr hle, hidx, h.card_eq] at h1
    omega
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top U').mp hcyc
  have hgo : orderOf g = Nat.card U := by rw [← hcard, ← hg, Nat.card_zpowers]
  have hgR : g ∈ R := hle (hg ▸ mem_zpowers g)
  have hgU : g ∈ U := h.mem_of_mul_self_ne_one hgR (h.gen_mul_self_ne_one hgo)
  have hle' : U' ≤ U := hg ▸ (zpowers_le).mpr hgU
  have : Finite U := by
    have := h.isPGroup
    exact Nat.finite_of_card_ne_zero (by have := h.four_le; omega)
  exact Subgroup.eq_of_le_of_card_ge hle' hcard.ge

theorem rightConjugate (h : IsDihedralRot U R) (g : G) :
    IsDihedralRot (rightConjugate U g) (rightConjugate R g) := by
  obtain ⟨ρ, hρ, -⟩ := h.exists_gen
  refine ⟨rightConjugate_le_rightConjugate h.le g, ?_, ?_, ?_, isPGroup_rightConjugate h.isPGroup g,
    ?_, ?_⟩
  · rw [← hρ, AschbacherTightEmbedding.rightConjugate, MonoidHom.map_zpowers]
    infer_instance
  · rw [relIndex_rightConjugate, h.relIndex_eq]
  · rw [rightConjugate_card]; exact h.four_le
  · intro x hx hxU
    rw [mem_rightConjugate_iff] at hx hxU
    have h1 := h.mul_self _ hx hxU
    have : x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
    rw [this, h1]; group
  · intro x hx hxU u hu
    rw [mem_rightConjugate_iff] at hx hxU hu
    have h1 := h.conj_eq _ hx hxU _ hu
    have : x * u * x⁻¹ = g⁻¹ * ((g * x * g⁻¹) * (g * u * g⁻¹) * (g * x * g⁻¹)⁻¹) * g := by group
    rw [this, h1]; group

theorem normalizer_le (h : IsDihedralRot U R) :
    normalizer (R : Set G) ≤ normalizer (U : Set G) := by
  intro g hg
  have hR : AschbacherTightEmbedding.rightConjugate R g = R :=
    (rightConjugate_eq_self_iff R g).mpr hg
  have h' := h.rightConjugate g
  rw [hR] at h'
  exact (rightConjugate_eq_self_iff U g).mp (h.eq_of_isCyclic h'.le h'.isCyclic h'.relIndex_eq)

theorem mem_of_commute (h : IsDihedralRot U R) {x : G} (hx : x ∈ R)
    (hc : ∀ u ∈ U, x * u = u * x) : x ∈ U := by
  by_contra hxU
  obtain ⟨ρ, hρ, hρo⟩ := h.exists_gen
  have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
  have h1 := h.conj_eq x hx hxU ρ hρU
  rw [hc ρ hρU, mul_assoc, mul_inv_cancel, mul_one] at h1
  apply h.gen_mul_self_ne_one hρo
  calc ρ * ρ = ρ⁻¹ * ρ := by rw [← h1]
    _ = 1 := inv_mul_cancel ρ

theorem exists_involution [Finite G] (h : IsDihedralRot U R) :
    ∃ z ∈ U, z ≠ 1 ∧ z * z = 1 ∧ (∀ y ∈ U, y * y = 1 → y = 1 ∨ y = z) ∧
      ∀ x ∈ R, x * z = z * x := by
  obtain ⟨ρ, hρ, hρo⟩ := h.exists_gen
  have hq4 := h.four_le
  set q := Nat.card U with hq
  have hqeven : 2 ∣ q := by
    have h1 : q ∣ Nat.card R := ⟨2, by rw [h.card_eq]; ring⟩
    obtain ⟨k, hk⟩ := h.isPGroup.exists_card_eq
    rw [hk] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rw [hj]
    have : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      omega
    exact dvd_pow_self 2 this
  obtain ⟨t, ht⟩ := hqeven
  have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
  have hzU : ρ ^ t ∈ U := U.pow_mem hρU t
  have hz1 : ρ ^ t ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hzz : ρ ^ t * ρ ^ t = 1 := by
    rw [← pow_add, ← two_mul, ← ht, ← hρo, pow_orderOf_eq_one]
  refine ⟨ρ ^ t, hzU, hz1, hzz, ?_, ?_⟩
  · intro y hy hyy
    rw [← hρ] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : ρ ^ (2 * k) = 1 := by rw [two_mul, zpow_add, hyy]
    rw [orderOf_dvd_iff_zpow_eq_one.symm, hρo, ht] at h1
    have h2 : (t : ℤ) ∣ k := by
      have h3 : ((2 * t : ℕ) : ℤ) = 2 * (t : ℤ) := by push_cast; ring
      rw [h3] at h1
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h1
    obtain ⟨j, rfl⟩ := h2
    rcases Int.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · left
      rw [zpow_mul, show i + i = 2 * i by ring, zpow_mul, zpow_natCast, zpow_ofNat, pow_two, hzz,
        one_zpow]
    · right
      rw [zpow_mul, zpow_natCast, zpow_add, zpow_mul, zpow_ofNat, pow_two, hzz, one_zpow, one_mul,
        zpow_one]
  · intro x hx
    by_cases hxU : x ∈ U
    · exact h.commute_of_mem hxU hzU
    · have h1 := h.conj_eq x hx hxU _ hzU
      have hzinv : (ρ ^ t)⁻¹ = ρ ^ t := inv_eq_of_mul_eq_one_right hzz
      rw [hzinv] at h1
      calc x * ρ ^ t = x * ρ ^ t * x⁻¹ * x := by group
        _ = ρ ^ t * x := by rw [h1]

theorem eq_of_central (h : IsDihedralRot U R) {z : G}
    (hz : ∀ y ∈ U, y * y = 1 → y = 1 ∨ y = z) {x : G} (hx : x ∈ R)
    (hc : ∀ y ∈ R, x * y = y * x) : x = 1 ∨ x = z := by
  have hxU : x ∈ U := h.mem_of_commute hx fun u hu => hc u (h.le hu)
  obtain ⟨s, hsR, hsU⟩ := h.exists_not_mem
  have h1 := h.conj_eq s hsR hsU x hxU
  rw [← hc s hsR, mul_assoc, mul_inv_cancel, mul_one] at h1
  apply hz x hxU
  calc x * x = x⁻¹ * x := by rw [← h1]
    _ = 1 := inv_mul_cancel x

theorem le_or_mul_self (h : IsDihedralRot U R) {A : Subgroup G} (hAR : A ≤ R)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A ≤ U ∨ ∀ a ∈ A, a * a = 1 := by
  by_cases hle : A ≤ U
  · exact Or.inl hle
  right
  obtain ⟨s, hsA, hsU⟩ := Set.not_subset.mp hle
  intro a ha
  by_cases haU : a ∈ U
  · have h1 := h.conj_eq s (hAR hsA) hsU a haU
    rw [hA s hsA a ha, mul_assoc, mul_inv_cancel, mul_one] at h1
    calc a * a = a⁻¹ * a := by rw [← h1]
      _ = 1 := inv_mul_cancel a
  · exact h.mul_self a (hAR ha) haU

theorem card_eq_four (h : IsDihedralRot U R) {A : Subgroup G} (hAR : A ≤ R)
    (hAn : R ≤ normalizer (A : Set G)) (hA2 : ∀ a ∈ A, a * a = 1) (hAU : ¬ A ≤ U) :
    Nat.card U = 4 := by
  obtain ⟨s, hsA, hsU⟩ := Set.not_subset.mp hAU
  obtain ⟨ρ, hρ, hρo⟩ := h.exists_gen
  have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
  have hρR : ρ ∈ R := h.le hρU
  have h1 : ρ * s * ρ⁻¹ ∈ A := (mem_normalizer_iff.mp (hAn hρR) s).mp hsA
  have h2 : s * (ρ * s * ρ⁻¹) ∈ A := A.mul_mem hsA h1
  have hsinv := h.conj_eq s (hAR hsA) hsU ρ hρU
  have hss : s * s = 1 := h.mul_self s (hAR hsA) hsU
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have h3 : s * (ρ * s * ρ⁻¹) = ρ⁻¹ * ρ⁻¹ := by
    calc s * (ρ * s * ρ⁻¹) = (s * ρ * s⁻¹) * ρ⁻¹ := by rw [hs1]; group
      _ = ρ⁻¹ * ρ⁻¹ := by rw [hsinv]
  rw [h3] at h2
  have h4 := hA2 _ h2
  have h5 : ρ ^ 4 = 1 := by
    have : ρ ^ 4 = (ρ⁻¹ * ρ⁻¹ * (ρ⁻¹ * ρ⁻¹))⁻¹ := by group
    rw [this, h4, inv_one]
  have h6 : orderOf ρ ∣ 4 := orderOf_dvd_of_pow_eq_one h5
  rw [hρo] at h6
  have := Nat.le_of_dvd (by norm_num) h6
  have := h.four_le
  omega

end IsDihedralRot

end CFSG.ComponentClassification.Asc76.Sec4
