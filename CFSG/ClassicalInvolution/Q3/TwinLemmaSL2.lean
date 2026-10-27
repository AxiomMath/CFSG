module

public import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

namespace CFSG.ClassicalInvolution.Q3.Twin

open scoped MatrixGroups commutatorElement
open CFSG.ClassicalInvolution

private theorem sl2_eight_to_four : ∀ x : SL(2, ZMod 3), x ^ 8 = 1 → x ^ 4 = 1 := by
  decide +kernel

private theorem sl2_commutator_generate : ∀ g q : SL(2, ZMod 3), g ^ 3 = 1 → g ≠ 1 → q ^ 4 = 1 →
    ∃ a b : SL(2, ZMod 3), a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ q = ⁅a, g⁆ * ⁅b, g⁆ := by
  decide +kernel

private theorem sl2_quat_mul_zpowers : ∀ g : SL(2, ZMod 3), g ^ 3 = 1 → g ≠ 1 →
    ∀ x : SL(2, ZMod 3), ∃ a : SL(2, ZMod 3), ∃ k : Fin 3, a ^ 4 = 1 ∧ x = a * g ^ (k : ℕ) := by
  decide +kernel

private theorem sl2_two_generated : ∃ x y : SL(2, ZMod 3), x ^ 4 = 1 ∧ y ^ 4 = 1 ∧
    ∀ q : SL(2, ZMod 3), q ^ 4 = 1 → ∃ i j : Fin 4, q = x ^ (i : ℕ) * y ^ (j : ℕ) := by
  decide +kernel

private theorem sl2_generated_by_conjugate : ∀ g x : SL(2, ZMod 3), g ^ 3 = 1 → g ≠ 1 →
    x ^ 4 = 1 → x ^ 2 ≠ 1 → ∀ q : SL(2, ZMod 3), q ^ 4 = 1 →
      ∃ i j : Fin 4, q = x ^ (i : ℕ) * (g * x * g⁻¹) ^ (j : ℕ) := by
  decide +kernel

private theorem sl2_involution_unique : ∀ x y : SL(2, ZMod 3), x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 →
    y ≠ 1 → x = y := by
  decide +kernel

private theorem sl2_involution_central : ∀ x : SL(2, ZMod 3), x ^ 2 = 1 → x ≠ 1 →
    ∀ y : SL(2, ZMod 3), x * y = y * x := by
  decide +kernel

private theorem sl2_quat_noncomm :
    ∃ a b : SL(2, ZMod 3), a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ a * b ≠ b * a := by
  decide +kernel

section Abstract

variable {J : Type*} [Group J] (e : J ≃* SL(2, ZMod 3))

include e

@[expose] def quat : Subgroup J := sl2ThreeQ.map e.symm.toMonoidHom

theorem mem_quat {x : J} : x ∈ quat e ↔ x ^ 4 = 1 := by
  rw [quat, Subgroup.mem_map_equiv, MulEquiv.symm_symm, mem_sl2ThreeQ_iff, ← map_pow]
  exact ⟨fun h => e.injective (by simpa using h), fun h => by simp [h]⟩

theorem natCard_quat : Nat.card (quat e) = 8 := by
  rw [quat, Subgroup.card_map_of_injective e.symm.injective, natCard_sl2ThreeQ]

theorem natCard_of_equiv : Nat.card J = 24 := by
  rw [Nat.card_congr e.toEquiv, natCard_sl2Three]

theorem quat_normal : (quat e).Normal :=
  sl2ThreeQ_normal.map _ e.symm.surjective

theorem pow_four_of_pow_two_pow {x : J} {n : ℕ} (h : x ^ (2 ^ n) = 1) : x ^ 4 = 1 := by
  obtain ⟨m, hm, hmx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  have h24 : orderOf x ∣ 24 := natCard_of_equiv e ▸ orderOf_dvd_natCard x
  have hm3 : m ≤ 3 := by
    by_contra hm4
    have h16 : 2 ^ 4 ∣ 2 ^ m := Nat.pow_dvd_pow 2 (by omega)
    have := (h16.trans (hmx ▸ h24)).trans (dvd_refl 24)
    omega
  have h8 : x ^ 8 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hmx]
    exact Nat.pow_dvd_pow 2 hm3
  exact e.injective (by simpa using sl2_eight_to_four (e x) (by rw [← map_pow, h8, map_one]))

theorem quat_sup_zpowers {g : J} (hg : g ^ 3 = 1) (hg1 : g ≠ 1) :
    quat e ⊔ Subgroup.zpowers g = ⊤ := by
  have hg' : (e g) ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  have hg1' : e g ≠ 1 := fun h => hg1 (e.injective (by simpa using h))
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, k, ha, hx⟩ := sl2_quat_mul_zpowers (e g) hg' hg1' (e x)
  have hx' : x = e.symm a * g ^ (k : ℕ) := by
    apply e.injective
    rw [map_mul, map_pow, MulEquiv.apply_symm_apply, ← hx]
  rw [hx']
  refine Subgroup.mul_mem_sup ((mem_quat e).mpr ?_) (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _)
  exact e.injective (by simpa using ha)

theorem commutator_quat {g : J} (hg : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ⁅quat e, Subgroup.zpowers g⁆ = quat e := by
  have hg' : (e g) ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  have hg1' : e g ≠ 1 := fun h => hg1 (e.injective (by simpa using h))
  have := quat_normal e
  refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
  intro q hq
  obtain ⟨a, b, ha, hb, hab⟩ := sl2_commutator_generate (e g) (e q) hg' hg1'
    (by rw [← map_pow, (mem_quat e).mp hq, map_one])
  have ha' : e.symm a ∈ quat e := (mem_quat e).mpr (e.injective (by simpa using ha))
  have hb' : e.symm b ∈ quat e := (mem_quat e).mpr (e.injective (by simpa using hb))
  have hq' : q = ⁅e.symm a, g⁆ * ⁅e.symm b, g⁆ := by
    apply e.injective
    rw [map_mul, commutatorElement_def, commutatorElement_def]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hab, commutatorElement_def, commutatorElement_def]
  rw [hq']
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator ha' (Subgroup.mem_zpowers g))
    (Subgroup.commutator_mem_commutator hb' (Subgroup.mem_zpowers g))

theorem exists_closure_quat : ∃ x y : J, x ∈ quat e ∧ y ∈ quat e ∧
    Subgroup.closure ({x, y} : Set J) = quat e := by
  obtain ⟨x, y, hx, hy, h⟩ := sl2_two_generated
  refine ⟨e.symm x, e.symm y, (mem_quat e).mpr (e.injective (by simpa using hx)),
    (mem_quat e).mpr (e.injective (by simpa using hy)), le_antisymm ?_ ?_⟩
  · rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact (mem_quat e).mpr (e.injective (by simpa using hx))
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (mem_quat e).mpr (e.injective (by simpa using hy))
  · intro q hq
    obtain ⟨i, j, hij⟩ := h (e q) (by rw [← map_pow, (mem_quat e).mp hq, map_one])
    have : q = e.symm x ^ (i : ℕ) * e.symm y ^ (j : ℕ) := by
      apply e.injective
      rw [map_mul, map_pow, map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← hij]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem quat_le_closure {g x : J} (hg : g ^ 3 = 1) (hg1 : g ≠ 1) (hx : x ∈ quat e)
    (hx2 : x ^ 2 ≠ 1) : quat e ≤ Subgroup.closure ({x, g * x * g⁻¹} : Set J) := by
  have hg' : (e g) ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  have hg1' : e g ≠ 1 := fun h => hg1 (e.injective (by simpa using h))
  have hx' : (e x) ^ 4 = 1 := by rw [← map_pow, (mem_quat e).mp hx, map_one]
  have hx2' : (e x) ^ 2 ≠ 1 := fun h => hx2 (e.injective (by simpa using h))
  intro q hq
  obtain ⟨i, j, hij⟩ := sl2_generated_by_conjugate (e g) (e x) hg' hg1' hx' hx2' (e q)
    (by rw [← map_pow, (mem_quat e).mp hq, map_one])
  have : q = x ^ (i : ℕ) * (g * x * g⁻¹) ^ (j : ℕ) := by
    apply e.injective
    rw [hij]
    simp
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem involution_unique {x y : J} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x = y := by
  refine e.injective (sl2_involution_unique (e x) (e y) ?_ ?_ ?_ ?_)
  · rw [← map_pow, hx, map_one]
  · rw [← map_pow, hy, map_one]
  · exact fun h => hx1 (e.injective (by simpa using h))
  · exact fun h => hy1 (e.injective (by simpa using h))

theorem involution_central {x : J} (hx : x ^ 2 = 1) (hx1 : x ≠ 1) (y : J) : x * y = y * x := by
  refine e.injective ?_
  rw [map_mul, map_mul]
  exact sl2_involution_central (e x) (by rw [← map_pow, hx, map_one])
    (fun h => hx1 (e.injective (by simpa using h))) (e y)

theorem exists_noncomm_quat : ∃ a b : J, a ∈ quat e ∧ b ∈ quat e ∧ a * b ≠ b * a := by
  obtain ⟨a, b, ha, hb, hab⟩ := sl2_quat_noncomm
  refine ⟨e.symm a, e.symm b, (mem_quat e).mpr (e.injective (by simpa using ha)),
    (mem_quat e).mpr (e.injective (by simpa using hb)), fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem isSolvable_of_equiv : Group.IsSolvable J := by
  have : Finite J := Finite.of_equiv SL(2, ZMod 3) e.symm.toEquiv
  have hp : IsPGroup 2 (quat e) := IsPGroup.of_card (n := 3) (by rw [natCard_quat]; norm_num)
  have : Group.IsNilpotent (quat e) := hp.isNilpotent
  have := quat_normal e
  have : Group.IsSolvable (J ⧸ quat e) := by
    have hc : Nat.card (J ⧸ quat e) = 3 := by
      have h := Subgroup.card_mul_index (quat e)
      rw [natCard_quat, natCard_of_equiv e] at h
      rw [Subgroup.index] at h
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic (J ⧸ quat e) := isCyclic_of_prime_card hc
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (quat e)

theorem le_quat_of_isPGroup {Q : Subgroup J} (hQ : IsPGroup 2 Q) : Q ≤ quat e := by
  intro x hx
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  rw [mem_quat]
  refine pow_four_of_pow_two_pow e (n := k) ?_
  have := congrArg Subtype.val hk
  simpa using this

end Abstract

section Ambient

variable {Y : Type*} [Group Y] {J : Subgroup Y} (e : J ≃* SL(2, ZMod 3))

include e

@[expose] def quatIn : Subgroup Y := (quat e).map J.subtype

theorem mem_quatIn {y : Y} : y ∈ quatIn e ↔ y ∈ J ∧ y ^ 4 = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have := congrArg Subtype.val ((mem_quat e).mp hx)
    simpa using this
  · rintro ⟨hy, hy4⟩
    exact ⟨⟨y, hy⟩, (mem_quat e).mpr (Subtype.ext (by simpa using hy4)), rfl⟩

theorem quatIn_le : quatIn e ≤ J := fun _ hy => ((mem_quatIn e).mp hy).1

theorem natCard_quatIn : Nat.card (quatIn e) = 8 := by
  rw [quatIn, Subgroup.card_map_of_injective J.subtype_injective, natCard_quat]

theorem natCard_subgroup : Nat.card J = 24 := natCard_of_equiv e

theorem isPGroup_quatIn : IsPGroup 2 (quatIn e) :=
  IsPGroup.of_card (n := 3) (by rw [natCard_quatIn]; norm_num)

theorem conj_mem_quatIn {j q : Y} (hj : j ∈ J) (hq : q ∈ quatIn e) : j * q * j⁻¹ ∈ quatIn e := by
  rw [mem_quatIn] at hq ⊢
  refine ⟨J.mul_mem (J.mul_mem hj hq.1) (J.inv_mem hj), ?_⟩
  rw [conj_pow, hq.2, mul_one, mul_inv_cancel]

theorem mem_quatIn_of_pow_two_pow {y : Y} (hy : y ∈ J) {n : ℕ} (h : y ^ (2 ^ n) = 1) :
    y ∈ quatIn e := by
  rw [mem_quatIn]
  refine ⟨hy, ?_⟩
  have := pow_four_of_pow_two_pow e (x := (⟨y, hy⟩ : J)) (n := n) (Subtype.ext (by simpa using h))
  simpa using congrArg Subtype.val this

theorem quatIn_sup_zpowers {s : Y} (hs : s ∈ J) (h3 : s ^ 3 = 1) (h1 : s ≠ 1) :
    quatIn e ⊔ Subgroup.zpowers s = J := by
  have h := quat_sup_zpowers e (g := (⟨s, hs⟩ : J)) (Subtype.ext (by simpa using h3))
    (fun h => h1 (congrArg Subtype.val h))
  have := congrArg (Subgroup.map J.subtype) h
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype] at this
  simpa [quatIn] using this

theorem commutator_quatIn {s : Y} (hs : s ∈ J) (h3 : s ^ 3 = 1) (h1 : s ≠ 1) :
    ⁅quatIn e, Subgroup.zpowers s⁆ = quatIn e := by
  have h := commutator_quat e (g := (⟨s, hs⟩ : J)) (Subtype.ext (by simpa using h3))
    (fun h => h1 (congrArg Subtype.val h))
  have := congrArg (Subgroup.map J.subtype) h
  rwa [Subgroup.map_commutator, MonoidHom.map_zpowers] at this

theorem exists_closure_quatIn : ∃ x y : Y, x ∈ quatIn e ∧ y ∈ quatIn e ∧
    Subgroup.closure ({x, y} : Set Y) = quatIn e := by
  obtain ⟨x, y, hx, hy, h⟩ := exists_closure_quat e
  refine ⟨x, y, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ?_⟩
  have := congrArg (Subgroup.map J.subtype) h
  rw [MonoidHom.map_closure, Set.image_pair] at this
  exact this

theorem quatIn_le_closure {s x : Y} (hs : s ∈ J) (h3 : s ^ 3 = 1) (h1 : s ≠ 1)
    (hx : x ∈ quatIn e) (hx2 : x ^ 2 ≠ 1) :
    quatIn e ≤ Subgroup.closure ({x, s * x * s⁻¹} : Set Y) := by
  have hxJ : x ∈ J := quatIn_le e hx
  have hxq : (⟨x, hxJ⟩ : J) ∈ quat e :=
    (mem_quat e).mpr (Subtype.ext (by simpa using ((mem_quatIn e).mp hx).2))
  have h := quat_le_closure e (g := (⟨s, hs⟩ : J)) (x := ⟨x, hxJ⟩)
    (Subtype.ext (by simpa using h3)) (fun h => h1 (congrArg Subtype.val h)) hxq
    (fun h => hx2 (by simpa using congrArg Subtype.val h))
  have := Subgroup.map_mono (f := J.subtype) h
  rw [MonoidHom.map_closure] at this
  refine le_trans ?_ (le_trans this (le_of_eq ?_))
  · intro q hq
    exact ⟨⟨q, quatIn_le e hq⟩,
      (mem_quat e).mpr (Subtype.ext (by simpa using ((mem_quatIn e).mp hq).2)), rfl⟩
  · congr 1
    ext w
    simp

theorem isSolvable_subgroup : Group.IsSolvable J := isSolvable_of_equiv e

theorem eq_quatIn_of_card_eq {Q : Subgroup Y} (hQJ : Q ≤ J) (hQ : IsPGroup 2 Q)
    (hc : Nat.card Q = 8) : Q = quatIn e := by
  have hQ' : IsPGroup 2 (Q.subgroupOf J) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQJ).symm
  have h := le_quat_of_isPGroup e hQ'
  have hle : Q ≤ quatIn e := fun x hx => ⟨⟨x, hQJ hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have : Finite (quatIn e) := Nat.finite_of_card_ne_zero (by rw [natCard_quatIn e]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_quatIn e, hc])

theorem involution_unique_in {x y : Y} (hxJ : x ∈ J) (hyJ : y ∈ J) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have := involution_unique e (x := ⟨x, hxJ⟩) (y := ⟨y, hyJ⟩) (Subtype.ext (by simpa using hx))
    (Subtype.ext (by simpa using hy)) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem involution_central_in {z : Y} (hzJ : z ∈ J) (hz : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∀ j ∈ J, z * j = j * z := by
  intro j hj
  have := involution_central e (x := ⟨z, hzJ⟩) (Subtype.ext (by simpa using hz))
    (fun h => hz1 (congrArg Subtype.val h)) ⟨j, hj⟩
  exact congrArg Subtype.val this

theorem involution_mem_quatIn {z : Y} (hzJ : z ∈ J) (hz : z ^ 2 = 1) : z ∈ quatIn e := by
  rw [mem_quatIn]
  refine ⟨hzJ, ?_⟩
  rw [show 4 = 2 * 2 by norm_num, pow_mul, hz, one_pow]

theorem exists_noncomm_quatIn : ∃ a b : Y, a ∈ quatIn e ∧ b ∈ quatIn e ∧ a * b ≠ b * a := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_noncomm_quat e
  refine ⟨a, b, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, fun h => hab (Subtype.ext h)⟩

end Ambient

end CFSG.ClassicalInvolution.Q3.Twin
