module

public import CFSG.Quasithin.Recognition.M12AscTrans
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open scoped commutatorElement

namespace SD46

theorem index_ne_two_of_perfect {J : Type*} [Group J] [Group.IsPerfect J] (N : Subgroup J) :
    N.index ≠ 2 := by
  intro hN
  have h : commutator J ≤ N := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    rw [commutatorElement_def, mul_mem_iff_of_index_two hN, mul_mem_iff_of_index_two hN,
      mul_mem_iff_of_index_two hN, inv_mem_iff, inv_mem_iff]
    tauto
  rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at h
  rw [h, index_top] at hN
  exact absurd hN (by norm_num)

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {g x : G}
    (hg : orderOf g = 2) (hx : x ∈ zpowers g) : x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hg]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem eq_one_of_mem_of_odd {G : Type*} [Group G] {N : Subgroup G} (hN : Odd (Nat.card ↥N))
    {g : G} (hg : g ∈ N) (hg2 : g ^ 2 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  have h2 : orderOf g ∣ Nat.card ↥N := by
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime 2 (Nat.card ↥N) := Nat.coprime_two_left.mpr hN
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

variable {C : Type*} [Group C] [Finite C]

theorem eq_of_orderOf_eq_two_of_perfect {β : C} (hβ : β ∈ center C) (hβ2 : orderOf β = 2)
    (hSD : ∀ R : Sylow 2 C, ∃ n, 4 ≤ n ∧
      Nonempty (↥(R : Subgroup C) ≃* Open.SemidihedralGroup n))
    {J : Subgroup C} (hJ : Group.IsPerfect ↥J) {x : C} (hxJ : x ∈ J) (hx2 : orderOf x = 2) :
    x = β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hx1 : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  have hxp : IsPGroup 2 (zpowers (⟨x, hxJ⟩ : ↥J)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2, pow_one])
  obtain ⟨T, hxT⟩ := hxp.exists_le_sylow
  have hxT' : (⟨x, hxJ⟩ : ↥J) ∈ (T : Subgroup ↥J) := hxT (mem_zpowers _)
  set T' : Subgroup C := (T : Subgroup ↥J).map J.subtype with hT'
  have hxT'' : x ∈ T' := ⟨⟨x, hxJ⟩, hxT', rfl⟩
  obtain ⟨R, hTR⟩ := (T.isPGroup'.map J.subtype).exists_le_sylow
  obtain ⟨n, hn, ⟨e⟩⟩ := hSD R
  have hβR : β ∈ (R : Subgroup C) := by
    have : (zpowers β).Normal := normal_of_le_center (zpowers_le.mpr hβ)
    have hp : IsPGroup 2 (zpowers β) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hβ2, pow_one])
    exact hp.le_sylow_of_normal R (mem_zpowers β)
  have heβ : e ⟨β, hβR⟩ = CFSG.Semidihedral.z n := by
    have hc : e ⟨β, hβR⟩ ∈ center (Open.SemidihedralGroup n) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (mem_center_iff.mp hβ y'))
    rw [CFSG.Semidihedral.center_eq_zpowers n hn] at hc
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two
      (CFSG.Semidihedral.orderOf_z n (by omega)) hc with h | h
    · exfalso
      have h1 : (⟨β, hβR⟩ : ↥(R : Subgroup C)) = 1 := e.injective (h.trans (map_one e).symm)
      have h2 : β = 1 := congrArg Subtype.val h1
      rw [h2, orderOf_one] at hβ2
      omega
    · exact h
  set QU : Subgroup C :=
    ((CFSG.Semidihedral.quaternionSubgroup n).comap e.toMonoidHom).map (R : Subgroup C).subtype
    with hQU
  have hQUinv : ∀ y ∈ QU, orderOf y = 2 → y = β := by
    rintro _ ⟨y, hy, rfl⟩ hy2
    have hy2' : orderOf (e y) = 2 := by
      rw [MulEquiv.orderOf_eq]
      rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hy2
    have h1 := CFSG.Semidihedral.quaternion_unique_involution n (by omega) (e y) hy hy2'
    rw [← heβ] at h1
    exact congrArg Subtype.val (e.injective h1)
  have hQUidx : (QU.subgroupOf (R : Subgroup C)).index = 2 := by
    have h1 : QU.subgroupOf (R : Subgroup C) =
        (CFSG.Semidihedral.quaternionSubgroup n).comap e.toMonoidHom :=
      comap_map_eq_self_of_injective (R : Subgroup C).subtype_injective _
    rw [h1, index_comap_of_surjective _ e.surjective]
    exact CFSG.Semidihedral.quaternionSubgroup_index n (by omega)
  have hxQU : x ∉ QU := fun h => hne (hQUinv x h hx2)
  have hT'idx : QU.relIndex T' = 2 := by
    rw [relIndex, index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨x, hxT''⟩, fun h => hxQU h, fun b => ?_⟩
    by_cases hb : (b : C) ∈ QU
    · exact Or.inr hb
    · left
      have hbR : (b : C) ∈ (R : Subgroup C) := hTR b.2
      have hxR : x ∈ (R : Subgroup C) := hTR hxT''
      have key := mul_mem_iff_of_index_two hQUidx (a := ⟨b, hbR⟩) (b := ⟨x, hxR⟩)
      exact key.mpr (iff_of_false hb hxQU)
  obtain ⟨X₀, -, hX₀i, -, -⟩ := CFSG.Quasithin.thompson_transfer_index_two T
    (Q := QU.subgroupOf J) (by rw [subgroupOf, relIndex_comap]; exact hT'idx)
    (u := ⟨x, hxJ⟩) (Subtype.ext hx1) hxT' (fun a ha => by
      have ha' : (a : C)⁻¹ * x * a ∈ QU := ha
      have hord : orderOf ((a : C)⁻¹ * x * a) = 2 := by
        have h1 := MulEquiv.orderOf_eq (MulAut.conj (a : C)⁻¹) x
        rw [MulAut.conj_apply, inv_inv] at h1
        rw [h1, hx2]
      have h2 := hQUinv _ ha' hord
      apply hne
      have h3 : x = (a : C) * ((a : C)⁻¹ * x * a) * (a : C)⁻¹ := by group
      rw [h3, h2, mem_center_iff.mp hβ (a : C), mul_inv_cancel_right])
  exact index_ne_two_of_perfect X₀ hX₀i

theorem mem_of_perfect {β : C} (hβ : β ∈ center C) (hβ2 : orderOf β = 2)
    (hSD : ∀ R : Sylow 2 C, ∃ n, 4 ≤ n ∧
      Nonempty (↥(R : Subgroup C) ≃* Open.SemidihedralGroup n))
    {J : Subgroup C} (hJ : Group.IsPerfect ↥J) [Nontrivial ↥J] : β ∈ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : 2 ∣ Nat.card ↥J := by
    by_contra h
    have : Group.IsSolvable ↥J :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h))
    exact Group.IsPerfect.not_isSolvable ↥J ‹_›
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have h := eq_of_orderOf_eq_two_of_perfect hβ hβ2 hSD hJ y.2
    (by rw [Subgroup.orderOf_coe]; exact hy)
  rw [← h]
  exact y.2

end SD46

end CFSG.ComponentClassification.HarrisLit
