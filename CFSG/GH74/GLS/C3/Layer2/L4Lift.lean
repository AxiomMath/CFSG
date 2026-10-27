module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

variable {C : Type} [Group C]

omit [Group C] in
theorem mem_zpowers_iff_of_mul_self' {C : Type} [Group C] {v a : C} (hv : v * v = 1) :
    a ∈ zpowers v ↔ a = 1 ∨ a = v := by
  constructor
  · intro ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    have h2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
    have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    have hv1 : v ^ k = v ^ (k % 2) := by
      conv_lhs => rw [hk]
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [hv1, h0, zpow_zero]
    · right; rw [hv1, h1, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem exists_mem_ne_one_ne {C : Type} [Group C] {E : Subgroup C} {v : C}
    (hE : 2 < Nat.card E) : ∃ e ∈ E, e ≠ 1 ∧ e ≠ v := by
  by_contra hno
  push Not at hno
  have hsub : (E : Set C) ⊆ {1, v} := by
    intro e he
    by_cases h1 : e = 1
    · exact Or.inl h1
    · exact Or.inr (hno e he h1)
  have hfin : Finite E := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    rw [Nat.card_eq_zero_of_infinite] at hE
    omega
  have h1 : (E : Set C).ncard ≤ ({1, v} : Set C).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, v} : Set C).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    simp
  have h3 : (E : Set C).ncard = Nat.card E := Nat.card_coe_set_eq _ |>.symm
  omega

theorem no_perfect_extension [Finite C] {v : C} {S E L : Subgroup C} [L.Normal]
    (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvc : ∀ c : C, c * v = v * c) (hvL : v ∈ L)
    (hS : IsSylowOf 2 S ⊤)
    (hZS : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 → s = v)
    (hE : E = S ⊓ L) (hEcard : Nat.card E = 8) (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hvE : v ∈ E) (hperf : L ≤ ⁅L, L⁆ ⊔ zpowers v) : False := by
  have hEL : E ≤ L := by rw [hE]; exact inf_le_right
  have hES : E ≤ S := by rw [hE]; exact inf_le_left
  by_cases hvK : v ∈ ⁅L, L⁆
  ·
    have hLK : L ≤ ⁅L, L⁆ := by
      refine hperf.trans ?_
      exact sup_le le_rfl (zpowers_le.2 hvK)
    have hcomm : commutator ↥L = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : (g : C) ∈ (commutator ↥L).map L.subtype := by
        have : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
          show Subgroup.map L.subtype ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⁅L, L⁆
          rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
        rw [this]; exact hLK g.2
      obtain ⟨c, hc, hcg⟩ := hg
      have : c = g := Subtype.ext hcg
      rwa [this] at hc
    have hSylL : IsSylowOf 2 E L := by
      rw [hE]
      exact hS.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.2 inferInstance).ge
    obtain ⟨-, -, hodd⟩ := isSylowOf_iff.1 hSylL
    set H : Subgroup L := E.subgroupOf L with hH
    let _ : CommGroup H := { (inferInstance : Group H) with
      mul_comm := fun a b => Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)) }
    let φ : H →* H := MonoidHom.id H
    have hidx : ¬ 2 ∣ H.index := hodd
    set vL : L := ⟨v, hvL⟩ with hvL_def
    have hvLH : vL ∈ H := hvE
    have htriv : ∀ g : L, MonoidHom.transfer φ g = 1 := by
      intro g
      have : g ∈ (MonoidHom.transfer φ).ker :=
        Abelianization.commutator_subset_ker (MonoidHom.transfer φ) (hcomm ▸ Subgroup.mem_top g)
      exact this
    have hcentral : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * vL ^ k * g₀ ∈ H → g₀⁻¹ * vL ^ k * g₀ = vL ^ k := by
      intro k g₀ _
      have hcomm' : ∀ c : L, c * vL = vL * c := fun c => Subtype.ext (hvc c)
      have : Commute g₀ (vL ^ k) := (Commute.pow_right (hcomm' g₀) k)
      calc g₀⁻¹ * vL ^ k * g₀ = (vL ^ k) * g₀⁻¹ * g₀ := by rw [← this.inv_left.eq]
        _ = vL ^ k := by group
    have htr := MonoidHom.transfer_eq_pow φ vL hcentral
    rw [htriv vL] at htr
    have hodd' : Odd H.index := Nat.odd_iff.2 (by omega)
    have hpow : vL ^ H.index = vL := by
      obtain ⟨m, hm⟩ := hodd'
      have hvv : vL * vL = 1 := Subtype.ext hv2
      rw [hm, pow_succ, pow_mul, sq, hvv, one_pow, one_mul]
    have h1 : (⟨vL ^ H.index, MonoidHom.transfer_eq_pow_aux vL hcentral⟩ : H) = 1 := by
      have := htr.symm
      simpa [φ] using this
    have h2 : vL ^ H.index = 1 := congrArg (fun x : H => (x : L)) h1
    rw [hpow] at h2
    exact hv1 (congrArg Subtype.val h2)
  ·
    set K := ⁅L, L⁆ with hK
    obtain ⟨e, heE, he1, hev⟩ := exists_mem_ne_one_ne (E := E) (v := v) (by omega)
    have heL : e ∈ L := hEL heE
    have hsK : ∃ s ∈ E, s ≠ 1 ∧ s ∈ K := by
      have : e ∈ K ⊔ zpowers v := hperf heL
      rw [Subgroup.mem_sup_of_normal_left] at this
      obtain ⟨k, hk, w, hw, hkw⟩ := this
      rcases (mem_zpowers_iff_of_mul_self' hv2).1 hw with hw1 | hw1
      · rw [hw1, mul_one] at hkw
        exact ⟨e, heE, he1, hkw ▸ hk⟩
      · rw [hw1] at hkw
        refine ⟨e * v, E.mul_mem heE hvE, ?_, ?_⟩
        · intro h1
          apply hev
          exact (mul_eq_one_iff_eq_inv.1 h1).trans (inv_eq_of_mul_eq_one_right hv2)
        · have : e * v = k := by rw [← hkw, mul_assoc, hv2, mul_one]
          rw [this]; exact hk
    obtain ⟨s, hsE, hs1, hsK⟩ := hsK
    obtain ⟨-, hSp, -⟩ := isSylowOf_iff.1 hS
    have : Group.IsNilpotent S := hSp.isNilpotent
    set N' : Subgroup S := K.subgroupOf S with hN'
    have hN'ne : N' ≠ ⊥ := by
      intro hbot
      have : (⟨s, hES hsE⟩ : S) ∈ N' := hsK
      rw [hbot, Subgroup.mem_bot] at this
      exact hs1 (congrArg Subtype.val this)
    have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
    have hQp : IsPGroup 2 ↥(N' ⊓ Subgroup.center S) := hSp.to_subgroup _
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hk
      exact hne ((Subgroup.eq_bot_iff_card _).2 hk)
    have hdvd : 2 ∣ Nat.card ↥(N' ⊓ Subgroup.center S) := by
      rw [hk]; exact dvd_pow_self 2 hk0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hzN' : (z : S) ∈ N' := z.2.1
    have hzc : (z : S) ∈ Subgroup.center S := z.2.2
    have hz2 : (z : S) * (z : S) = 1 := by
      have : (z : S) ^ 2 = 1 := by
        have h2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
        exact congrArg (fun y : ↥(N' ⊓ Subgroup.center S) => (y : S)) h2
      rwa [sq] at this
    have hz1 : (z : S) ≠ 1 := by
      intro h1
      have : z = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hz
      omega
    have hvz : ((z : S) : C) = v := by
      apply hZS _ (z : S).2
      · intro t ht
        have := Subgroup.mem_center_iff.1 hzc ⟨t, ht⟩
        exact (congrArg Subtype.val this).symm
      · exact congrArg Subtype.val hz2
      · intro h1
        exact hz1 (Subtype.ext h1)
    apply hvK
    rw [← hvz]
    exact hzN'

end CFSG.GH74.GLS.C3.Layer2.L4
