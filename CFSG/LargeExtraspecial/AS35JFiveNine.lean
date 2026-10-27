module

public import CFSG.LargeExtraspecial.AS35JPoints
public import CFSG.LargeExtraspecial.AS35ESixNine
public import CFSG.LargeExtraspecial.AS35HSixEightB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem zt_mul_self_J (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) :
    S.z * t * (S.z * t) = 1 := by
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  calc S.z * t * (S.z * t) = S.z * (t * S.z) * t := by group
    _ = S.z * (S.z * t) * t := by rw [S.mem_M_iff.mp htM]
    _ = 1 := by rw [← mul_assoc, S.z_mul_z, one_mul, htt]

theorem conj_zt_facts_J (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) {x : G} :
    orderOf (x⁻¹ * (S.z * t) * x) = 2 ∧ x⁻¹ * (S.z * t) * x ≠ 1 ∧
      x⁻¹ * (S.z * t) * x ≠ S.z := by
  have hzt1 : S.z * t ≠ 1 := by
    intro h1
    apply S.ne_z_of_mem_ESet ht.1
    calc t = S.z * (S.z * t) := by rw [← mul_assoc, S.z_mul_z, one_mul]
      _ = S.z := by rw [h1, mul_one]
  have hu1 : x⁻¹ * (S.z * t) * x ≠ 1 := by
    intro h1
    apply hzt1
    calc S.z * t = x * (x⁻¹ * (S.z * t) * x) * x⁻¹ := by group
      _ = 1 := by rw [h1]; group
  refine ⟨orderOf_eq_prime ?_ hu1, hu1, ?_⟩
  · rw [pow_two, show x⁻¹ * (S.z * t) * x * (x⁻¹ * (S.z * t) * x) =
      x⁻¹ * (S.z * t * (S.z * t)) * x by group, S.zt_mul_self_J hS ht]
    group
  · intro h1
    apply ht.2
    refine isConj_iff.mpr ⟨x, ?_⟩
    calc x * S.z * x⁻¹ = x * (x⁻¹ * (S.z * t) * x) * x⁻¹ := by rw [h1]
      _ = S.z * t := by group

theorem conj_z_mem_oTwoCent_J (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) {x : G}
    (hu : x⁻¹ * (S.z * t) * x ∈ S.QG) : x * S.z * x⁻¹ ∈ oTwoCent (S.z * t) := by
  have h1 : S.z ∈ oTwoCent (x⁻¹ * (S.z * t) * x) :=
    hS.zInOTwo _ hu (S.conj_zt_facts_J hS ht).1
  have h2 := CQuot.conj_mem_oTwoCent_conj x h1
  rwa [show x * (x⁻¹ * (S.z * t) * x) * x⁻¹ = S.z * t by group] at h2

theorem commute_of_mem_oTwoCent_J (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) {x : G}
    (hu : x⁻¹ * (S.z * t) * x ∈ S.QG) {y : G} (hy : y ∈ oTwoCent (S.z * t)) :
    y * (x * S.z * x⁻¹) = x * S.z * x⁻¹ * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hu1, huz⟩ := S.conj_zt_facts_J hS ht (x := x)
  set u := x⁻¹ * (S.z * t) * x with hudef
  set R : Subgroup G := S.QG ⊓ centralizer ({u} : Set G) with hR
  have hRu : R ≤ centralizer ({u} : Set G) := inf_le_right
  have hRn : R ≤ normalizer (oTwoCent u : Set G) := by
    intro r hr
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact conj_mem_oTwoCent (hRu hr) hw
    · intro hw
      have h1 := conj_mem_oTwoCent (inv_mem (hRu hr)) hw
      rwa [show r⁻¹ * (r * w * r⁻¹) * r⁻¹⁻¹ = w by group] at h1
  have hT : IsPGroup 2 (R ⊔ oTwoCent u : Subgroup G) :=
    (S.isPGroup_QG.to_le inf_le_left).to_sup_of_normal_right' (isPGroup_oTwoCent u) hRn
  have hcomm := AS35J.commute_of_weaklyClosed hT le_sup_left (a := S.z)
    (fun r hr => S.z_comm_QG (mem_inf.mp hr).1) (fun g _ hg => by
      refine hS.weak g (S.mem_QG_of_sq_eq_one_of_commute inf_le_left
        (S.relIndex_centralizer_eq_two hu hu1 huz) ?_ fun f hf => (hg f hf).symm)
      rw [pow_two, show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ by group,
        S.z_mul_z]
      group)
  have hy' : x⁻¹ * y * x ∈ oTwoCent u := by
    have h1 := CQuot.conj_mem_oTwoCent_conj x⁻¹ hy
    rwa [inv_inv] at h1
  have h1 := hcomm _ (le_sup_right (a := R) hy')
  calc y * (x * S.z * x⁻¹) = x * ((x⁻¹ * y * x) * S.z) * x⁻¹ := by group
    _ = x * (S.z * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
    _ = x * S.z * x⁻¹ * y := by group

theorem conj_z_ne_t_J (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) {x : G}
    (hu : x⁻¹ * (S.z * t) * x ∈ S.QG) :
    (x * S.z * x⁻¹) * S.z * (x * S.z * x⁻¹)⁻¹ ≠ t := by
  intro h
  obtain ⟨-, hu1, -⟩ := S.conj_zt_facts_J hS ht (x := x)
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  have haa : x * S.z * x⁻¹ * (x * S.z * x⁻¹) = 1 := by
    rw [show x * S.z * x⁻¹ * (x * S.z * x⁻¹) = x * (S.z * S.z) * x⁻¹ by group, S.z_mul_z]
    group
  have hainv : (x * S.z * x⁻¹)⁻¹ = x * S.z * x⁻¹ := inv_eq_of_mul_eq_one_right haa
  have hza : S.z * (x * S.z * x⁻¹) = x * S.z * x⁻¹ * t := by
    calc S.z * (x * S.z * x⁻¹) = (x * S.z * x⁻¹)⁻¹ *
        ((x * S.z * x⁻¹) * S.z * (x * S.z * x⁻¹)⁻¹) * ((x * S.z * x⁻¹) * (x * S.z * x⁻¹)) := by
          group
      _ = x * S.z * x⁻¹ * t := by rw [h, haa, mul_one, hainv]
  have e : (x⁻¹ * S.z * x) * S.z * (x⁻¹ * S.z * x)⁻¹ = S.z * (x⁻¹ * (S.z * t) * x) := by
    calc (x⁻¹ * S.z * x) * S.z * (x⁻¹ * S.z * x)⁻¹ =
        x⁻¹ * (S.z * (x * S.z * x⁻¹)) * S.z⁻¹ * x := by group
      _ = x⁻¹ * (x * S.z * x⁻¹ * (t * S.z⁻¹)) * x := by rw [hza]; group
      _ = x⁻¹ * (x * S.z * x⁻¹ * (S.z * t)) * x := by
          rw [S.z_inv, S.mem_M_iff.mp htM]
      _ = S.z * (x⁻¹ * (S.z * t) * x) := by group
  have h3 := hS.weak _ (by rw [e]; exact S.QG.mul_mem S.z_mem_QG hu)
  apply hu1
  have h4 : S.z * (x⁻¹ * (S.z * t) * x) = S.z * 1 := by rw [mul_one, ← e, h3]
  exact mul_left_cancel h4

theorem conj_z_commute_J (hS : S.SixHyp) {t h : G} (ht : t ∈ S.DSet) (hh : h * S.z * h⁻¹ = t)
    {x : G} (hu : x⁻¹ * (S.z * t) * x ∈ S.QG) :
    (x * S.z * x⁻¹) * S.z = S.z * (x * S.z * x⁻¹) := by
  have hc : ∀ p ∈ S.zConj (S.HAt h), p ≠ S.z → p ≠ t →
      (x * S.z * x⁻¹) * p = p * (x * S.z * x⁻¹) := by
    intro p hp hpz hpt
    obtain ⟨k, hk, hkQ⟩ := S.exists_conj_mem_QG_J hS ht hh hp hpz hpt
    have h1 := S.conj_z_mem_oTwoCent_J hS ht hkQ
    rw [hk] at h1
    exact (S.commute_of_mem_oTwoCent_J hS ht hu h1).symm
  rcases S.conj_z_eq_or_J hS ht hh hc with h1 | h1
  · calc x * S.z * x⁻¹ * S.z =
        (x * S.z * x⁻¹) * S.z * (x * S.z * x⁻¹)⁻¹ * (x * S.z * x⁻¹) := by group
      _ = S.z * (x * S.z * x⁻¹) := by rw [h1]
  · exact absurd h1 (S.conj_z_ne_t_J hS ht hu)

theorem conj_conj_z_eq_or_J (hS : S.SixHyp) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {c : G} (hc : c * (S.z * t) = S.z * t * c) :
    (c * S.z * c⁻¹) * S.z * (c * S.z * c⁻¹)⁻¹ = S.z ∨
      (c * S.z * c⁻¹) * S.z * (c * S.z * c⁻¹)⁻¹ = t := by
  refine S.conj_z_eq_or_J hS ht hh fun p hp hpz hpt => ?_
  obtain ⟨k, hk, hkQ⟩ := S.exists_conj_mem_QG_J hS ht hh hp hpz hpt
  have hkQ' : (c⁻¹ * k)⁻¹ * (S.z * t) * (c⁻¹ * k) ∈ S.QG := by
    rwa [show (c⁻¹ * k)⁻¹ * (S.z * t) * (c⁻¹ * k) = k⁻¹ * (c * (S.z * t) * c⁻¹) * k by group,
      show c * (S.z * t) * c⁻¹ = S.z * t by rw [hc]; group]
  have h1 := S.conj_z_commute_J hS ht hh hkQ'
  rw [show c⁻¹ * k * S.z * (c⁻¹ * k)⁻¹ = c⁻¹ * p * c by rw [← hk]; group] at h1
  calc c * S.z * c⁻¹ * p = c * (S.z * (c⁻¹ * p * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * p * c) * S.z) * c⁻¹ := by rw [← h1]
    _ = p * (c * S.z * c⁻¹) := by group

theorem fiveNineOne_J (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) :
    S.z ∈ oTwoCent (S.z * t) := by
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet ht
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have hee := S.zt_mul_self_J hS ht
  have hze : S.z * (S.z * t) = S.z * t * S.z := by
    calc S.z * (S.z * t) = S.z * (t * S.z) := by rw [S.mem_M_iff.mp htM]
      _ = S.z * t * S.z := by group
  set A : Set G := {y | ∃ c : G, c * (S.z * t) = S.z * t * c ∧ c * S.z * c⁻¹ = y} with hA
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    rintro _ ⟨c, -, rfl⟩
    rw [show c * S.z * c⁻¹ * (c * S.z * c⁻¹) = c * (S.z * S.z) * c⁻¹ by group, S.z_mul_z]
    group
  have hAe : ∀ a ∈ A, a * (S.z * t) = S.z * t * a := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c * (S.z * t) * c⁻¹ = S.z * t := by rw [hc]; group
    calc c * S.z * c⁻¹ * (S.z * t) = c * S.z * c⁻¹ * (c * (S.z * t) * c⁻¹) := by rw [hc']
      _ = c * (S.z * (S.z * t)) * c⁻¹ := by group
      _ = c * (S.z * t * S.z) * c⁻¹ := by rw [hze]
      _ = c * (S.z * t) * c⁻¹ * (c * S.z * c⁻¹) := by group
      _ = S.z * t * (c * S.z * c⁻¹) := by rw [hc']
  have hAA : ∀ a ∈ A, ∀ b ∈ A,
      a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = S.z * t := by
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
    have hc₁' : c₁⁻¹ * (S.z * t) = S.z * t * c₁⁻¹ := by
      calc c₁⁻¹ * (S.z * t) = c₁⁻¹ * (S.z * t * c₁) * c₁⁻¹ := by group
        _ = c₁⁻¹ * (c₁ * (S.z * t)) * c₁⁻¹ := by rw [hc₁]
        _ = S.z * t * c₁⁻¹ := by group
    have hc : (c₁⁻¹ * c₂) * (S.z * t) = S.z * t * (c₁⁻¹ * c₂) := by
      rw [mul_assoc, hc₂, ← mul_assoc, hc₁', mul_assoc]
    rw [show c₁ * S.z * c₁⁻¹ * (c₂ * S.z * c₂⁻¹) * (c₁ * S.z * c₁⁻¹)⁻¹ * (c₂ * S.z * c₂⁻¹)⁻¹ =
      c₁ * ((((c₁⁻¹ * c₂) * S.z * (c₁⁻¹ * c₂)⁻¹) * S.z * ((c₁⁻¹ * c₂) * S.z * (c₁⁻¹ * c₂)⁻¹)⁻¹ *
        S.z⁻¹)⁻¹) * c₁⁻¹ by group]
    rcases S.conj_conj_z_eq_or_J hS ht hh hc with h1 | h1
    · left
      rw [h1]
      group
    · right
      rw [h1, S.z_inv, mul_inv_rev, inv_eq_of_mul_eq_one_right htt, S.z_inv]
      calc c₁ * (S.z * t) * c₁⁻¹ = S.z * t * c₁ * c₁⁻¹ := by rw [hc₁]
        _ = S.z * t := by group
  have hX2 := AS35J.isPGroup_closure_of_comm hee hA2 hAe hAA
  have hXC : closure A ≤ centralizer ({S.z * t} : Set G) := by
    rw [closure_le]
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hAe a ha)
  have hcA : ∀ c ∈ centralizer ({S.z * t} : Set G), ∀ a ∈ A, c * a * c⁻¹ ∈ A := by
    rintro c hc _ ⟨d, hd, rfl⟩
    have hc' := mem_centralizer_singleton_iff.mp hc
    refine ⟨c * d, ?_, by group⟩
    rw [mul_assoc, hd, ← mul_assoc, hc', mul_assoc]
  have hXn : ∀ c ∈ centralizer ({S.z * t} : Set G), ∀ y ∈ closure A, c * y * c⁻¹ ∈ closure A := by
    intro c hc y hy
    induction hy using closure_induction with
    | mem a ha => exact subset_closure (hcA c hc a ha)
    | one => simp
    | mul y₁ y₂ _ _ ih₁ ih₂ =>
      rw [show c * (y₁ * y₂) * c⁻¹ = c * y₁ * c⁻¹ * (c * y₂ * c⁻¹) by group]
      exact mul_mem ih₁ ih₂
    | inv y _ ih =>
      rw [show c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ by group]
      exact inv_mem ih
  exact le_oTwoCent hXC hXn hX2 (subset_closure ⟨1, by group, by group⟩)

end Setting

namespace S14

theorem aschbacherFiveNineOneStmt : AschbacherFiveNineOneStmt :=
  fun _ _ _ S hS _ _ ht => S.fiveNineOne_J hS ht

end S14

end CFSG.LargeExtraspecial
