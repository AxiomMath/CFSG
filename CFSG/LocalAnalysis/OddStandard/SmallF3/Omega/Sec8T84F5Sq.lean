module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEInd1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private lemma mem_zpowers_eq_one_or {u x : G} (hu : u * u = 1) (hx : x ∈ zpowers u) :
    x = 1 ∨ x = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hu, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hu, one_zpow, one_mul, zpow_one]

private lemma le_normalizer_inf' {A B C : Subgroup G} (hB : A ≤ normalizer (B : Set G))
    (hC : A ≤ normalizer (C : Set G)) :
    A ≤ normalizer ((B ⊓ C : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_inf]
  rw [Subgroup.mem_normalizer_iff.mp (hB ha) x, Subgroup.mem_normalizer_iff.mp (hC ha) x]

private lemma card_sup_le_mul_card {A B : Subgroup G} (h : A ≤ normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have hmem : ∀ p : ↥A × ↥B, (p.1 : G) * p.2 ∈ (A ⊔ B : Subgroup G) := by
    intro p
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B h]
    exact Set.mul_mem_mul p.1.2 p.2.2
  have hsurj : Function.Surjective (fun p : ↥A × ↥B =>
      (⟨(p.1 : G) * p.2, hmem p⟩ : ↥(A ⊔ B))) := by
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B h] at hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext rfl⟩
  calc Nat.card ↥(A ⊔ B) ≤ Nat.card (↥A × ↥B) := Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

private lemma card_sup_zpowers_le_four {t γ : G} (ht : orderOf t = 2)
    (hγsq : γ * γ ∈ zpowers t) (hcomm : t * γ = γ * t) :
    Nat.card ↥(zpowers t ⊔ zpowers γ) ≤ 4 := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  rcases mem_zpowers_eq_one_or ht2 hγsq with hγ | hγ
  · have hclass : ∀ x ∈ (zpowers t ⊔ zpowers γ : Subgroup G),
        x = 1 ∨ x = t ∨ x = γ ∨ x = t * γ := by
      intro x hx
      have hct : ∀ u ∈ zpowers t, ∀ v ∈ zpowers γ, u * v = v * u := by
        rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
        exact (Commute.zpow_zpow (show Commute t γ from hcomm) m n).eq
      obtain ⟨u, hu, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hct hx
      rcases mem_zpowers_eq_one_or ht2 hu with h1 | h1 <;>
        rcases mem_zpowers_eq_one_or hγ hv with h2 | h2
      · left; rw [h1, h2, mul_one]
      · right; right; left; rw [h1, h2, one_mul]
      · right; left; rw [h1, h2, mul_one]
      · right; right; right; rw [h1, h2]
    have hsub : ((zpowers t ⊔ zpowers γ : Subgroup G) : Set G) ⊆ {1, t, γ, t * γ} := by
      intro x hx
      rcases hclass x hx with h | h | h | h <;> simp [h]
    calc Nat.card ↥(zpowers t ⊔ zpowers γ)
        = ((zpowers t ⊔ zpowers γ : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, t, γ, t * γ} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 4 := by
        have h1 := Set.ncard_insert_le (1 : G) ({t, γ, t * γ} : Set G)
        have h2 := Set.ncard_insert_le t ({γ, t * γ} : Set G)
        have h3 := Set.ncard_insert_le γ ({t * γ} : Set G)
        have h4 : ({t * γ} : Set G).ncard = 1 := Set.ncard_singleton _
        omega
  · have hsup : zpowers t ⊔ zpowers γ = zpowers γ := by
      refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
      exact Subgroup.zpowers_le.mpr
        (hγ ▸ Subgroup.mul_mem (Subgroup.zpowers γ) (Subgroup.mem_zpowers γ)
          (Subgroup.mem_zpowers γ))
    rw [hsup, Nat.card_zpowers]
    have h4 : γ ^ (4 : ℕ) = 1 := by
      have hγ2 : γ ^ 2 = t := by rw [pow_two, hγ]
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hγ2, pow_two, ht2]
    exact orderOf_le_of_pow_eq_one (by norm_num) h4

theorem sec8t84_gamma_sq (F : Sec8T84Base) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) {γ : G} (hγS : γ ∈ S)
    (hγ : InducesOutsideGStar L 6 (-1) γ) : γ * γ ∈ zpowers t := by
  obtain ⟨V, _, _, _, Q, hQ, e, x, _hfr, _hsign, hind, hx2, _hxnot⟩ := hγ
  have hL : IsOm6M L := ⟨hctx.component.isQuasisimple, hctx.omega6m⟩
  have hperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hind2 : InducesViaP L (Subgroup.center ↥L) hQ e (γ * γ) (x * x) :=
    inducesViaP_mul hind hind
  rw [hx2] at hind2
  have hcent : γ * γ ∈ centralizer (L : Set G) :=
    mem_centralizer_of_inducesViaP_one hperf hind2
  have hmem : γ * γ ∈ S ⊓ centralizer (L : Set G) := ⟨S.mul_mem hγS hγS, hcent⟩
  rw [F.h86 G t L S z g B hctx] at hmem
  exact hmem

theorem sec8t84_gamma0 (F : Sec8T84Base) (hI : Asc82Step84IK)
    (hKP : CFSG.Assembly.KProper Catalog G) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) :
    ∃ γ ∈ S, InducesOutsideGStar L 6 (-1) γ ∧ S = zpowers t ⊔ zpowers γ ⊔ (S ⊓ L) ∧
      γ * γ ∈ zpowers t ∧ Nat.card S ≤ 4 * Nat.card ↥(S ⊓ L) := by
  obtain ⟨γ, hγS, hγout, hSeq⟩ := hI G hKP t L S z g B hctx
  have hγsq : γ * γ ∈ zpowers t := sec8t84_gamma_sq F hctx hγS hγout
  have hγcent : γ ∈ centralizer ({t} : Set G) := hctx.sylow.1 hγS
  have hcomm : t * γ = γ * t :=
    Subgroup.mem_centralizer_iff.mp hγcent t (Set.mem_singleton t)
  have hH4 : Nat.card ↥(zpowers t ⊔ zpowers γ) ≤ 4 :=
    card_sup_zpowers_le_four hctx.involution hγsq hcomm
  have hHS : zpowers t ⊔ zpowers γ ≤ S :=
    sup_le (Subgroup.zpowers_le.mpr (sec4_t_mem_S hctx.sylow hctx.involution))
      (Subgroup.zpowers_le.mpr hγS)
  have hHnormS : zpowers t ⊔ zpowers γ ≤ Subgroup.normalizer (S : Set G) :=
    hHS.trans Subgroup.le_normalizer
  have hHnormL : zpowers t ⊔ zpowers γ ≤ Subgroup.normalizer (L : Set G) :=
    fun x hx => sec4_mem_normalizer F.h36 hctx.toSec3SettingLB x (hctx.sylow.1 (hHS hx))
  have hN : zpowers t ⊔ zpowers γ ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf' hHnormS hHnormL
  have hsup_le := card_sup_le_mul_card hN
  rw [← hSeq] at hsup_le
  refine ⟨γ, hγS, hγout, hSeq, hγsq, ?_⟩
  calc Nat.card S ≤ Nat.card ↥(zpowers t ⊔ zpowers γ) * Nat.card ↥(S ⊓ L) := hsup_le
    _ ≤ 4 * Nat.card ↥(S ⊓ L) := Nat.mul_le_mul_right _ hH4

theorem sec8t84_SL_E16 (F : Sec8T84Base) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) :
    ∃ B' : Subgroup G, B' ≤ S ⊓ L ∧ IsElemAb2 B' 4 ∧ B' ≠ B ∧
      (B.subgroupOf (S ⊓ L)).Normal ∧ (B'.subgroupOf (S ⊓ L)).Normal ∧
      ∀ U : Subgroup G, U ≤ S ⊓ L → IsElemAb2 U 4 → U = B ∨ U = B' := by
  have hL : IsOm6M L := ⟨hctx.component.isQuasisimple, hctx.omega6m⟩
  have hSyl : IsSylow2Of (S ⊓ L) L :=
    sec4_isSylow2Of_inf hctx.component.le (sec4_mem_normalizer F.h36 hctx.toSec3SettingLB)
      hctx.sylow
  obtain ⟨B₁, B₂, hne, hB1, hB2, honly⟩ := F.hM.sylow_E16 G L hL (S ⊓ L) hSyl
  have hBle : B ≤ S ⊓ L := by
    rw [inf_comm]
    exact hctx.B_le
  rcases honly B hBle hctx.B_e16 with hB | hB
  · refine ⟨B₂, hB2.1, hB2.2.1, ?_, ?_, hB2.2.2, ?_⟩
    · rw [hB]; exact hne.symm
    · rw [hB]; exact hB1.2.2
    · intro U hU hUe
      rcases honly U hU hUe with h | h
      · left; rw [hB]; exact h
      · right; exact h
  · refine ⟨B₁, hB1.1, hB1.2.1, ?_, ?_, hB1.2.2, ?_⟩
    · rw [hB]; exact hne
    · rw [hB]; exact hB2.2.2
    · intro U hU hUe
      rcases honly U hU hUe with h | h
      · right; exact h
      · left; rw [hB]; exact h

theorem sec8t84_t_not_mem_L (F : Sec8T84Base) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) : t ∉ L := by
  intro htL
  have hconj : IsConj t (t * t) :=
    F.h83 G t L hctx.toSec3SettingLB hctx.omega6m t hctx.involution htL
  have ht2 : t * t = 1 := by rw [← pow_two, ← hctx.involution]; exact pow_orderOf_eq_one t
  rw [ht2] at hconj
  have ht1 : t = 1 := isConj_one_left.mp hconj
  have hinv : orderOf t = 2 := hctx.involution
  rw [ht1, orderOf_one] at hinv
  exact absurd hinv (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
