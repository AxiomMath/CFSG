module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LPgl

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Subgroup

section Grp

variable {Y : Type*} [Group Y] [Finite Y]

theorem caseA_normal_of_comm {J K : Subgroup Y} (hJK : J ≤ K)
    (hcomm : ∀ a b : Y, a * b * a⁻¹ * b⁻¹ ∈ J) : K.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
  rw [h1]
  exact K.mul_mem (hJK (hcomm g n)) hn

theorem caseA_index_two_or_four (J : Subgroup Y) [J.Normal] {t : Y} (ht2 : t * t = 1)
    (htJ : t ∉ J) (h4 : J.index ≤ 4) : J.index = 2 ∨ J.index = 4 := by
  have hord : orderOf (QuotientGroup.mk t : Y ⧸ J) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, pow_two, ht2, QuotientGroup.mk_one]
    · rwa [Ne, QuotientGroup.eq_one_iff]
  have h2 : 2 ∣ J.index := hord ▸ orderOf_dvd_natCard (QuotientGroup.mk t : Y ⧸ J)
  have h0 : J.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem caseA_index_le_two {J P : Subgroup Y} (hJ : Nat.card J = 360) (hP : Nat.card P = 720)
    (h4 : J.index ≤ 4) : P.index ≤ 2 := by
  have h1 := Subgroup.card_mul_index J
  have h2 := Subgroup.card_mul_index P
  rw [hJ] at h1
  rw [hP] at h2
  omega

theorem caseA_card_sylow_inf (P : Subgroup Y) [P.Normal] (hP : Nat.card P = 720)
    (hidx : P.index ≤ 2) (S : Sylow 2 Y) : Nat.card ↥((S : Subgroup Y) ⊓ P) = 16 := by
  obtain ⟨a, ha⟩ := (S.isPGroup'.to_inf_left (K := P)).exists_card_eq
  have ha4 : a ≤ 4 := by
    by_contra hlt
    have h1 : 2 ^ 5 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
    have h2 : Nat.card ↥((S : Subgroup Y) ⊓ P) ∣ 720 := hP ▸ Subgroup.card_dvd_of_le inf_le_right
    rw [ha] at h2
    have h3 := h1.trans h2
    omega
  have hodd : ¬ 2 ∣ (S : Subgroup Y).index := S.not_dvd_index
  have hY : Nat.card (S : Subgroup Y) * (S : Subgroup Y).index = 720 * P.index := by
    rw [Subgroup.card_mul_index, ← hP, Subgroup.card_mul_index]
  have hr : P.relIndex (S : Subgroup Y) * Nat.card ↥(P ⊓ (S : Subgroup Y)) =
      Nat.card (S : Subgroup Y) := Subgroup.relIndex_mul_card P _
  rw [inf_comm, ha] at hr
  have hrd : P.relIndex (S : Subgroup Y) ∣ P.index := Subgroup.relIndex_dvd_index_of_normal P _
  have hi0 : 0 < P.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hr0 : 0 < P.relIndex (S : Subgroup Y) := by
    rcases Nat.eq_zero_or_pos (P.relIndex (S : Subgroup Y)) with h | h
    · rw [h, zero_mul] at hr
      have : 0 < Nat.card (S : Subgroup Y) := Nat.card_pos
      omega
    · exact h
  have hrle : P.relIndex (S : Subgroup Y) ≤ P.index := Nat.le_of_dvd hi0 hrd
  rw [ha]
  rw [← hr] at hY
  generalize P.relIndex (S : Subgroup Y) = r at hr hr0 hrle hrd hY
  generalize (S : Subgroup Y).index = o at hodd hY
  generalize P.index = i at hidx hi0 hrle hrd hY
  have hi : i = 1 ∨ i = 2 := by omega
  have hrr : r = 1 ∨ r = 2 := by omega
  rcases hi with rfl | rfl <;> rcases hrr with rfl | rfl <;> interval_cases a <;> omega

theorem caseA_p3 (J : Subgroup Y) [J.Normal] (e : J ≃* alternatingGroup (Fin 6))
    (hC : centralizer (J : Set Y) = ⊥) {t : Y} (ht2 : t * t = 1) (htJ : t ∉ J)
    (hpgl : PGLTwoSquareOuter J t) (hcomm : ∀ a b : Y, a * b * a⁻¹ * b⁻¹ ∈ J)
    (hidx : (J ⊔ zpowers t).index ≤ 2) :
    ∀ S : Sylow 2 Y, t ∈ S → ∀ g : Y, g * t * g⁻¹ ∈ S →
      ∃ s ∈ S, s * t * s⁻¹ = g * t * g⁻¹ := by
  obtain ⟨hP, hD, -⟩ := pgl9_sylow J e hC ht2 htJ hpgl
  haveI : (J ⊔ zpowers t).Normal := caseA_normal_of_comm le_sup_left hcomm
  intro S hS g hg
  have hs2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hsJ : g * t * g⁻¹ ∉ J := fun h => htJ (by
    have h1 := Normal.conj_mem inferInstance _ h g⁻¹
    have h2 : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
    rwa [h2] at h1)
  have hsP : g * t * g⁻¹ ∈ J ⊔ zpowers t := by
    have h1 : g * t * g⁻¹ = (g * t * g⁻¹ * t⁻¹) * t := by group
    rw [h1]
    exact (J ⊔ zpowers t).mul_mem (mem_sup_left (hcomm g t)) (mem_sup_right (mem_zpowers t))
  obtain ⟨d, hd, hdt⟩ := hD ((S : Subgroup Y) ⊓ (J ⊔ zpowers t)) inf_le_right
    (S.isPGroup'.to_inf_left) (caseA_card_sylow_inf _ hP hidx S)
    ⟨hS, mem_sup_right (mem_zpowers t)⟩ (g * t * g⁻¹) ⟨hg, hsP⟩ hsJ hs2
  exact ⟨d, hd.1, hdt⟩

theorem caseA_elemAb_le_eight (J : Subgroup Y) [J.Normal] (e : J ≃* alternatingGroup (Fin 6))
    (hC : centralizer (J : Set Y) = ⊥) {t : Y} (ht2 : t * t = 1) (htJ : t ∉ J)
    (hpgl : PGLTwoSquareOuter J t) (hcomm : ∀ a b : Y, a * b * a⁻¹ * b⁻¹ ∈ J)
    (hidx : (J ⊔ zpowers t).index ≤ 2) :
    ∀ F : Subgroup Y, (∀ f ∈ F, f * f = 1) → Nat.card F ≤ 8 := by
  obtain ⟨-, -, hF⟩ := pgl9_sylow J e hC ht2 htJ hpgl
  haveI : (J ⊔ zpowers t).Normal := caseA_normal_of_comm le_sup_left hcomm
  intro F hF2
  have h4 : Nat.card ↥((J ⊔ zpowers t) ⊓ F) ≤ 4 :=
    hF _ inf_le_left fun f hf => hF2 f hf.2
  have h1 := Subgroup.relIndex_mul_card (J ⊔ zpowers t) F
  have h2 : (J ⊔ zpowers t).relIndex F ∣ (J ⊔ zpowers t).index :=
    Subgroup.relIndex_dvd_index_of_normal _ _
  have hi0 : 0 < (J ⊔ zpowers t).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h3 : (J ⊔ zpowers t).relIndex F ≤ 2 := (Nat.le_of_dvd hi0 h2).trans hidx
  rw [← h1]
  calc (J ⊔ zpowers t).relIndex F * Nat.card ↥((J ⊔ zpowers t) ⊓ F)
      ≤ 2 * 4 := Nat.mul_le_mul h3 h4
    _ = 8 := by norm_num

theorem caseA_group (J : Subgroup Y) [J.Normal] (e : J ≃* alternatingGroup (Fin 6))
    (hC : centralizer (J : Set Y) = ⊥) {t : Y} (ht2 : t * t = 1) (htJ : t ∉ J)
    (hpgl : PGLTwoSquareOuter J t) :
    J.index ≤ 4 ∧
    (∀ S : Sylow 2 Y, t ∈ S → ∀ g : Y, g * t * g⁻¹ ∈ S →
      ∃ s ∈ S, s * t * s⁻¹ = g * t * g⁻¹) ∧
    Nat.card Y ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2 ∧
    (∀ F : Subgroup Y, (∀ f ∈ F, f * f = 1) → Nat.card F ≤ 8) := by
  obtain ⟨h4, hcomm⟩ := A6_out J e hC
  have h4' : J.index ≤ 4 := h4
  have hJ : Nat.card J = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact a6aut_card
  obtain ⟨hP, -, -⟩ := pgl9_sylow J e hC ht2 htJ hpgl
  have hidx : (J ⊔ zpowers t).index ≤ 2 := caseA_index_le_two hJ hP h4'
  refine ⟨h4', caseA_p3 J e hC ht2 htJ hpgl hcomm hidx, ?_,
    caseA_elemAb_le_eight J e hC ht2 htJ hpgl hcomm hidx⟩
  rw [← Subgroup.card_mul_index J, hJ]
  rcases caseA_index_two_or_four J ht2 htJ h4' with h | h <;> rw [h] <;> norm_num

end Grp

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
