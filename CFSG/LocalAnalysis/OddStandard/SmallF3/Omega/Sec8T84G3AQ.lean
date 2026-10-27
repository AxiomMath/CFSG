module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AS
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3E0
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AC
import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G}
  {E Y1 Y2 T T1 T2 V1 V2 F1 F2 : Subgroup G}

private lemma sec8t84g3a_aq_cent {H A : Subgroup G} (hAH : A ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (A : Set G))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card (oddCoreIn H))) :
    ∀ o ∈ oddCoreIn H, ∀ a ∈ A, a * o = o * a := by
  intro o ho a ha
  have haH : a ∈ H := hAH ha
  have hoH : o ∈ H := CFSG.ClassicalInvolution.Balance.oddCoreIn_le H ho
  have hconjO : a * o⁻¹ * a⁻¹ ∈ oddCoreIn H :=
    CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn haH ((oddCoreIn H).inv_mem ho)
  have hconjA : o * a * o⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hoH) a).mp ha
  have hcA : o * a * o⁻¹ * a⁻¹ ∈ A := A.mul_mem hconjA (A.inv_mem ha)
  have hcO : o * a * o⁻¹ * a⁻¹ ∈ oddCoreIn H := by
    have h := (oddCoreIn H).mul_mem ho hconjO
    rw [show o * (a * o⁻¹ * a⁻¹) = o * a * o⁻¹ * a⁻¹ from by group] at h
    exact h
  have hdisj : Disjoint A (oddCoreIn H) := Subgroup.disjoint_of_coprime_natCard hcop
  have hinf : A ⊓ oddCoreIn H = ⊥ := disjoint_iff.mp hdisj
  have hc1 : o * a * o⁻¹ * a⁻¹ = 1 := by
    have hmem : o * a * o⁻¹ * a⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hinf]
      exact ⟨hcA, hcO⟩
    simpa using hmem
  have hoeq : o * a = a * o := by
    calc o * a = (o * a * o⁻¹ * a⁻¹) * (a * o) := by group
      _ = a * o := by rw [hc1, one_mul]
  exact hoeq.symm

private lemma sec8t84g3a_aq_coprime (Q A : Subgroup G) (hcard : Nat.card A = 2 ^ 8) :
    Nat.Coprime (Nat.card A) (Nat.card (oddCoreIn Q)) := by
  have hodd : Odd (Nat.card (oddCoreIn Q)) :=
    CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn Q
  rw [hcard]
  exact (Nat.coprime_pow_left_iff (n := 8) (by norm_num) 2
    (Nat.card (oddCoreIn Q))).mpr (Nat.coprime_two_left.mpr hodd)

theorem sec8t84g3a_T_le_Q (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) :
    T ≤ sec8t84g_Q E (F1 ⊔ F2) := by
  unfold sec8t84g_Q
  refine le_inf h.T_syl.1 ?_
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sec8t84_E0_le_T h.D)).mp
    (sec8t84_E0_normal h.D)

theorem sec8t84g3a_O_eq (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) :
    oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) =
      sec8t84g_Q E (F1 ⊔ F2) ⊓ oddCoreIn (normalizer (E : Set G)) := by
  set Q : Subgroup G := sec8t84g_Q E (F1 ⊔ F2) with hQ
  set X : Subgroup G := normalizer (E : Set G) with hX
  set N : Subgroup G := oddCoreIn X with hN
  set O : Subgroup G := oddCoreIn Q with hO
  have hTQ : T ≤ Q := sec8t84g3a_T_le_Q h
  have hEQ : E ≤ Q := (sec8t84_E_le_T h.D).trans hTQ
  have hE0Q : F1 ⊔ F2 ≤ Q := (sec8t84_E0_le_T h.D).trans hTQ
  have hQX : Q ≤ X := by rw [hQ, hX]; unfold sec8t84g_Q; exact inf_le_left
  have hQnormE : Q ≤ Subgroup.normalizer (E : Set G) := by
    rw [hQ]; unfold sec8t84g_Q; exact inf_le_left
  have hQnormE0 : Q ≤ Subgroup.normalizer ((F1 ⊔ F2 : Subgroup G) : Set G) := by
    rw [hQ]; unfold sec8t84g_Q; exact inf_le_right
  have hcentE : ∀ o ∈ O, ∀ a ∈ E, a * o = o * a :=
    sec8t84g3a_aq_cent hEQ hQnormE (sec8t84g3a_aq_coprime Q E h.E8.2)
  have hcentE0 : ∀ o ∈ O, ∀ a ∈ F1 ⊔ F2, a * o = o * a :=
    sec8t84g3a_aq_cent hE0Q hQnormE0
      (sec8t84g3a_aq_coprime Q (F1 ⊔ F2) (sec8t84_E0_isElemAb2 h.D).2)
  refine le_antisymm ?_ ?_
  · intro o ho
    have hoQ : o ∈ Q := CFSG.ClassicalInvolution.Balance.oddCoreIn_le Q ho
    have hoX : o ∈ X := hQX hoQ
    have hodd : Odd (orderOf o) :=
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn Q).of_dvd_nat
        (Subgroup.orderOf_dvd_natCard O ho)
    have hc : ∀ e ∈ E, o * e = e * o := fun e he => (hcentE o ho e he).symm
    have hoN : o ∈ N := sec8t84g3a_odd_cent_mem h.E8 h.XO h.D.t_sq hoX hodd hc
    exact Subgroup.mem_inf.mpr ⟨hoQ, hoN⟩
  · intro o ho
    obtain ⟨hoQ, hoN⟩ := Subgroup.mem_inf.mp ho
    have hQnormN : Q ≤ Subgroup.normalizer (N : Set G) :=
      hQX.trans (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn X)
    have hnorm : Q ≤ Subgroup.normalizer ((Q ⊓ N : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer hQnormN).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hodd : Odd (Nat.card ↥(Q ⊓ N)) :=
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X).of_dvd_nat
        (Subgroup.card_dvd_of_le (inf_le_right : Q ⊓ N ≤ N))
    exact CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes
      (inf_le_left : Q ⊓ N ≤ Q) hnorm hodd ho

theorem sec8t84g3a_O_cent (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) :
    oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) ≤ centralizer ((E ⊔ (F1 ⊔ F2) : Subgroup G) : Set G) := by
  set Q : Subgroup G := sec8t84g_Q E (F1 ⊔ F2) with hQ
  set O : Subgroup G := oddCoreIn Q with hO
  have hTQ : T ≤ Q := sec8t84g3a_T_le_Q h
  have hEQ : E ≤ Q := (sec8t84_E_le_T h.D).trans hTQ
  have hE0Q : F1 ⊔ F2 ≤ Q := (sec8t84_E0_le_T h.D).trans hTQ
  have hQnormE : Q ≤ Subgroup.normalizer (E : Set G) := by
    rw [hQ]; unfold sec8t84g_Q; exact inf_le_left
  have hQnormE0 : Q ≤ Subgroup.normalizer ((F1 ⊔ F2 : Subgroup G) : Set G) := by
    rw [hQ]; unfold sec8t84g_Q; exact inf_le_right
  have hcentE : ∀ o ∈ O, ∀ a ∈ E, a * o = o * a :=
    sec8t84g3a_aq_cent hEQ hQnormE (sec8t84g3a_aq_coprime Q E h.E8.2)
  have hcentE0 : ∀ o ∈ O, ∀ a ∈ F1 ⊔ F2, a * o = o * a :=
    sec8t84g3a_aq_cent hE0Q hQnormE0
      (sec8t84g3a_aq_coprime Q (F1 ⊔ F2) (sec8t84_E0_isElemAb2 h.D).2)
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hEW : E ≤ Subgroup.centralizer ({o} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcentE o ho a ha
  have hE0W : (F1 ⊔ F2 : Subgroup G) ≤ Subgroup.centralizer ({o} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcentE0 o ho a ha
  have hW : (E ⊔ (F1 ⊔ F2) : Subgroup G) ≤ Subgroup.centralizer ({o} : Set G) :=
    sup_le hEW hE0W
  exact Subgroup.mem_centralizer_singleton_iff.mp (hW hw)

theorem sec8t84g3a_W_inf (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) :
    (E ⊔ (F1 ⊔ F2)) ⊓ oddCoreIn (normalizer (E : Set G)) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwW, hwN⟩ := Subgroup.mem_inf.mp hw
  have hWT : E ⊔ (F1 ⊔ F2) ≤ T :=
    sup_le (sec8t84_E_le_T h.D) (sec8t84_E0_le_T h.D)
  have hwT : w ∈ T := hWT hwW
  have hodd : Odd (orderOf w) :=
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (normalizer (E : Set G))).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard (oddCoreIn (normalizer (E : Set G))) hwN)
  obtain ⟨k, hk⟩ := h.T_syl.2.1.exists_orderOf_eq_pow (⟨w, hwT⟩ : T)
  have hk' : orderOf w = 2 ^ k := by simpa using hk
  have hk0 : k = 0 := by
    by_contra hk
    have he : Even (2 ^ k) := even_iff_two_dvd.mpr (dvd_pow_self 2 hk)
    exact (Nat.not_even_iff_odd.mpr (hk' ▸ hodd)) he
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])

end CFSG.OddStandard.SmallF3.Omega
