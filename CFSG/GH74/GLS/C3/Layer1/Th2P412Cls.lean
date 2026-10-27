module

public import CFSG.GH74.GLS.C3.Layer1.Th2P43fBurn
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem tau_cases [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {w : G} (hwP : w ∈ T ⊓ K)
    (hwR : w ∉ conjugate (T ⊓ CxK x K) a⁻¹) :
    psi (a⁻¹ * w * a) = swap 5 6 ∨ psi (a⁻¹ * w * a) = a7P 1 * swap 5 6 := by
  have hwC : a⁻¹ * w * a ∈ conjugate (T ⊓ K) a := conj_mem_conj hwP
  have hwCC : a⁻¹ * w * a ∈ centralizer ({x} : Set G) := F.T_le_C (F.conj_mem_T hwP)
  have hτcomm : ∀ i : Fin 8, psi (a⁻¹ * w * a) * a7P i = a7P i * psi (a⁻¹ * w * a) := by
    intro i
    obtain ⟨u', hu', hui⟩ := F.psi_P_surj i
    rw [← hui, ← F.psi_mul _ hwCC u' (F.P_le_C hu'), ← F.psi_mul u' (F.P_le_C hu') _ hwCC]
    exact congrArg psi (F.core.comm_P_conj u' hu' _ hwC).symm
  rcases cent_a7P _ hτcomm with h1 | h1 | h1 | h1
  · exact absurd (F.mem_R_of_psi hwP h1) hwR
  · exfalso
    have hzq : z * (a⁻¹ * w * a) ∈ T ⊓ CxK x K := by
      have hT : z * (a⁻¹ * w * a) ∈ T := T.mul_mem F.z_mem.1 (F.conj_mem_T hwP)
      refine ⟨hT, (F.psi_ker _ (F.T_le_C hT)).1 ?_⟩
      rw [F.psi_mul z (F.P_le_C F.z_mem) _ hwCC, F.psi_z, h1]
      decide
    have hzP' : z * (a⁻¹ * w * a) ∈ conjugate (T ⊓ K) a := F.Q_le_conj hG hs e7 hP2 hQ4 hzq
    have hz' : z ∈ conjugate (T ⊓ K) a := by
      have := Subgroup.mul_mem _ hzP' (Subgroup.inv_mem _ hwC)
      have e : z * (a⁻¹ * w * a) * (a⁻¹ * w * a)⁻¹ = z := by group
      rwa [e] at this
    have : z ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨F.z_mem, hz'⟩
    rw [F.core.P_inf_conj, Subgroup.mem_bot] at this
    exact F.z_ne this
  · exact Or.inl h1
  · exact Or.inr h1

theorem isConj_tt_x_of_not_mem_R [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {u w : G} (hu : u ∈ T ⊓ K) (hw : w ∈ T ⊓ K)
    (hu2 : u * u = 1) (hw2 : w * w = 1) (huR : u ∉ conjugate (T ⊓ CxK x K) a⁻¹)
    (hwR : w ∉ conjugate (T ⊓ CxK x K) a⁻¹) : IsConj (tt a u w) x := by
  have hR := F.R_four hG hs e7 hP2 hQ4
  have hu1 : u ≠ 1 := fun h => huR (by rw [h]; exact one_mem _)
  have hw1 : w ≠ 1 := fun h => hwR (by rw [h]; exact one_mem _)
  have hzR : z ∈ conjugate (T ⊓ CxK x K) a⁻¹ := F.z_mem_four hR
  have huz : u ≠ z := fun h => huR (h ▸ hzR)
  have hwz : w ≠ z := fun h => hwR (h ▸ hzR)
  obtain ⟨r, hrR, hr1, hrz⟩ := F.exists_nc hR
  have hrP : r ∈ T ⊓ K := hR.1 hrR
  have hr2 : r * r = 1 := (forall_of_isElementaryAbelian hR.2.1).2 r hrR
  obtain ⟨V', hV'P, hV'el, hV'4, huV'⟩ := F.core.P_d8.exists_four_containing hu hu2
  have hV' : IsFourSub (T ⊓ K) V' := ⟨hV'P, hV'el, hV'4⟩
  have hne : conjugate (T ⊓ CxK x K) a⁻¹ ≠ V' := fun h => huR (h ▸ huV')
  have hsides := F.klein_sides hR hV' hne hrR hr1 hrz huV' hu1 huz
  have hτ := F.tau_cases hG hs e7 hP2 hQ4 hw hwR
  have hdich : (psi u * psi (a⁻¹ * w * a)).support.card = (psi (a⁻¹ * w * a)).support.card ∨
      (psi r * psi (a⁻¹ * w * a)).support.card = (psi (a⁻¹ * w * a)).support.card := by
    rcases hsides with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (dichotomy_perm h1 h2 hτ).symm
    · exact dichotomy_perm h2 h1 hτ
  have h1P : (1 : G) ∈ T ⊓ K := one_mem _
  have hone : (1 : G) * 1 = 1 := mul_one 1
  have hwx : IsConj (a⁻¹ * w * a) x := F.isConj_conj_x hw hw2 hw1
  have ht1 : tt a 1 w = a⁻¹ * w * a := by unfold tt; rw [one_mul]
  rcases hdich with hA | hB
  · have := F.k_rule' hu h1P hw hu2 hone hw2 (by rw [F.psi_one, one_mul]; exact hA)
    rw [ht1] at this
    exact this.trans hwx
  · exfalso
    have h1 := F.k_rule' hrP h1P hw hr2 hone hw2 (by rw [F.psi_one, one_mul]; exact hB)
    rw [ht1] at h1
    have h2 := F.isConj_tt_v_of_left hrP hw hr2 hw2 hr1 hw1 (F.psi_R hrR)
    exact F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
      (((h1.trans hwx).symm).trans h2)

theorem isConj_x_or_v_of_involution_T [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {t : G} (ht : t ∈ T) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    IsConj x t ∨ IsConj (z * x) t := by
  have ht' : t ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ ht
  obtain ⟨u, hu, q, hq, htq⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj ht'
  have hwP : a * q * a⁻¹ ∈ T ⊓ K := mem_conjugate_iff'.1 hq
  have hcomm : u * q = q * u := F.core.comm_P_conj u hu q hq
  have hsq : (u * u) * (q * q) = 1 * 1 := by
    calc (u * u) * (q * q) = u * (u * q) * q := by group
      _ = u * (q * u) * q := by rw [hcomm]
      _ = (u * q) * (u * q) := by group
      _ = 1 * 1 := by rw [← htq, ht2]; simp
  obtain ⟨hu2, hq2⟩ := eq_of_mul_eq_of_inf_eq_bot F.core.P_inf_conj
    (Subgroup.mul_mem _ hu hu) (one_mem _)
    (Subgroup.mul_mem _ hq hq) (one_mem _) hsq
  have hw2 : (a * q * a⁻¹) * (a * q * a⁻¹) = 1 := by
    calc (a * q * a⁻¹) * (a * q * a⁻¹) = a * (q * q) * a⁻¹ := by group
      _ = 1 := by rw [hq2]; group
  have hq' : q = a⁻¹ * (a * q * a⁻¹) * a := by group
  have htt : t = tt a u (a * q * a⁻¹) := by
    unfold tt
    rw [htq]
    congr 1
  have hR := F.R_four hG hs e7 hP2 hQ4
  by_cases hu1 : u = 1
  · left
    have : t = a⁻¹ * (a * q * a⁻¹) * a := by rw [htq, hu1, one_mul]; exact hq'
    have hw1 : a * q * a⁻¹ ≠ 1 := by
      intro h
      apply ht1
      rw [this, h]
      group
    rw [this]
    exact (F.isConj_conj_x hwP hw2 hw1).symm
  by_cases hw1 : a * q * a⁻¹ = 1
  · left
    have hq1 : q = 1 := by rw [hq', hw1]; group
    have : t = u := by rw [htq, hq1, mul_one]
    rw [this]
    exact (F.isConj_P_x hu hu2 hu1).symm
  by_cases huR : u ∈ conjugate (T ⊓ CxK x K) a⁻¹
  · right
    rw [htt]
    exact (F.isConj_tt_v_of_left hu hwP hu2 hw2 hu1 hw1 (F.psi_R huR)).symm
  by_cases hwR : a * q * a⁻¹ ∈ conjugate (T ⊓ CxK x K) a⁻¹
  · right
    rw [htt]
    exact (F.isConj_tt_v_of_right hu hwP hu2 hw2 hu1 hw1 (F.psi_R hwR)).symm
  · left
    rw [htt]
    exact (F.isConj_tt_x_of_not_mem_R hG hs e7 hP2 hQ4 hu hwP hu2 hw2 huR hwR).symm

end Frame

end CFSG.GH74.GLS.Th2.P43f
