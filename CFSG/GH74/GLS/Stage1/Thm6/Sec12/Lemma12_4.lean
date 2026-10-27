module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_2

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

omit [Finite G] in
theorem exists_mul_of_sup_eq {B N T : Subgroup G} (hBT : B ≤ T) (hN : NormalIn N T)
    (hsup : B ⊔ N = T) {t : G} (ht : t ∈ T) : ∃ b ∈ B, ∃ d ∈ N, t = b * d := by
  have hnorm : B ≤ Subgroup.normalizer (N : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hN.2 b (hBT hb) r hr, fun hr => ?_⟩
    have := hN.inv_conj (hBT hb) hr
    have e : b⁻¹ * (b * r * b⁻¹) * b = r := by group
    rwa [e] at this
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right B N hnorm
  have ht' : t ∈ (↑(B ⊔ N) : Set G) := by rw [hsup]; exact ht
  rw [hset] at ht'
  obtain ⟨b, hb, d, hd, e⟩ := Set.mem_mul.1 ht'
  exact ⟨b, hb, d, hd, e.symm⟩

theorem HBase.sq_mem_R (h : HBase G x S T P Q Rd F) (hRf : IP_Rd_factor T P Q Rd) {t : G}
    (ht : t ∈ T) (htt : t * t ∈ Rd) : t * t ∈ P ⊔ Q := by
  obtain ⟨B, hBT, hBRd, hBsup⟩ := hRf
  obtain ⟨b, hb, d, hd, rfl⟩ := exists_mul_of_sup_eq hBT h.Rd_normal hBsup ht
  have hbT : b ∈ T := hBT hb
  have hd'Rd : b⁻¹ * d * b ∈ Rd := h.Rd_normal.inv_conj hbT hd
  have e : b * d * (b * d) = (b * b) * ((b⁻¹ * d * b) * d) := by group
  have hb2 : b * b ∈ Rd := by
    have : b * b = (b * d * (b * d)) * ((b⁻¹ * d * b) * d)⁻¹ := by group
    rw [this]
    exact Rd.mul_mem htt (Rd.inv_mem (Rd.mul_mem hd'Rd hd))
  have hb2R : b * b ∈ P ⊔ Q := by
    have : b * b ∈ B ⊓ Rd := ⟨B.mul_mem hb hb, hb2⟩
    rwa [hBRd] at this
  have hdd : (b⁻¹ * d * b) * d ∈ P ⊔ Q := by
    by_cases hdR : d ∈ P ⊔ Q
    · exact (P ⊔ Q).mul_mem (h.R_normal.inv_conj hbT hdR) hdR
    · have hd'R : b⁻¹ * d * b ∉ P ⊔ Q := by
        intro hd'R
        apply hdR
        have := h.R_normal.2 b hbT _ hd'R
        have e2 : b * (b⁻¹ * d * b) * b⁻¹ = d := by group
        rwa [e2] at this
      exact relIndex_two_mul_mem h.R_index_le_two hd'Rd hd hd'R hdR
  rw [e]
  exact (P ⊔ Q).mul_mem hb2R hdd

theorem HBase.R_invol (h : HBase G x S T P Q Rd F) {a : G} (ha : a ∈ P ⊔ Q) (ha2 : a * a = 1) :
    ∃ p ∈ P, ∃ q ∈ Q, a = p * q ∧ p * p = 1 ∧ q * q = 1 := by
  obtain ⟨p, hp, q, hq, e⟩ := h.mem_R.1 ha
  have hpq : p * q = q * p := h.PQ_comm p hp q hq
  have h1 : p * q * (p * q) = p * p * (q * q) :=
    (show Commute q p from hpq.symm).mul_mul_mul_comm p q
  have hsq : p * p * (q * q) = 1 := by rw [← h1, ← e]; exact ha2
  have hpp : p * p = (q * q)⁻¹ := eq_inv_of_mul_eq_one_left hsq
  have hpp1 : p * p = 1 := by
    apply h.eq_one_of_mem_P_Q (P.mul_mem hp hp)
    rw [hpp]
    exact Q.inv_mem (Q.mul_mem hq hq)
  have hqq : q * q = 1 := by rw [hpp1, one_mul] at hsq; exact hsq
  exact ⟨p, hp, q, hq, e, hpp1, hqq⟩

theorem lemma_12_4' (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (hout : IP_outer x T Rd)
    (hcf : IP_cent_four T P Q Rd) (hP4 : IP_P_four P) (hRf : IP_Rd_factor T P Q Rd) {t : G}
    (ht : t ∈ T) (htt2 : t * t * (t * t) = 1) :
    t * t ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by
  have httRd : t * t ∈ Rd := involution_mem_Rd h hout (T.mul_mem ht ht) htt2
  obtain ⟨v, hv, w, hw, e, hvv1, hww⟩ := h.R_invol (h.sq_mem_R hRf ht httRd) htt2
  have hwx : w = 1 ∨ w = x := h.Q_invol hP4 hw hww
  have hwcent : w * t = t * w := by
    rcases hwx with e1 | e1
    · rw [e1]; simp
    · rw [e1]; exact h.x_central t ht
  have hwin : w ∈ Subgroup.zpowers x := by
    rcases hwx with e1 | e1
    · rw [e1]; exact Subgroup.one_mem _
    · rw [e1]; exact Subgroup.mem_zpowers x
  by_cases hvz : v = 1 ∨ v = z
  · rw [e]
    have hvmem : v ∈ Subgroup.zpowers z := by
      rcases hvz with e1 | e1
      · rw [e1]; exact Subgroup.one_mem _
      · rw [e1]; exact Subgroup.mem_zpowers z
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hvmem) (Subgroup.mem_sup_left hwin)
  · rw [not_or] at hvz
    have hV : IsFour (Subgroup.zpowers v ⊔ Subgroup.zpowers z) :=
      isFour_pair hvv1 hz.z_sq hvz.1 hz.z_ne_one hvz.2 (hz.z_central v (h.P_le_T hv)).symm
    have hVP : Subgroup.zpowers v ⊔ Subgroup.zpowers z ≤ P :=
      sup_le ((Subgroup.zpowers_le).2 hv) ((Subgroup.zpowers_le).2 hz.z_mem_P)
    have htv : t * v = v * t := by
      have hc : t * (v * w) = (v * w) * t := by rw [← e]; group
      have : (t * v) * w = (v * t) * w := by
        calc t * v * w = t * (v * w) := by group
          _ = v * w * t := hc
          _ = v * (w * t) := by group
          _ = v * (t * w) := by rw [hwcent]
          _ = v * t * w := by group
      exact mul_right_cancel this
    have hvC : v ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact htv
    have hzC : z ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact (hz.z_central t ht).symm
    have hxC : x ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact (h.x_central t ht).symm
    have hEC : (Subgroup.zpowers v ⊔ Subgroup.zpowers z) ⊔ Subgroup.zpowers x ≤
        Subgroup.centralizer ({t} : Set G) :=
      sup_le (sup_le ((Subgroup.zpowers_le).2 hvC) ((Subgroup.zpowers_le).2 hzC))
        ((Subgroup.zpowers_le).2 hxC)
    have htE : t ∈ centIn T ((Subgroup.zpowers v ⊔ Subgroup.zpowers z) ⊔ Subgroup.zpowers x) := by
      refine Subgroup.mem_inf.2 ⟨ht, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_centralizer_iff.1 (hEC hy) t (Set.mem_singleton t)
      exact this.symm
    have hmem : t * t ∈ phi2 (centIn T ((Subgroup.zpowers v ⊔ Subgroup.zpowers z) ⊔
        Subgroup.zpowers x)) := Subgroup.subset_closure ⟨t, htE, rfl⟩
    have h12 := omega1_phi_cent_le h hout hcf hVP hV
    have : t * t ∈ Subgroup.zpowers x := h12 (Subgroup.subset_closure ⟨hmem, htt2⟩)
    exact Subgroup.mem_sup_left this

theorem lemma_12_4 (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (hout : IP_outer x T Rd)
    (hcf : IP_cent_four T P Q Rd) (hP4 : IP_P_four P) (hRf : IP_Rd_factor T P Q Rd) {t : G}
    (ht : t ∈ T) (ht4 : orderOf t = 4) :
    t * t ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by
  have hpow : t ^ 4 = 1 := by rw [← ht4]; exact pow_orderOf_eq_one t
  have htt2 : t * t * (t * t) = 1 := by
    have h4 : t ^ 4 = t ^ 2 * t ^ 2 := by rw [← pow_add]
    rw [pow_two] at h4
    rw [← h4]; exact hpow
  exact lemma_12_4' h hz hout hcf hP4 hRf ht htt2

end CFSG.GH74.GLS.Stage1.Thm6.Sec12

