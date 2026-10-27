module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412E8
public import CFSG.GH74.GLS.C3.Layer1.Th2P412Gen
public import CFSG.GH74.GLS.C3.Layer1.Th2P412Fus
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt CFSG.GH74.GLS.Th2.P412

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem x_central_conj [Finite G] : ∀ w ∈ conjugate (T ⊓ K) a, w * x = x * w := by
  intro w hw
  have hp : a * w * a⁻¹ ∈ T ⊓ K := mem_conjugate_iff'.1 hw
  have hzc := F.z_central _ hp
  have e1 : w * x = a⁻¹ * ((a * w * a⁻¹) * z) * a := by rw [← F.a_z_a]; group
  have e2 : x * w = a⁻¹ * (z * (a * w * a⁻¹)) * a := by rw [← F.a_z_a]; group
  rw [e1, e2, hzc]

theorem eq_v_of_central [Finite G] {s : G} (hsS : s ∈ S) (hs1 : s ≠ 1)
    (hc : ∀ t ∈ S, s * t = t * s) : s = z * x := by
  by_cases hsT : s ∈ T
  · have hs' : s ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ hsT
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj hs'
    have hpc : ∀ p₁ ∈ T ⊓ K, p₁ * p = p * p₁ := by
      intro p₁ hp₁
      have h1 := hc p₁ (F.core.T_le_S hp₁.1)
      rw [hpq] at h1
      have h2 : q * p₁ = p₁ * q := (F.core.comm_P_conj p₁ hp₁ q hq).symm
      have h3 : p * p₁ * q = p₁ * p * q := by
        calc p * p₁ * q = p * (p₁ * q) := by group
          _ = p * (q * p₁) := by rw [h2]
          _ = p * q * p₁ := by group
          _ = p₁ * (p * q) := h1
          _ = p₁ * p * q := by group
      exact (mul_right_cancel h3).symm
    have hqc : ∀ q₁ ∈ conjugate (T ⊓ K) a, q₁ * q = q * q₁ := by
      intro q₁ hq₁
      have h1 := hc q₁ (F.core.T_le_S (F.core.conj_le F.core.P_le hq₁))
      rw [hpq] at h1
      have h2 : p * q₁ = q₁ * p := F.core.comm_P_conj p hp q₁ hq₁
      have h3 : p * (q * q₁) = p * (q₁ * q) := by
        calc p * (q * q₁) = p * q * q₁ := by group
          _ = q₁ * (p * q) := h1
          _ = (q₁ * p) * q := by group
          _ = (p * q₁) * q := by rw [h2]
          _ = p * (q₁ * q) := by group
      exact (mul_left_cancel h3).symm
    have hp' := F.core.P_d8.central_eq F.z_mem F.z_ne F.z_central p hp hpc
    have hq' := (F.core.P_d8.conjugate a).central_eq F.x_mem F.x_ne F.x_central_conj q hq hqc
    have hsa : s * a = a * s := hc a F.core.a_mem
    rcases hp' with hp1 | hpz <;> rcases hq' with hq1 | hqx
    · exact absurd (by rw [hpq, hp1, hq1]; group) hs1
    · exfalso
      have hsx : s = x := by rw [hpq, hp1, hqx]; group
      rw [hsx] at hsa
      have h1 : a * x * a⁻¹ = x := by
        calc a * x * a⁻¹ = (x * a) * a⁻¹ := by rw [hsa]
          _ = x := by group
      exact F.x_ne_z (by rw [← h1, F.a_x])
    · exfalso
      have hsz : s = z := by rw [hpq, hpz, hq1]; group
      rw [hsz] at hsa
      have h1 : a * z * a⁻¹ = z := by
        calc a * z * a⁻¹ = (z * a) * a⁻¹ := by rw [hsa]
          _ = z := by group
      rw [F.a_z] at h1
      exact F.x_ne_z h1
    · rw [hpq, hpz, hqx]
  · exfalso
    have hxS : x ∈ S := F.core.T_le_S F.x_mem_T
    have h1 : s * x * s⁻¹ = x := by
      calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [hc x hxS]
        _ = x := by group
    rw [F.swap_x hsS hsT] at h1
    exact F.x_ne_z h1.symm

theorem card_S_le [Finite G] : Nat.card ↥S ≤ 128 := by
  have hmul := Subgroup.relIndex_mul_card T S
  rw [inf_eq_left.2 F.core.T_le_S, F.card_T] at hmul
  have h2 := F.relIndex_le_two
  omega

theorem card_CS_le [Finite G] {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁1 : s₁ ≠ 1) (hs₁z : s₁ ≠ z) :
    Nat.card ↥(S ⊓ centralizer (Esub x z a s₁ : Set G)) ≤ 16 := by
  set A : Subgroup G := (T ⊓ K) ⊓ centralizer ({s₁} : Set G) with hA
  have hAP : A ≤ T ⊓ K := inf_le_left
  have hA4 : Nat.card ↥A ≤ 4 := by
    have hdvd : Nat.card ↥A ∣ 8 := by
      rw [← F.core.P_d8.card_eq]
      exact Subgroup.card_dvd_of_le hAP
    have hne : Nat.card ↥A ≠ 8 := by
      intro h8
      have hAeq : A = T ⊓ K :=
        Subgroup.eq_of_le_of_card_ge hAP (by rw [h8, F.core.P_d8.card_eq])
      have hc : ∀ p ∈ T ⊓ K, p * s₁ = s₁ * p := fun p hp => by
        have : p ∈ A := hAeq ▸ hp
        exact Subgroup.mem_centralizer_singleton_iff.1 this.2
      rcases F.core.P_d8.central_eq F.z_mem F.z_ne F.z_central s₁ hs₁ hc with h | h
      · exact hs₁1 h
      · exact hs₁z h
    have hmem : Nat.card ↥A ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hd] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hcomm : ∀ u ∈ A, ∀ w ∈ conjugate A a, u * w = w * u := fun u hu w hw =>
    F.core.comm_P_conj u (hAP hu) w (conjugate_le_conjugate' hAP a hw)
  have hdisj : A ⊓ conjugate A a = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have : u ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨hAP hu.1, conjugate_le_conjugate' hAP a hu.2⟩
    rw [F.core.P_inf_conj] at this
    exact this
  have hAA : Nat.card ↥(A ⊔ conjugate A a) ≤ 16 := by
    rw [card_sup_of_commute_of_disjoint hcomm hdisj, card_conjugate']
    exact (Nat.mul_le_mul hA4 hA4).trans (by norm_num)
  have hle : S ⊓ centralizer (Esub x z a s₁ : Set G) ≤ A ⊔ conjugate A a := by
    rintro t ⟨htS, htE⟩
    have htE' : t ∈ centralizer (Esub x z a s₁ : Set G) := htE
    have hcomm_e : ∀ e ∈ Esub x z a s₁, e * t = t * e := fun e he =>
      Subgroup.mem_centralizer_iff.1 htE' e he
    have htx : t * x = x * t := (hcomm_e x (x_mem_Esub x z a s₁)).symm
    have htT : t ∈ T := by
      by_contra htT
      have h1 : t * x * t⁻¹ = x := by rw [htx]; group
      rw [F.swap_x htS htT] at h1
      exact F.x_ne_z h1.symm
    have hty : (tt a s₁ s₁) * t = t * (tt a s₁ s₁) := hcomm_e _ (y0_mem_Esub x z a s₁)
    have ht' : t ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ htT
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj ht'
    obtain ⟨s₁', hs₁'def⟩ : ∃ s₁', s₁' = a⁻¹ * s₁ * a := ⟨_, rfl⟩
    have hs₁' : s₁' ∈ conjugate (T ⊓ K) a := by
      rw [hs₁'def]; exact conj_mem_conj (K := K) (T := T) (a := a) hs₁
    have hps' : p * s₁' = s₁' * p := F.core.comm_P_conj p hp s₁' hs₁'
    have hc2 : s₁ * q = q * s₁ := F.core.comm_P_conj s₁ hs₁ q hq
    have hy0 : tt a s₁ s₁ = s₁ * s₁' := by rw [hs₁'def]; rfl
    rw [hy0, hpq] at hty
    have hcpq : (p * s₁) * (q * s₁') = (s₁ * p) * (s₁' * q) := by
      calc (p * s₁) * (q * s₁') = p * (s₁ * q) * s₁' := by group
        _ = p * (q * s₁) * s₁' := by rw [hc2]
        _ = (p * q) * (s₁ * s₁') := by group
        _ = (s₁ * s₁') * (p * q) := hty.symm
        _ = s₁ * (s₁' * p) * q := by group
        _ = s₁ * (p * s₁') * q := by rw [← hps']
        _ = (s₁ * p) * (s₁' * q) := by group
    obtain ⟨hpc, hqc⟩ := eq_of_mul_eq_of_inf_eq_bot F.core.P_inf_conj
      (Subgroup.mul_mem _ hp hs₁) (Subgroup.mul_mem _ hs₁ hp)
      (Subgroup.mul_mem _ hq hs₁') (Subgroup.mul_mem _ hs₁' hq) hcpq
    have hpA : p ∈ A := ⟨hp, Subgroup.mem_centralizer_singleton_iff.2 hpc⟩
    have hqA : q ∈ conjugate A a := by
      rw [mem_conjugate_iff']
      refine ⟨mem_conjugate_iff'.1 hq, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have e1 : (a * q * a⁻¹) * s₁ = a * (q * s₁') * a⁻¹ := by rw [hs₁'def]; group
      have e2 : s₁ * (a * q * a⁻¹) = a * (s₁' * q) * a⁻¹ := by rw [hs₁'def]; group
      rw [e1, e2, hqc]
    rw [hpq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hpA) (Subgroup.mem_sup_right hqA)
  exact (Subgroup.card_le_of_le hle).trans hAA

theorem s1_not_mem_Esub [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {s₁ : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁2 : s₁ * s₁ = 1)
    (hs₁R : s₁ ∉ conjugate (T ⊓ CxK x K) a⁻¹) : s₁ ∉ Esub x z a s₁ := by
  intro hE
  have hR := F.R_four hG hs e7 hP2 hQ4
  have hzR : z ∈ conjugate (T ⊓ CxK x K) a⁻¹ := F.z_mem_four hR
  have hxv : ¬ IsConj x (z * x) :=
    F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
  have hs₁1 : s₁ ≠ 1 := fun h => hs₁R (h ▸ one_mem _)
  have hs₁z : s₁ ≠ z := fun h => hs₁R (h ▸ hzR)
  have hs₁S : s₁ ∈ S := F.core.T_le_S hs₁.1
  have hs₁v : s₁ ≠ z * x := by
    intro h
    have hxP : x ∈ T ⊓ K := by
      have e : x = z⁻¹ * s₁ := by rw [h]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ F.z_mem) hs₁
    have : x ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨hxP, F.x_mem⟩
    rw [F.core.P_inf_conj, Subgroup.mem_bot] at this
    exact F.x_ne this
  have hF := ((F.Fv_inter hG hs e7 hP2 hQ4 hs₁ hs₁2 hs₁R) s₁ hs₁S).2 ⟨hE, hs₁1, hs₁v⟩
  obtain ⟨-, -, -, hxsv⟩ := hF
  obtain ⟨hpzP, hpz2⟩ := F.invol_mul_z hs₁ hs₁2
  have hpz1 : s₁ * z ≠ 1 := by
    intro h
    apply hs₁z
    rw [mul_eq_one_iff_eq_inv.1 h]
    exact inv_eq_of_mul_eq_one_right F.z_sq
  have e0 : tt a s₁ (1 : G) = s₁ := by unfold tt; group
  have h1 : s₁ * (z * x) = tt a (s₁ * z) z := by
    have := F.tt_mul_v (p := s₁) (one_mem _)
    rwa [e0, one_mul] at this
  rw [h1] at hxsv
  have h2 : IsConj (tt a (s₁ * z) z) (z * x) :=
    F.isConj_tt_v_of_right hpzP F.z_mem hpz2 F.z_sq hpz1 F.z_ne
      (by rw [F.a_z_a]; exact F.psi_x)
  exact hxv (hxsv.trans h2)

end Frame

end CFSG.GH74.GLS.Th2.P43f

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P43f
  CFSG.GH74.GLS.Th2.P412 CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.Uniqueness

theorem mem_S_of_commute {G : Type} [Group G] [Finite G] {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {v : G} (hv2 : v * v = 1) (hvc : ∀ s ∈ S, s * v = v * s) : v ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvp : IsPGroup 2 ↥(zpowers v) := (isElementaryAbelian_zpowers_of_sq hv2).isPGroup 2 _
  have hnorm : zpowers v ≤ normalizer (S : Set G) := by
    refine zpowers_le.2 (C3.Layer2.L4.TIData.mem_normalizer_of_forall S fun e he => ?_)
    have : v * e * v⁻¹ = e := by rw [← hvc e he]; group
    rw [this]
    exact he
  have hsup : IsPGroup 2 ↥(zpowers v ⊔ S) := IsPGroup.to_sup_of_normal_right' hvp hS.isPGroup hnorm
  have heq := hS.eq_of_le (le_sup_right : S ≤ zpowers v ⊔ S) le_top hsup
  have hv : v ∈ zpowers v ⊔ S := Subgroup.mem_sup_left (mem_zpowers v)
  rw [heq] at hv
  exact hv

end CFSG.GH74.GLS
