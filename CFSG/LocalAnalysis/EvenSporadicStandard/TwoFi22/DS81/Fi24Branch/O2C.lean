module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core4
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma54Layer

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

theorem zpowers_le_O2In_Cz (c : Core4 E t z) : zpowers z ≤ TwoFi22.O2In (Cz z) := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime c.klein.z_sq c.klein.z_ne
  refine TwoB.le_O2In (V := zpowers z) (H := Cz z)
    (Subgroup.zpowers_le.mpr (mem_Cz.mpr rfl)) ?_ (TwoB.isPGroup_zpowers_two hz2)
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hcomm : (n : G) * (g : G) = (g : G) * (n : G) := by
    have hz_cent : z ∈ centralizer ({(g : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mem_Cz.mp g.2).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hz_cent) hn)
  have hconj : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
    rw [← hcomm]; group
  simpa [hconj] using hn

theorem O2In_Cz_le_R (c : Core4 E t z) : TwoFi22.O2In (Cz z) ≤ Rg t z := by
  have hQ2 : IsPGroup 2 (TwoFi22.O2In (Cz z)) := TwoB.isPGroup_O2In (Cz z)
  have hR2 : IsPGroup 2 (Rg t z) := TwoB.isPGroup_O2In (Jg t z)
  have hRC : Rg t z ≤ Cz z := (Rg_le_Jg t z).trans c.jr.J_le_C
  have hXC : normalizer (Rg t z : Set G) ≤ Cz z := c.N_le_Cz
  have hQnormal : ((TwoFi22.O2In (Cz z)).subgroupOf (Cz z)).Normal :=
    TwoB.normal_subgroupOf_O2In (Cz z)
  have hC_le_normQ : Cz z ≤ normalizer (TwoFi22.O2In (Cz z) : Set G) := by
    letI : ((TwoFi22.O2In (Cz z)).subgroupOf (Cz z)).Normal := hQnormal
    exact Subgroup.le_normalizer_of_normal_subgroupOf (TwoB.O2In_le (Cz z))
  have hR_normQ : Rg t z ≤ normalizer (TwoFi22.O2In (Cz z) : Set G) :=
    hRC.trans hC_le_normQ
  have hQXn : ((TwoFi22.O2In (Cz z) ⊓ normalizer (Rg t z : Set G)).subgroupOf
      (normalizer (Rg t z : Set G))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · have hconj := hQnormal.conj_mem
        (⟨(n : G), hXC hn.2⟩ : ↥(Cz z)) (by rw [Subgroup.mem_subgroupOf]; exact hn.1)
        (⟨(g : G), hXC g.2⟩ : ↥(Cz z))
      simpa [Subgroup.mem_subgroupOf] using hconj
    · exact (normalizer (Rg t z : Set G)).mul_mem
        ((normalizer (Rg t z : Set G)).mul_mem g.2 hn.2)
        ((normalizer (Rg t z : Set G)).inv_mem g.2)
  have hQinfX_le_R : TwoFi22.O2In (Cz z) ⊓ normalizer (Rg t z : Set G) ≤ Rg t z := by
    have h := TwoB.le_O2In (H := normalizer (Rg t z : Set G))
      (V := TwoFi22.O2In (Cz z) ⊓ normalizer (Rg t z : Set G))
      inf_le_right hQXn (hQ2.to_le inf_le_left)
    rwa [c.o2N] at h
  let T : Subgroup G := TwoFi22.O2In (Cz z) ⊔ Rg t z
  have hT2 : IsPGroup 2 T := hQ2.to_sup_of_normal_left' hR2 hR_normQ
  by_contra hQR
  have hTR_ne : T ≠ Rg t z := by
    intro h
    exact hQR (le_sup_left.trans (le_of_eq h))
  have hlt : (Rg t z).subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hTR_ne
    apply le_antisymm ?_ le_sup_right
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥T) ∈ (Rg t z).subgroupOf T := by
      rw [htop]; exact Subgroup.mem_top _
    rwa [Subgroup.mem_subgroupOf] at hx'
  haveI : Group.IsNilpotent ↥T := hT2.isNilpotent
  obtain ⟨n, hnN, hnR⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := ↥T) ((Rg t z).subgroupOf T) hlt)
  have hn_RQ : (n : G) ∈ Rg t z ⊔ TwoFi22.O2In (Cz z) := by
    rw [sup_comm]; exact n.2
  obtain ⟨r', hr', q, hq, hrq⟩ := (mem_sup_of_le_normalizer hR_normQ).mp hn_RQ
  have hn_norm : (n : G) ∈ normalizer (Rg t z : Set G) := by
    have h : n ∈ (normalizer (Rg t z : Set G)).subgroupOf T := by
      rw [Subgroup.subgroupOf_normalizer_eq (le_sup_right : Rg t z ≤
        TwoFi22.O2In (Cz z) ⊔ Rg t z)]
      exact hnN
    rwa [Subgroup.mem_subgroupOf] at h
  have hr'_norm : (r' : G)⁻¹ ∈ normalizer (Rg t z : Set G) :=
    Subgroup.le_normalizer ((Rg t z).inv_mem hr')
  have hq_eq : (q : G) = (r' : G)⁻¹ * (n : G) := by rw [← hrq]; group
  have hq_norm : (q : G) ∈ normalizer (Rg t z : Set G) := by
    rw [hq_eq]; exact mul_mem hr'_norm hn_norm
  have hq_R : (q : G) ∈ Rg t z := hQinfX_le_R ⟨hq, hq_norm⟩
  have hnR_mem : (n : G) ∈ Rg t z := by
    rw [← hrq]; exact (Rg t z).mul_mem hr' hq_R
  apply hnR
  rw [Subgroup.mem_subgroupOf]
  exact hnR_mem

theorem O2In_Cz_eq_or (c : Core4 E t z) :
    TwoFi22.O2In (Cz z) = zpowers z ∨ TwoFi22.O2In (Cz z) = Rg t z := by
  have hzQ : zpowers z ≤ TwoFi22.O2In (Cz z) := zpowers_le_O2In_Cz c
  have hQR : TwoFi22.O2In (Cz z) ≤ Rg t z := O2In_Cz_le_R c
  refine c.irred (TwoFi22.O2In (Cz z)) hzQ hQR ?_ ?_
  · intro n hn q hq
    have hnC : n ∈ Cz z := CNz_le_Cz E z hn
    have hconj := (TwoB.normal_subgroupOf_O2In (Cz z)).conj_mem
      (⟨q, TwoB.O2In_le (Cz z) hq⟩ : ↥(Cz z))
      (by rw [Subgroup.mem_subgroupOf]; exact hq)
      (⟨n, hnC⟩ : ↥(Cz z))
    simpa [Subgroup.mem_subgroupOf] using hconj
  · intro n hn q hq
    have hconj := (TwoB.normal_subgroupOf_O2In (Cz z)).conj_mem
      (⟨q, TwoB.O2In_le (Cz z) hq⟩ : ↥(Cz z))
      (by rw [Subgroup.mem_subgroupOf]; exact hq)
      (⟨n, c.jr.J_le_C hn⟩ : ↥(Cz z))
    simpa [Subgroup.mem_subgroupOf] using hconj

structure O2CData (t z : G) : Prop where
  O2_eq : TwoFi22.O2In (Cz z) = Rg t z
  normalizer_eq : normalizer (Rg t z : Set G) = Cz z
  cent_le : Cz z ⊓ centralizer (Rg t z : Set G) ≤ Rg t z
  normal_le : ∀ Q : Subgroup G, Q ≤ Cz z → (∀ c ∈ Cz z, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) →
    IsPGroup 2 ↥Q → Q ≤ Rg t z

theorem o2cData_of_eq (c : Core4 E t z) (h : TwoFi22.O2In (Cz z) = Rg t z) : O2CData t z := by
  have hQnormal : ((TwoFi22.O2In (Cz z)).subgroupOf (Cz z)).Normal :=
    TwoB.normal_subgroupOf_O2In (Cz z)
  have hC_le_normR : Cz z ≤ normalizer (Rg t z : Set G) := by
    have hC_le_normQ : Cz z ≤ normalizer (TwoFi22.O2In (Cz z) : Set G) := by
      letI : ((TwoFi22.O2In (Cz z)).subgroupOf (Cz z)).Normal := hQnormal
      exact Subgroup.le_normalizer_of_normal_subgroupOf (TwoB.O2In_le (Cz z))
    rwa [h] at hC_le_normQ
  refine ⟨h, ?_, ?_, ?_⟩
  · exact le_antisymm c.N_le_Cz hC_le_normR
  · calc Cz z ⊓ centralizer (Rg t z : Set G) ≤ centralizer (Rg t z : Set G) := inf_le_right
      _ = zpowers z := c.jr.cent_R
      _ ≤ Rg t z := Subgroup.zpowers_le.mpr (c.jr.V_le_R z_mem_Vtz)
  · intro Q' hQ'C hQ'n hQ'2
    haveI : (Q'.subgroupOf (Cz z)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hQ'n (g : G) g.2 (n : G) hn
    have hle := TwoB.le_O2In hQ'C (inferInstance) hQ'2
    rwa [h] at hle

theorem isCharacteristicP_of_O2C_eq (c : Core4 E t z) (h : TwoFi22.O2In (Cz z) = Rg t z) :
    CFSG.IsCharacteristicP 2 ↥(Cz z) := by
  apply TwoB.isCharacteristicP_of_isTwoConstrained
  intro x hx
  rw [h]
  rw [h] at hx
  have hxzp : x ∈ zpowers z := by
    rw [← c.jr.cent_R]
    exact hx.2
  exact Subgroup.zpowers_le.mpr (c.jr.V_le_R z_mem_Vtz) hxzp

theorem O2In_Cz_eq_R_of_isCharacteristicP (c : Core4 E t z)
    (hC : CFSG.IsCharacteristicP 2 ↥(Cz z)) : TwoFi22.O2In (Cz z) = Rg t z := by
  rcases O2In_Cz_eq_or c with h | h
  · exfalso
    have hT : TwoB.IsTwoConstrained (Cz z) :=
      TwoB.isTwoConstrained_of_isCharacteristicP (Cz z) hC
    have hC_le_Q : Cz z ≤ TwoFi22.O2In (Cz z) := by
      intro x hx
      have hxcent : x ∈ centralizer (TwoFi22.O2In (Cz z) : Set G) := by
        rw [h]
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hzx : z ∈ centralizer ({x} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr (mem_Cz.mp hx).symm
        exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hzx) hy)
      exact hT ⟨hx, hxcent⟩
    have hR_le_Q : Rg t z ≤ TwoFi22.O2In (Cz z) :=
      ((Rg_le_Jg t z).trans c.jr.J_le_C).trans hC_le_Q
    have hcontra : (2 : ℕ) ^ 13 ≤ 2 := by
      calc (2 : ℕ) ^ 13 = Nat.card ↥(Rg t z) := c.jr.card_R.symm
        _ ≤ Nat.card ↥(TwoFi22.O2In (Cz z)) := Subgroup.card_le_of_le hR_le_Q
        _ = Nat.card ↥(zpowers z) := by rw [h]
        _ = orderOf z := Nat.card_zpowers z
        _ = 2 := orderOf_eq_prime c.klein.z_sq c.klein.z_ne
    exact absurd hcontra (by norm_num)
  · exact h

theorem o2cData (c : Core4 E t z) (hC : CFSG.IsCharacteristicP 2 ↥(Cz z)) : O2CData t z :=
  o2cData_of_eq c (O2In_Cz_eq_R_of_isCharacteristicP c hC)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
