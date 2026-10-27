module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

open Subgroup

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem sup_inf_eq_of_isSylowOf_inf {p : ℕ} [Fact p.Prime] {S Y C : Subgroup G}
    (hSp : IsPGroup p S) (hSYC : S ≤ Y ⊔ C)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hSC : S ≤ Subgroup.normalizer (C : Set G))
    (hYC : Y ≤ Subgroup.normalizer (C : Set G))
    (hcop : Nat.Coprime p (Nat.card (Y ⊓ C : Subgroup G)))
    (hSyl : CFSG.ABGLocalTools.IsSylowOf p (S ⊓ Y) Y) :
    (S ⊓ Y) ⊔ (S ⊓ C) = S := by
  classical
  set A := S ⊓ Y with hA
  set B := S ⊓ C with hB
  let H := Y ⊔ C
  have hSH : S ≤ H := hSYC
  have hCH : C ≤ H := le_sup_right
  have hCHnorm : H ≤ Subgroup.normalizer (C : Set G) :=
    sup_le hYC Subgroup.le_normalizer
  have hScop : Nat.Coprime (Nat.card S) (Nat.card (Y ⊓ C : Subgroup G)) := by
    obtain ⟨n, hn⟩ := hSp.exists_card_eq
    rw [hn]
    exact hcop.pow_left n
  have hSinf : S ⊓ (Y ⊓ C) = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hScop)
  have hABbot : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ S ⊓ (Y ⊓ C) := ⟨hx.1.1, hx.1.2, hx.2.2⟩
    rw [hSinf] at hx'
    exact hx'
  have hdisj : Disjoint A B := disjoint_iff.mpr hABbot
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
    rintro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      refine ⟨S.mul_mem (S.mul_mem hb.1 ha.1) (S.inv_mem hb.1), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hSY hb.1) a).mp ha.2
    · intro ha
      refine ⟨?_, ?_⟩
      · have hconj : b⁻¹ * (b * a * b⁻¹) * b = a := by group
        rw [← hconj]
        exact S.mul_mem (S.mul_mem (S.inv_mem hb.1) ha.1) hb.1
      · exact (Subgroup.mem_normalizer_iff.mp (hSY hb.1) a).mpr ha.2
  have hcardT : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A B hBA hdisj
  have hrelC : C.relIndex (Y ⊔ C) = (Y ⊓ C).relIndex Y := by
    have hsub : (Y ⊓ C).subgroupOf Y = C.subgroupOf Y := by
      ext x
      simp
    have : (C.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYC
    have : (C.subgroupOf (Y ⊔ C)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hYC
    have hcard := (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient Y C hYC).toEquiv).symm
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Subgroup.relIndex,
      Subgroup.index_eq_card, hsub]
    exact hcard
  have hq_eq : B.relIndex S = C.relIndex S := by
    rw [hB, inf_comm, Subgroup.inf_relIndex_right]
  have hCN : (C.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hCHnorm
  have hKmap : Nat.card ↥((S.subgroupOf H).map (QuotientGroup.mk' (C.subgroupOf H))) =
      B.relIndex S := by
    have h1 := Subgroup.relIndex_ker (f := QuotientGroup.mk' (C.subgroupOf H))
      (K := S.subgroupOf H)
    rw [QuotientGroup.ker_mk'] at h1
    rw [← h1, Subgroup.relIndex_subgroupOf hSH]
    exact hq_eq.symm
  have hq_dvd_rel : B.relIndex S ∣ (Y ⊓ C).relIndex Y := by
    have hdvd : B.relIndex S ∣ C.relIndex H := by
      rw [← hKmap]
      have h1 := Subgroup.card_dvd_of_le
        (H := (S.subgroupOf H).map (QuotientGroup.mk' (C.subgroupOf H)))
        (K := (⊤ : Subgroup (↥H ⧸ C.subgroupOf H))) le_top
      rw [Subgroup.card_top] at h1
      rw [Subgroup.relIndex, Subgroup.index_eq_card]
      exact h1
    rwa [← hrelC]
  have hq_pow : ∃ k, B.relIndex S = p ^ k := by
    have hN : (B.subgroupOf S).Normal := by
      have h := Subgroup.normal_subgroupOf_of_le_normalizer hSC
      simpa [hB] using h
    have hquot : IsPGroup p (↥S ⧸ B.subgroupOf S) := hSp.to_quotient (B.subgroupOf S)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hquot
    refine ⟨k, ?_⟩
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact hk
  have hA_card : Nat.card ↥A = p ^ ((Y ⊓ C).relIndex Y).factorization p := by
    rw [hSyl.card_eq]
    congr 1
    have hsplit := Subgroup.relIndex_mul_card (H := Y ⊓ C) (K := Y)
    rw [show (Y ⊓ C) ⊓ Y = Y ⊓ C from inf_eq_left.mpr inf_le_left] at hsplit
    have : (Y ⊓ C).IsFiniteRelIndex Y := Subgroup.isFiniteRelIndex_of_finiteIndex
    have hzero : (Nat.card (Y ⊓ C : Subgroup G)).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)
    have hfac := Nat.factorization_mul
      (Subgroup.relIndex_ne_zero (H := Y ⊓ C) (K := Y))
      (Nat.card_pos (α := ↥(Y ⊓ C : Subgroup G))).ne'
    rw [hsplit] at hfac
    have hfacp := congrArg (fun f : ℕ →₀ ℕ => f p) hfac
    have hzero' : (Nat.card {x // x ∈ Y ∧ x ∈ C}).factorization p = 0 := by
      simpa using hzero
    simpa [hzero'] using hfacp
  have hq_le_A : B.relIndex S ≤ Nat.card ↥A := by
    obtain ⟨k, hk⟩ := hq_pow
    rw [hk, hA_card]
    have : (Y ⊓ C).IsFiniteRelIndex Y := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Nat.pow_le_pow_right (Nat.Prime.pos Fact.out)
      ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out
        (Subgroup.relIndex_ne_zero (H := Y ⊓ C) (K := Y))).mp (hk ▸ hq_dvd_rel))
  have hS_card : Nat.card ↥S = B.relIndex S * Nat.card ↥B := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := S)
    rw [inf_eq_left.mpr (show B ≤ S from inf_le_left)] at h
    exact h.symm
  have hTle : A ⊔ B ≤ S :=
    sup_le (show A ≤ S from inf_le_left) (show B ≤ S from inf_le_left)
  refine Subgroup.eq_of_le_of_card_ge hTle ?_
  rw [hcardT, hS_card]
  exact Nat.mul_le_mul_right _ hq_le_A

theorem commutator_inf_inf_eq_bot {p : ℕ} [Fact p.Prime] {S Y C : Subgroup G}
    (hSp : IsPGroup p S) (hcop : Nat.Coprime p (Nat.card (Y ⊓ C : Subgroup G)))
    (hcomm : ⁅Y, C⁆ ≤ Y ⊓ C) : ⁅S ⊓ Y, S ⊓ C⁆ = ⊥ := by
  have hScop : Nat.Coprime (Nat.card S) (Nat.card (Y ⊓ C : Subgroup G)) := by
    obtain ⟨n, hn⟩ := hSp.exists_card_eq
    rw [hn]
    exact hcop.pow_left n
  have hSinf : S ⊓ (Y ⊓ C) = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hScop)
  have hleS : ⁅S ⊓ Y, S ⊓ C⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haS : a ∈ S := ha.1
    have hbS : b ∈ S := hb.1
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem haS hbS) (S.inv_mem haS)) (S.inv_mem hbS)
  have hleYC : ⁅S ⊓ Y, S ⊓ C⁆ ≤ Y ⊓ C :=
    (Subgroup.commutator_mono inf_le_right inf_le_right).trans hcomm
  have hle : ⁅S ⊓ Y, S ⊓ C⁆ ≤ S ⊓ (Y ⊓ C) := le_inf hleS hleYC
  rw [hSinf] at hle
  exact le_bot_iff.mp hle

end CFSG.GroupTheory

end
