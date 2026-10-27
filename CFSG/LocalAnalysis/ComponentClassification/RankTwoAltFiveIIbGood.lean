module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbSylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEps

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem isSylowOf_centralizer_V₀ (hm : MType (R ⊔ T) P) (hP64 : Nat.card P = 64) :
    IsSylowOf 2 P (centralizer (V₀ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC₀ : P ≤ centralizer (V₀ : Set G) := fun p hp => (mem_transvGroup.mp (hP.le hp)).2.1
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_le hPC₀ hP.isPGroup
  by_contra hne
  have hlt : P < Q := lt_of_le_of_ne hPQ fun he => hne (he ▸ hQ)
  obtain ⟨n, hn, hnP⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer hQ.isPGroup hlt)
  obtain ⟨hnQ, hnN⟩ := mem_inf.mp hn
  have hnV : n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := by
    have hPn : rightConjugate P n = P := (rightConjugate_eq_self_iff _ n).mpr hnN
    have hVn : rightConjugate (R ⊔ T) n ≤ P := by
      rw [← hPn]
      exact map_mono (hPC ▸ inf_le_left)
    exact (rightConjugate_eq_self_iff _ n).mp (h.eq_of_elemAbelian_P_of_mType hP hPC hm hVn
      (isElemAbelian_rightConjugate h.loc.elem n) (by rw [rightConjugate_card, h.loc.card]))
  obtain ⟨p, hp, hnp⟩ := h.exists_mul_mem_normalizer_R hP hPC hP64 hnV
  have hpQ : p ∈ Q := hPQ hp
  have hmQ : n * p ∈ Q := mul_mem hnQ hpQ
  have hm2 : IsPGroup 2 (zpowers (n * p)) := hQ.isPGroup.to_le (zpowers_le.mpr hmQ)
  have hpV : p ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := (mem_transvGroup.mp (hP.le hp)).1
  have hmV : n * p ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := mul_mem hnV hpV
  have hmC : n * p ∈ centralizer (V₀ : Set G) := hQ.le hmQ
  have hmCV := h.mem_centralizer_of_mem_centralizer_V₀ hmV hnp hm2 hmC
  have hmT : n * p ∈ transvGroup (R ⊔ T) V₀ := h.centralizer_le_transvGroup hmCV
  have hsup : P ⊔ zpowers (n * p) = P :=
    hP.eq_of_le le_sup_left (sup_le hP.le (zpowers_le.mpr hmT))
      (hQ.isPGroup.to_le (sup_le hPQ (zpowers_le.mpr hmQ)))
  have hmP : n * p ∈ P := hsup ▸ mem_sup_right (mem_zpowers _)
  apply hnP
  have := mul_mem hmP (inv_mem hp)
  rwa [mul_inv_cancel_right] at this

theorem mul_self_mem_of_centralizer (hm : MType (R ⊔ T) P) (hP64 : Nat.card P = 64) (y u : G)
    (hu : u ∈ centralizer ((rightConjugate V₀ y : Subgroup G) : Set G))
    (hu2 : IsPGroup 2 (zpowers u)) : u * u ∈ rightConjugate V₀ y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [centralizer_rightConjugate, mem_rightConjugate_iff] at hu
  obtain ⟨n, hn⟩ := hu2 ⟨u, mem_zpowers u⟩
  have hn' : u ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hu'2 : IsPGroup 2 (zpowers (y * u * y⁻¹)) := by
    apply isPGroup_zpowers_of_pow_eq_one (n := n)
    rw [conj_pow, hn']
    group
  obtain ⟨S, hS, hSu⟩ := exists_isSylowOf_le (zpowers_le.mpr hu) hu'2
  obtain ⟨c, hc, hSc⟩ :=
    Lemma22.exists_conj_eq_of_isSylowOf (h.isSylowOf_centralizer_V₀ hP hPC hm hP64) hS
  have hmem : y * u * y⁻¹ ∈ Lemma34.conj P c := hSc ▸ hSu (mem_zpowers _)
  rw [Lemma34.mem_conj_iff] at hmem
  have hsq := h.P_mul_self_mem_V₀ hP hPC hmem
  obtain ⟨w, hw⟩ : ∃ w : G, w = c⁻¹ * (y * u * y⁻¹) * c * (c⁻¹ * (y * u * y⁻¹) * c) := ⟨_, rfl⟩
  rw [← hw] at hsq
  rw [mem_rightConjugate_iff]
  have e : y * (u * u) * y⁻¹ = c * w * c⁻¹ := by rw [hw]; group
  rw [e, ← mem_centralizer_iff.mp hc w hsq, mul_inv_cancel_right]
  exact hsq

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
