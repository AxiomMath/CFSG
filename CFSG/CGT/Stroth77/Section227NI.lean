module

public import CFSG.CGT.Stroth77.Section227
import CFSG.CGT.Stroth77.Section223Layer
import CFSG.CGT.Stroth77.Section227A

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

theorem StrothTypeIndex.eq_t200_or_eq_t201_of_familyTwo {τ : StrothTypeIndex}
    (hfam : τ.m + 2 = τ.n) (hm : τ.m = 1) : τ = .t200 1 ∨ τ = .t201 1 := by
  cases τ <;>
    simp_all [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k, Type101.k,
      Type110.k, Type111.k, Type120.k, Type121.k, Type130.k, Type131.k, Type200.k, Type201.k,
      Type210.k, Type211.k, Type220.k, Type221.k, Type230.k, Type231.k, Type300.k, Type310.k,
      Type32x.k, Type321.k, Type331.k] <;>
    omega

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem mem_inf_centralizer_mhoOne (h : F.IsD D dD) {y : G}
    (hyN : y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))
    (hyc : ∀ d ∈ D, d⁻¹ * y⁻¹ * d * y ∈
      Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2}) :
    y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) := by
  set K := F.dA.toConfig with hK
  set W := Subgroup.closure {(F.dA.c : G), (K.x * K.y) ^ 2} with hW
  have hAc : IsMulCommutative F.A := F.dA.isMulCommutative
  have hcommD := h.comm
  have hev022 : K.ev (0, 2, 2) = (K.x * K.y) ^ 2 := by
    rw [K.xy_sq]
    simp [Arch76.Config.ev, show (2 : ZMod 4).val = 2 from rfl]
  have hWV : W ≤ omegaIn 1 F.A := by
    rw [hW, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact mem_omegaIn_one_of_mul_self K.w_mem (by rw [← pow_two]; exact K.hw)
    · rw [← hev022]
      exact mem_omegaIn_one_of_mul_self (K.ev_mem _)
        (by rw [← pow_two, ← K.ev_nsmul, Arch76.two_nsmul_022, K.ev_zero])
  have hsq : ∀ d ∈ D, d ^ 2 * y = y * d ^ 2 := by
    intro d hd
    set k := d⁻¹ * y⁻¹ * d * y with hk
    have hkV := (mem_omegaIn_one_iff hAc).mp (hWV (hyc d hd))
    have hkD : k ∈ D := h.A_le hkV.1
    have h1 : y⁻¹ * d * y = d * k := by rw [hk]; group
    have h2 : y⁻¹ * d ^ 2 * y = d ^ 2 := by
      rw [Arch76.Config.conj_pow_eq, h1, pow_two, pow_two,
        show d * k * (d * k) = d * d * (k * k) by
          rw [mul_assoc d k (d * k), ← mul_assoc k d k, hcommD k hkD d hd]; group,
        hkV.2, mul_one]
    calc d ^ 2 * y = y * (y⁻¹ * d ^ 2 * y) := by group
      _ = y * d ^ 2 := by rw [h2]
  have hle : mhoOne D ≤ Subgroup.centralizer ({y} : Set G) :=
    GroupTheory.HuppertProduct.mho_le_of_forall fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hsq d hd)
  refine ⟨hyN, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

end StrothFrame.IsD

theorem ni_of_h224a_of_h225
    (H2a : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 1 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ z ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G),
        z * z = 1 → z ∈ omegaIn 1 D)
    (H3a : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ z ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G),
        z * z = 1 → z ∈ omegaIn 1 D) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      τ.m ≠ τ.n → τ ≠ .t200 1 → τ ≠ .t201 1 →
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G), y * y = 1 →
        y * (F.dA.c : G) = (F.dA.c : G) * y →
        (∀ d ∈ D, d⁻¹ * y⁻¹ * d * y ∈
          Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2}) → y ∈ D := by
  intro G _ _ F D τ dD h hns hmn h200 h201 y hyN hy2 _ hyc
  have hyR := h.mem_inf_centralizer_mhoOne hyN hyc
  have hcard : Nat.card D = 2 ^ (τ.m + τ.n + τ.n) := by
    rw [dD.card, show τ.k 2 = τ.n by simpa using congrFun τ.k_eq 2]
    rfl
  have h32 : 32 ≤ Nat.card D := F.dA.card_eq_32 ▸ Subgroup.card_le_of_le h.A_le
  rcases StrothTypeIndex.m_eq_n_or_succ_or_succ_succ τ with hfam | hfam | hfam
  · by_cases hm : 2 ≤ τ.m
    · exact omegaIn_le 1 D (H2a h hfam hm hns y hyR hy2)
    · exfalso
      rw [← hfam] at hcard
      obtain h0 | h1 : τ.m = 0 ∨ τ.m = 1 := by omega
      · rw [hcard, h0] at h32
        norm_num at h32
      · exact h.card_ne_32 (by rw [hcard, h1]; norm_num)
  · by_cases hm : 2 ≤ τ.m
    · exact omegaIn_le 1 D (H3a h hfam hm hns y hyR hy2)
    · exfalso
      obtain h0 | h1 : τ.m = 0 ∨ τ.m = 1 := by omega
      · rw [hcard, ← hfam, h0] at h32
        norm_num at h32
      · rcases StrothTypeIndex.eq_t200_or_eq_t201_of_familyTwo hfam h1 with h' | h'
        exacts [h200 h', h201 h']
  · exact absurd hfam hmn

theorem ni_of_h224a_of_h225_of_hC5
    (H2a : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 1 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ z ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G),
        z * z = 1 → z ∈ omegaIn 1 D)
    (H3a : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ z ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G),
        z * z = 1 → z ∈ omegaIn 1 D)
    (hC5 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      (τ = .t200 1 ∨ τ = .t201 1) →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer (F.A : Set G),
        (∀ d ∈ D, x⁻¹ * d * x = d) ∨
          (x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
            x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5)) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) → τ.m ≠ τ.n →
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G), y * y = 1 →
        y * (F.dA.c : G) = (F.dA.c : G) * y →
        (∀ d ∈ D, d⁻¹ * y⁻¹ * d * y ∈
          Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2}) → y ∈ D := by
  intro G _ _ F D τ dD h hns hmn y hyN hy2 hyw hyc
  by_cases ht : τ = .t200 1 ∨ τ = .t201 1
  · exact h.mem_of_t2m1 ht (hC5 F D τ dD h ht hns) hyN hyw hyc
  · push Not at ht
    exact ni_of_h224a_of_h225 H2a H3a F D τ dD h hns hmn ht.1 ht.2 y hyN hy2 hyw hyc

end CFSG.CGT.Stroth77
