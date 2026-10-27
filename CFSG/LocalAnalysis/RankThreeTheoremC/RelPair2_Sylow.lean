module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Coprime
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_of_mem_centralizer_subgroup {D : Subgroup G} {c : G}
    (hc : c ∈ centralizer (D : Set G)) : D.map (MulAut.conj c).toMonoidHom = D := by
  have hcomm : ∀ d ∈ D, c * d * c⁻¹ = d := fun d hd => by
    have := mem_centralizer_iff.mp hc d hd
    calc c * d * c⁻¹ = d * c * c⁻¹ := by rw [this]
      _ = d := by group
  have hfix : ∀ d ∈ D, (MulAut.conj c).toMonoidHom d = d := fun d hd => by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hcomm d hd
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [hfix d hd]
    exact hd
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

omit [Finite G] in
theorem le_normalizer_map_conj_of_mem_centralizer {D A : Subgroup G} {c : G}
    (hc : c ∈ centralizer (D : Set G)) (hDA : D ≤ normalizer (A : Set G)) :
    D ≤ normalizer ((A.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  rw [← map_conj_eq_of_mem_centralizer_subgroup hc, ← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hDA

theorem coprime_card_sup_of_normalized_coprime {p : ℕ} {H K B : Subgroup G} (hKH : K ≤ H)
    (hBH : B ≤ H) (hKN : H ≤ normalizer (K : Set G)) (hK : p.Coprime (Nat.card K))
    (hB : p.Coprime (Nat.card B)) : p.Coprime (Nat.card (K ⊔ B : Subgroup G)) := by
  have hKnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKN
  have hK' : p.Coprime (Nat.card (K.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
    exact hK
  have hB' : p.Coprime (Nat.card (B.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv]
    exact hB
  have hsup := normal_coprime_sup_coprime p (B.subgroupOf H) (K.subgroupOf H) hKnormal hB' hK'
  have himage : ((B.subgroupOf H) ⊔ (K.subgroupOf H)).map H.subtype = K ⊔ B := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBH, map_subgroupOf_eq_of_le hKH, sup_comm]
  rw [← himage, card_map_of_injective H.subtype_injective]
  exact hsup

theorem prime_dvd_card_invariantTwoJoinIn_inf_normalizer {p : ℕ} (hprime : p.Prime)
    (hodd : p ≠ 2) {D H K V₁ : Subgroup G} (hDp : IsPGroup p D) (hDH : D ≤ H) (hKH : K ≤ H)
    (hKN : H ≤ normalizer (K : Set G)) (hK : p.Coprime (Nat.card K)) (hV₁ : IsSylowOf 2 V₁ K)
    (hDV₁ : D ≤ normalizer (V₁ : Set G))
    (hdvd : p ∣ Nat.card (invariantTwoJoinIn D H)) :
    p ∣ Nat.card (invariantTwoJoinIn D (H ⊓ normalizer (V₁ : Set G))) := by
  classical
  by_contra hnot
  have hcop₁ : p.Coprime (Nat.card (invariantTwoJoinIn D (H ⊓ normalizer (V₁ : Set G)))) :=
    hprime.coprime_iff_not_dvd.mpr hnot
  have hcop2 : ∀ A : Subgroup G, IsPGroup 2 A → p.Coprime (Nat.card A) := by
    intro A hA
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
    rw [hn]
    exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right n
  have hDK : D ≤ normalizer (K : Set G) := hDH.trans hKN
  have hall : ∀ A : Subgroup G, A ≤ H → IsPGroup 2 A → D ≤ normalizer (A : Set G) →
      A ≤ K ⊔ invariantTwoJoinIn D (H ⊓ normalizer (V₁ : Set G)) := by
    intro A hAH hA2 hDA
    have hYc : p.Coprime (Nat.card (K ⊔ A : Subgroup G)) :=
      coprime_card_sup_of_normalized_coprime hKH hAH hKN hK (hcop2 A hA2)
    have hYN : (K ⊔ A : Subgroup G) ≤ normalizer (K : Set G) :=
      sup_le le_normalizer (hAH.trans hKN)
    have hDY : D ≤ normalizer ((K ⊔ A : Subgroup G) : Set G) :=
      (le_inf hDK hDA).trans (Subgroup.inf_normalizer_le_normalizer_sup K A)
    obtain ⟨A', hAA', hA'S, hDA'⟩ := exists_isSylowOf_normalized_containing hprime hDp hDY hYc
      (le_sup_right : A ≤ K ⊔ A) hA2 hDA
    have hKY : K ≤ K ⊔ A := le_sup_left
    have hS₁ : IsSylowOf 2 (A' ⊓ K) K := hA'S.inf_of_le_normalizer hKY hYN
    have hA'N : A' ≤ normalizer (K : Set G) := hA'S.le.trans hYN
    have hDS₁ : D ≤ normalizer ((A' ⊓ K : Subgroup G) : Set G) :=
      common_normalizer_le_normalizer_inf D A' K hDA' hDK
    obtain ⟨c, hcK, hcC, hc⟩ := exists_mem_centralizer_conj_eq_of_isSylowOf hprime hDp hDK hK hS₁
      hV₁ hDS₁ hDV₁
    have hA'V₁ : A' ≤ normalizer ((A' ⊓ K : Subgroup G) : Set G) :=
      common_normalizer_le_normalizer_inf A' A' K le_normalizer hA'N
    have hAcN : A.map (MulAut.conj c).toMonoidHom ≤ normalizer (V₁ : Set G) := by
      rw [← hc, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono (hAA'.trans hA'V₁)
    have hAcH : A.map (MulAut.conj c).toMonoidHom ≤ H :=
      (conjugate_subgroup_le_iff_of_conjugator_mem A H c (hKH hcK)).mpr hAH
    have hAcJ : A.map (MulAut.conj c).toMonoidHom ≤ invariantTwoJoinIn D (H ⊓ normalizer
        (V₁ : Set G)) :=
      le_invariantTwoJoinIn (le_inf hAcH hAcN) (hA2.map _)
        (le_normalizer_map_conj_of_mem_centralizer hcC hDA)
    intro x hx
    have hy : c * x * c⁻¹ ∈ invariantTwoJoinIn D (H ⊓ normalizer (V₁ : Set G)) :=
      hAcJ ⟨x, hx, rfl⟩
    have hyH : c * x * c⁻¹ ∈ H :=
      (invariantTwoJoinIn_le D (H ⊓ normalizer (V₁ : Set G))).trans inf_le_left hy
    have hycy : (c * x * c⁻¹) * c * (c * x * c⁻¹)⁻¹ ∈ K :=
      (mem_normalizer_iff.mp (hKN hyH) c).mp hcK
    have hk : c⁻¹ * ((c * x * c⁻¹) * c * (c * x * c⁻¹)⁻¹) ∈ K := K.mul_mem (K.inv_mem hcK) hycy
    have hxeq : x = (c⁻¹ * ((c * x * c⁻¹) * c * (c * x * c⁻¹)⁻¹)) * (c * x * c⁻¹) := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hk hy
  have hjoin : invariantTwoJoinIn D H ≤ K ⊔ invariantTwoJoinIn D (H ⊓ normalizer (V₁ : Set G)) :=
    invariantTwoJoinIn_le_of_forall hall
  have hJH : invariantTwoJoinIn D (H ⊓ normalizer (V₁ : Set G)) ≤ H :=
    (invariantTwoJoinIn_le _ _).trans inf_le_left
  have hcop : p.Coprime (Nat.card (K ⊔ invariantTwoJoinIn D (H ⊓ normalizer (V₁ : Set G)) :
      Subgroup G)) := coprime_card_sup_of_normalized_coprime hKH hJH hKN hK hcop₁
  exact (hprime.coprime_iff_not_dvd.mp hcop) (hdvd.trans (Subgroup.card_dvd_of_le hjoin))

theorem IsOptimalRelPair.isSylowOf_pCoreOf {p : ℕ} (hprime : p.Prime) (hodd : p ≠ 2)
    {M D R T H V : Subgroup G} (hDp : IsPGroup p D) (hopt : IsOptimalRelPair p M D R T H V) :
    IsSylowOf 2 (pCoreOf 2 H) ((primeComplementCore (G := H) p).map H.subtype) := by
  classical
  have hpair := hopt.pair
  set K := (primeComplementCore (G := H) p).map H.subtype with hK
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hKN : H ≤ normalizer (K : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype H _
  have hKc : p.Coprime (Nat.card K) := by
    rw [hK, card_map_of_injective H.subtype_injective]
    exact primeComplementCore_coprime p
  have hcop2 : ∀ A : Subgroup G, IsPGroup 2 A → p.Coprime (Nat.card A) := by
    intro A hA
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
    rw [hn]
    exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right n
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hpair.cand.base_le
  have hDK : D ≤ normalizer (K : Set G) := hDH.trans hKN
  have hVHM : V ≤ H ⊓ M := hpair.maximal.1
  have hV2 : IsPGroup 2 V := hpair.maximal.2.1
  have hDV : D ≤ normalizer (V : Set G) := hpair.maximal.2.2.1
  have hVH : V ≤ H := hVHM.trans inf_le_left
  have hVM : V ≤ M := hVHM.trans inf_le_right
  have hO₂K : pCoreOf 2 H ≤ K := by
    have hcop : p.Coprime (Nat.card ((pCoreOf 2 H).subgroupOf H)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 H)).toEquiv]
      exact hcop2 _ (pCoreOf_isPGroup 2 H)
    have h := Subgroup.map_mono (f := H.subtype)
      (normal_coprime_le_primeComplementCore p _ (pCoreOf_normal 2 H) hcop)
    rwa [map_subgroupOf_eq_of_le (pCoreOf_le 2 H)] at h
  have hY₀c : p.Coprime (Nat.card (K ⊔ V : Subgroup G)) :=
    coprime_card_sup_of_normalized_coprime hKH hVH hKN hKc (hcop2 V hV2)
  have hY₀N : (K ⊔ V : Subgroup G) ≤ normalizer (K : Set G) :=
    sup_le le_normalizer (hVH.trans hKN)
  have hDY₀ : D ≤ normalizer ((K ⊔ V : Subgroup G) : Set G) :=
    (le_inf hDK hDV).trans (Subgroup.inf_normalizer_le_normalizer_sup K V)
  obtain ⟨V', hVV', hV'S, hDV'⟩ := exists_isSylowOf_normalized_containing hprime hDp hDY₀ hY₀c
    (le_sup_right : V ≤ K ⊔ V) hV2 hDV
  have hV₁S : IsSylowOf 2 (V' ⊓ K) K := hV'S.inf_of_le_normalizer le_sup_left hY₀N
  have hDV₁ : D ≤ normalizer ((V' ⊓ K : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf D V' K hDV' hDK
  have hV'N : V' ≤ normalizer ((V' ⊓ K : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf V' V' K le_normalizer (hV'S.le.trans hY₀N)
  have hVN : V ≤ normalizer ((V' ⊓ K : Subgroup G) : Set G) := hVV'.trans hV'N
  set V₁ := V' ⊓ K with hV₁
  have hO₂V₁ : pCoreOf 2 H ≤ V₁ := by
    have hnormal : ((pCoreOf 2 H).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hO₂K).mpr
        (hKH.trans (localGroup_le_normalizer_pCoreOf 2 H))
    have hpg : IsPGroup 2 ((pCoreOf 2 H).subgroupOf K) :=
      (pCoreOf_isPGroup 2 H).of_equiv (Subgroup.subgroupOfEquivOfLe hO₂K).symm
    obtain ⟨Q, hQ⟩ := hV₁S.exists_sylow_eq_subgroupOf
    have hle := hpg.le_sylow_of_normal Q
    rw [hQ] at hle
    intro n hn
    exact hle (show (⟨n, hO₂K hn⟩ : K) ∈ (pCoreOf 2 H).subgroupOf K from hn)
  have hV₁ne : V₁ ≠ ⊥ := fun h =>
    twoLocal_pCoreOf_ne_bot H hpair.cand.twoLocal (le_bot_iff.mp (h ▸ hO₂V₁))
  have hH₂ : relPairBase R T ⊔ D ≤ normalizer (V₁ : Set G) :=
    sup_le (hpair.base_le.trans hVN) hDV₁
  have hcand : IsRelPairCandidate p D R T (normalizer (V₁ : Set G)) :=
    ⟨⟨V₁, hV₁ne, hV₁S.isPGroup, rfl⟩, hH₂,
      (prime_dvd_card_invariantTwoJoinIn_inf_normalizer hprime hodd hDp hDH hKH hKN hKc hV₁S hDV₁
        hpair.cand.not_coprime).trans
        (Subgroup.card_dvd_of_le (invariantTwoJoinIn_mono inf_le_right))⟩
  have hVle : V ≤ normalizer (V₁ : Set G) ⊓ M := le_inf hVN hVM
  obtain ⟨Vs, hVVs, hmax⟩ := exists_invariantTwoMaximalWithin_containing D
    (normalizer (V₁ : Set G) ⊓ M) V hVle hV2 hDV
  have hpair' : IsRelPairCandidatePair p M D R T (normalizer (V₁ : Set G)) Vs :=
    ⟨hcand, hmax, hpair.base_le.trans hVVs⟩
  have hcardV : Nat.card Vs = Nat.card V :=
    le_antisymm (hopt.card_le _ _ hpair') (Subgroup.card_le_of_le hVVs)
  have hcore := hopt.core_le _ _ hpair' hcardV
  have hV₁O₂ : V₁ ≤ pCoreOf 2 (normalizer (V₁ : Set G)) :=
    normal_pGroup_le_pCoreOf 2 V₁ _ le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl) hV₁S.isPGroup
  have hEq : pCoreOf 2 H = V₁ :=
    Subgroup.eq_of_le_of_card_ge hO₂V₁ ((Subgroup.card_le_of_le hV₁O₂).trans hcore)
  rw [hEq]
  exact hV₁S

end CFSG.LocalAnalysis.RankThreeTheoremC
