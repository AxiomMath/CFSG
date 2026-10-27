module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrRankGap

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {X : Type} [Group X] [Finite X]

theorem rank_gap_of_bound {a : X} (ha : orderOf a = 2) {J : Subgroup X}
    (hJa : J ≤ centralizer ({a} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    {b : X} {L : Subgroup X} (hC : UnbalancedGS.GSCorr a J b L)
    (hnotiso : ¬ UnbalancedGS.GSIsoCorr a J b L)
    (hdle : (pPrimeCore 2 L).index ≤ (pPrimeCore 2 J).index)
    (hrank : (pPrimeCore 2 L).index = (pPrimeCore 2 J).index →
      pRank 2 ↥(centralizer ({b} : Set X) ⊓ normalizer (L : Set X) ⊓ coreActionKernel L) ≤
        pRank 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X) ⊓ coreActionKernel J))
    {S P T : Subgroup X} (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (hbS : b ∈ S)
    (hP : P = S ⊓ (centralizer ({a} : Set X) ⊓ normalizer (J : Set X) ⊓ coreActionKernel J))
    (hT : T = P ⊓ centralizer ({b} : Set X)) (hJ2 : 2 ≤ pRank 2 ↥J) :
    conjugate L a ≠ L ∧ (pPrimeCore 2 L).index = (pPrimeCore 2 J).index ∧ T < P ∧
      8 ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hP hT
  have hcmp := UnbalancingLocal.correspondence_quotient_order_comparison hC
  have hcorr := hC
  obtain ⟨-, hbo, hab, -, -, hLb, hL, hbN, hcomm, -⟩ := hcorr
  set HJ := centralizer ({a} : Set X) ⊓ normalizer (J : Set X) with hHJdef
  set QJ := HJ ⊓ coreActionKernel J with hQJdef
  set P := S ⊓ QJ with hPdef
  set T := P ⊓ centralizer ({b} : Set X) with hTdef
  have hbr : ∀ Y : Subgroup X, pRank 2 ↥Y = Open.pRank 2 Y := fun Y =>
    (SectionRank.pRank_eq_open_pRank_top 2 Y).trans (SectionRank.pRank_eq_pRank_top_subgroup Y).symm
  have hdge : (pPrimeCore 2 J).index ≤ (pPrimeCore 2 L).index := by
    rw [index_eq_card, index_eq_card]
    exact hcmp.1
  have hdeq : (pPrimeCore 2 L).index = (pPrimeCore 2 J).index := le_antisymm hdle hdge
  have hne : conjugate L a ≠ L := by
    intro hLa
    apply hnotiso
    exact (hcmp.2.1 hLa).mp (by rw [← index_eq_card, ← index_eq_card]; exact hdeq.symm)
  have hQLQJ := hrank hdeq
  obtain ⟨P₀, hP₀⟩ := hSsyl
  have hS2 : IsPGroup 2 S := by
    have h1 : IsPGroup 2 ((P₀ : Subgroup HJ).map HJ.subtype) := P₀.isPGroup'.map HJ.subtype
    rwa [hP₀, map_subgroupOf_eq_of_le hSH] at h1
  have haP : a ∈ P := mem_inf_coreActionKernel_of_sylow ha hJa ⟨P₀, hP₀⟩
  have haT : a ∈ T := mem_inf.mpr ⟨haP, mem_centralizer_singleton_iff.mpr hab⟩
  have hbHJ : b ∈ HJ := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hab.symm, hbN⟩
  have hbT : b ∈ T := mem_inf.mpr ⟨mem_inf.mpr ⟨hbS, mem_inf.mpr ⟨hbHJ,
    mem_coreActionKernel.mpr ⟨hbN, hcomm⟩⟩⟩, mem_centralizer_singleton_iff.mpr rfl⟩
  have hab' : a ≠ b := by
    intro heq
    apply hne
    rw [heq]
    exact conjugate_eq_self_of_le_centralizer hLb
  obtain ⟨hEA, hE4⟩ := closure_pair_elementary ha hbo hab hab'
  have hET : closure ({a, b} : Set X) ≤ T := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact haT
    · exact hbT
  have hPS : P ≤ S := inf_le_left
  have hT2 : IsPGroup 2 T := hS2.to_le (inf_le_left.trans hPS)
  have hTle : T ≤ centralizer ({a} : Set X) ⊓ centralizer ({b} : Set X) ⊓
      normalizer (J : Set X) := fun u hu => by
    obtain ⟨hP', hCb'⟩ := mem_inf.mp hu
    have hHJ' := (mem_inf.mp (mem_inf.mp hP').2).1
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hHJ').1, hCb'⟩, (mem_inf.mp hHJ').2⟩
  have hJT : ∀ u ∈ T, ∀ j ∈ J, j⁻¹ * u⁻¹ * j * u ∈ (pPrimeCore 2 J).map J.subtype := fun u hu =>
    (mem_coreActionKernel.mp (mem_inf.mp (mem_inf.mp (mem_inf.mp hu).1).2).2).2
  obtain ⟨R, -, -, -, -, -, -, hrk, hLJ⟩ :=
    swapped_correspondence_centralizer_rank_bound hC hne hdeq.symm hT2 hTle haT hJT
  rw [hLJ] at hrk
  have hT2r : 2 ≤ pRank 2 ↥T := by
    rw [hbr]
    exact SectionRank.le_pRank one_lt_two hET
      ((SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mp hEA) (by rw [hE4]; norm_num)
  have hPQJ : pRank 2 ↥P = pRank 2 ↥QJ := (sylow_inf_coreActionKernel hSH ⟨P₀, hP₀⟩).2
  have hlt : pRank 2 ↥T < pRank 2 ↥P := by omega
  have hTP : T < P := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hne, hdeq, hTP, ?_⟩
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have h4 : 4 ≤ Nat.card T := hE4 ▸ card_le_of_le hET
  rw [hk] at h4 ⊢
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    interval_cases k <;> simp at h4
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · exfalso
    have hk2' : k = 2 := by omega
    subst hk2'
    have hTE : closure ({a, b} : Set X) = T := eq_of_le_of_card_ge hET (by rw [hk, hE4]; norm_num)
    have hP2 : IsPGroup 2 P := hS2.to_le hPS
    have hTEA : Assembly.IsElemAbelian 2 T := by
      rw [← hTE]
      exact (SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mp hEA
    have hT4 : Nat.card ↥T = 4 := by
      rw [← hTE, hE4]
    have h5 := Assembly.Dichotomy.four_involution_centralizer_rank_bound hP2
      (mem_inf.mp hbT).1 hTEA hT4
    have h6 : pRank 2 ↥P ≤ 2 := by
      rw [hbr]
      exact h5
    omega
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3

end CFSG.ComponentClassification.GSThmB.CorC
