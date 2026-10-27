module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Closed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldCore
public import CFSG.Goldschmidt.Final
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma413

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_of_stronglyClosed_of_isSimpleGroup
    [IsSimpleGroup G] {A S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hAS : A ≤ S)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA1 : A ≠ ⊥) (hev : Even (Nat.card G))
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ A) :
    ∀ x ∈ S, x ^ 2 = 1 → x ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Sylow 2 G := Sylow.ofCard S (by rw [hS.card_eq, card_top]) with hS'
  have hS'c : (S' : Subgroup G) = S := Sylow.coe_ofCard _ _
  have hAS' : A ≤ (S' : Subgroup G) := by rw [hS'c]; exact hAS
  have hcl' : Open.fusionStronglyClosed (A : Set G) (S' : Subgroup G) := by
    rw [hS'c]
    exact hcl
  have htop : normalClosure (A : Set G) = ⊤ := by
    rcases (normalClosure_normal (s := (A : Set G))).eq_bot_or_eq_top with h1 | h1
    · exact absurd (by rw [eq_bot_iff, ← h1]; exact le_normalClosure) hA1
    · exact h1
  have hO : Open.goldschmidtOddCore G = ⊥ := by
    rcases (Open.goldschmidtOddCore_normal G).eq_bot_or_eq_top with h1 | h1
    · exact h1
    · exfalso
      have h2 := odd_card_pPrimeCore_two G
      rw [← Goldschmidt.goldschmidtOddCore_eq_pPrimeCore, h1, card_top] at h2
      exact Nat.not_even_iff_odd.mpr h2 hev
  obtain ⟨hPE, hAeq, -⟩ := AschbacherTheorem3.goldschmidt_core Goldschmidt.topStatement G S' A
    hAS' (isMulCommutative_of_sq_eq_one hA2) hcl' htop hO
  intro x hxS hx2
  have hPn : (Open.pCore 2 G).Normal := by
    infer_instance
  rcases hPn.eq_bot_or_eq_top with h1 | h1
  · rw [h1, bot_sup_eq] at hPE
    rw [hAeq, h1, bot_sup_eq]
    refine subset_closure ⟨mem_inf.mpr ⟨?_, ?_⟩, hx2⟩
    · rw [hS'c]
      exact hxS
    · rw [hPE]
      exact mem_top x
  · rw [hAeq, h1]
    exact mem_sup_left (mem_top x)

theorem foote_lemma_4_14_nonempty
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) (hRO : FooteL2RootedOuter)
    (hAR : FooteAutRankThree) {M : Subgroup G} (hM : IsFooteM L M)
    (hPE : FooteEvenOrNormalizes M) (hne : ∃ t : G, FooteInCC M t) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  obtain ⟨t₁, ht₁, t₂, ht₂K, ht₂, hne'⟩ :=
    foote_lemma_4_13 h h47 hST hAsc h2An hA5 hE8 hK hcalc hFI hRO hAR hM hPE hne
  obtain ⟨T, A, S, hT, hA, hA8, ht₁A, htr, hACC, hS, hSA, hTS, hSC⟩ :=
    exists_omega_sylow h h47 hST hAsc h2An hM ht₁ ht₂ ht₂K hne'
  set C := coreActionKernel M with hC
  set N := normalizer (M : Set G) with hN
  have ht₁1 : t₁ ≠ 1 := fun h1 => by
    have h2 := ht₁.1
    rw [h1, orderOf_one] at h2
    omega
  have hcl := stronglyClosed_of_omega_sylow h h47 hST hAsc h2An hA5 hE8 hK hcalc hM hPE hT hA
    ht₁A ht₁1 htr hACC hS hSA hTS hSC
  have hAS : A ≤ S := hA.1.trans hTS
  have hAC : A ≤ C := hA.1.trans hT.le
  obtain ⟨W, hW, hWA⟩ := exists_isKleinFour_le hA.2.1 (by omega)
  have hNA : normalizer (A : Set G) ≤ N := foote_cor_4_8_iv h h47 hST hM hAC hW hWA
  have hSG := isSylowOf_top_of_stronglyClosed hS hAS hNA hcl
  have hA1' : A ≠ ⊥ := fun h1 => ht₁1 (by
    have h2 := ht₁A
    rwa [h1, mem_bot] at h2)
  have hev : Even (Nat.card G) := by
    rw [even_iff_two_dvd, ← ht₁.1]
    exact orderOf_dvd_natCard t₁
  have hinv := mem_of_stronglyClosed_of_isSimpleGroup hSG hAS hA.2.1 hA1' hev hcl
  obtain ⟨V, hV, hVM⟩ := hM.exists_isKleinFour h
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  obtain ⟨k, hkN, hk⟩ := exists_conj_le_of_isSylowOf hS (hVM.trans le_normalizer) hVp
  obtain ⟨w, hwV, hw1, -, -⟩ := exists_mem_ne_ne (le_of_eq hV.card_four.symm) (1 : G) 1
  have hw2 : w ^ 2 = 1 := sq_eq_one_of_isKleinFour hV hwV
  have hw'S : k⁻¹ * w * k ∈ S := hk w hwV
  have hw'M : k⁻¹ * w * k ∈ M := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hkN) w).mp (hVM hwV)
    rwa [inv_inv] at h1
  have hw'2 : (k⁻¹ * w * k) ^ 2 = 1 := by
    calc (k⁻¹ * w * k) ^ 2 = k⁻¹ * w ^ 2 * k := by rw [sq, sq]; group
      _ = 1 := by rw [hw2]; group
  have hw'1 : k⁻¹ * w * k ≠ 1 := fun h1 => hw1 (by
    calc w = k * (k⁻¹ * w * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have hw'O : k⁻¹ * w * k ∈ oddCoreIn M :=
    hM.inf_coreActionKernel_le h (mem_inf.mpr ⟨hw'M, hAC (hinv _ hw'S hw'2)⟩)
  have h1 := Subgroup.orderOf_dvd_natCard _ hw'O
  rw [orderOf_eq_prime hw'2 hw'1] at h1
  exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn M)) (even_iff_two_dvd.mpr h1)

end CFSG.ComponentClassification.FooteLit
