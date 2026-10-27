module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedEmbeddingKernel
public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316Alpha
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L33
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolMoved

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup FooteLit UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

@[expose] def MarkedAbsorptionLocal (S : Set (Subgroup G)) (T : Type*) [Group T] : Prop :=
  ∀ H P : Subgroup G, H ≠ ⊤ → Balanced S T H → Marked S T P → P ≤ H →
    (∃ a ∈ H, orderOf a = 2 ∧ a ∈ coreActionKernel P) →
    ∃ J ∈ markedComponents S T H, P ≤ J

theorem two_le_pRank_of_marked {T : Type*} [Group T] [Finite T]
    {S : Set (Subgroup G)} {P : Subgroup G}
    (hP : Marked S T P) (hTrank : 2 ≤ CFSG.pRank 2 T) :
    2 ≤ CFSG.Open.pRank 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eP⟩ := hP.2.1
  have hker : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥P) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (pPrimeCore_coprime_card (p := 2) (G := ↥P))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup P,
    ← CFSG.SectionRank.pRank_quotient_eq (p := 2) (N := pPrimeCore 2 ↥P) hker,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) (by norm_num) eP,
    ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 T]
  exact hTrank

theorem mem_of_coreActionKernel_of_involution {L M : Subgroup G}
    (hL : IsTwoComponentIn L M)
    (hC : ∀ b ∈ L, orderOf b = 2 → centralizer ({b} : Set G) ≤ M)
    {s : G} (hs2 : orderOf s = 2) (hsK : s ∈ coreActionKernel L) : s ∈ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hbL, hb2⟩ := Sol76T13.exists_orderOf_eq_two_of_isTwoComponentIn hL
  have hbb : b * b = 1 := by
    rw [← sq, ← hb2, pow_orderOf_eq_one]
  have hss : s * s = 1 := by
    rw [← sq, ← hs2, pow_orderOf_eq_one]
  have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsN : s ∈ normalizer (L : Set G) := (mem_coreActionKernel.mp hsK).1
  have hbO : b ∈ normalizer (oddCoreIn L : Set G) :=
    mem_normalizer_oddCoreIn (le_normalizer hbL)
  have hsO : s ∈ normalizer (oddCoreIn L : Set G) := mem_normalizer_oddCoreIn hsN
  have hcomm : b⁻¹ * s⁻¹ * b * s ∈ oddCoreIn L := (mem_coreActionKernel.mp hsK).2 b hbL
  rw [hb_inv, hs_inv] at hcomm
  have htbs : s * b * s * b ∈ oddCoreIn L := by
    have h := inv_mem hcomm
    rwa [show (b * s * b * s)⁻¹ = s⁻¹ * b⁻¹ * s⁻¹ * b⁻¹ by group,
      hs_inv, hb_inv] at h
  have htb : s * b * s⁻¹ * b ∈ oddCoreIn L := by
    rwa [hs_inv]
  obtain ⟨c, hcO, hcommc⟩ := Sol76.exists_conj_commute (O := oddCoreIn L)
    (odd_card_oddCoreIn L) hbb hbO hsO htb (k := 1) (by simpa [pow_two] using hss)
  let b' : G := c * b * c⁻¹
  have hcL : c ∈ L := map_subtype_le (pPrimeCore 2 ↥L) hcO
  have hb'L : b' ∈ L := by
    dsimp only [b']
    exact L.mul_mem (L.mul_mem hcL hbL) (L.inv_mem hcL)
  have hb'2 : orderOf b' = 2 := by
    dsimp only [b']
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hb2]
  have hsComm : s ∈ centralizer ({b'} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact hcommc
  exact hC b' hb'L hb'2 hsComm

theorem markedComponent_of_coreActionKernel_involution
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    {S : Set (Subgroup G)} (hFam : IsomorphicFamily S T)
    (hAbs : MarkedAbsorptionLocal S T) (hTrank : 2 ≤ CFSG.pRank 2 T)
    {M₁ M₂ : Subgroup G} (hM₁ne : M₁ ≠ ⊤) (hBal₁ : Balanced S T M₁)
    (hM₂ne : M₂ ≠ ⊤) (hBal₂ : Balanced S T M₂)
    (hC₁ : ∀ K ∈ markedComponents S T M₁, ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ M₁)
    (hC₂ : ∀ K ∈ markedComponents S T M₂, ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ M₂)
    {K L : Subgroup G} (hK : K ∈ markedComponents S T M₁)
    (hL : L ∈ markedComponents S T M₂)
    {s : G} (hs2 : orderOf s = 2) (hsK : s ∈ K)
    (hsKerL : s ∈ coreActionKernel L) :
    L ∈ markedComponents S T M₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    norm_num at hs2
  have hss : s * s = 1 := by
    rw [← sq, ← hs2, pow_orderOf_eq_one]
  have hKM₁ : K ≤ M₁ := hK.1.1
  have hLM₂ : L ≤ M₂ := hL.1.1
  have hsM₁ : s ∈ M₁ := hKM₁ hsK
  have hsM₂ : s ∈ M₂ :=
    mem_of_coreActionKernel_of_involution hL.1 (hC₂ L hL) hs2 hsKerL
  set U : Subgroup G := zpowers s with hU
  have hU2 : IsPGroup 2 U :=
    Sol76.isPGroup_zpowers_of_pow (k := 1) (by simpa [pow_two] using hss)
  have hUne : U ≠ ⊥ := fun h => hs1 (zpowers_eq_bot.mp h)
  have hUK : U ≤ coreActionKernel L := zpowers_le.mpr hsKerL
  obtain ⟨H, hHcompU, hHmarked, hHclosure, hHcover⟩ :=
    markedST_of_isomorphicFamily hFam L hL.2 U hU2 hUK hUne
  let C : Subgroup G := centralizer ({s} : Set G)
  have hHcomp : IsTwoComponentIn H C := by
    simpa only [C, U, UnbalancedLayer.centralizer_zpowers_eq] using hHcompU
  have hC₂L : ∀ b ∈ L, orderOf b = 2 → centralizer ({b} : Set G) ≤ M₂ := hC₂ L hL
  have hKernM₂ : oddCoreIn C ⊔ twoLayerIn C ≤ M₂ :=
    oddCore_sup_twoLayerIn_centralizer_le_of_marked_topRank hFam hL.1 hL.2 hC₂L
      (k := 1) (by simpa [pow_two] using hss) hs1 hsKerL hTrank
  have hHM₂ : H ≤ M₂ :=
    (le_twoLayerIn_of_isTwoComponentIn hHcomp).trans (le_sup_right.trans hKernM₂)
  have hHM₁ : H ≤ M₁ := by
    have := hHcomp.1.trans (hC₁ K hK s hsK hs2)
    simpa only [C] using this
  have hsKerH : s ∈ coreActionKernel H :=
    mem_coreActionKernel_of_le_centralizer (by simpa only [C] using hHcomp.1)
  obtain ⟨J₁, hJ₁, hHJ₁⟩ :=
    hAbs M₁ H hM₁ne hBal₁ hHmarked hHM₁ ⟨s, hsM₁, hs2, hsKerH⟩
  obtain ⟨J₂, hJ₂, hHJ₂⟩ :=
    hAbs M₂ H hM₂ne hBal₂ hHmarked hHM₂ ⟨s, hsM₂, hs2, hsKerH⟩
  let YL : Subgroup G := fixedShadow L U
  have hYL_L : YL ≤ L := fixedShadow_le L U
  have hYL_H : YL ≤ H := by
    rw [← hHcover]
    exact le_sup_left
  have hYL_J₂ : YL ≤ J₂ := hYL_H.trans hHJ₂
  obtain ⟨eL⟩ := hL.2.2.1
  have hLq : IsQuasisimple (L ⧸ pPrimeCore 2 L) := hL.2.quotient_quasisimple hFam
  obtain ⟨hYLcoverL, -, ⟨eYL, -⟩⟩ := fixedShadow_cover_quotient hLq hU2 hUK
  have hYLq : Nonempty (YL ⧸ pPrimeCore 2 YL ≃* T) := ⟨eYL.trans eL⟩
  have hYLrank : 2 ≤ CFSG.Open.pRank 2 YL :=
    (two_le_pRank_of_marked hL.2 hTrank).trans
      (Sol76T13.pRank_le_of_sup_oddCoreIn hYL_L hYLcoverL)
  have hYLcoverJ₂ : YL ⊔ oddCoreIn J₂ = J₂ :=
    sup_oddCoreIn_eq_of_full_oddQuotient hYL_J₂ hYLq hJ₂.2.2.1
  have hJ₂eq : J₂ = L :=
    Sol76T13.eq_of_sup_oddCoreIn_eq_components hJ₂.1 hL.1
      (hC₂ J₂ hJ₂) (hC₂ L hL) hYL_J₂ hYL_L hYLcoverJ₂ hYLcoverL hYLrank
      (Subgroup.isPerfect_iff.mp (fixedShadow_perfect L U))
  have hHL : H ≤ L := hJ₂eq ▸ hHJ₂
  have hHcoverJ₁ : H ⊔ oddCoreIn J₁ = J₁ :=
    sup_oddCoreIn_eq_of_full_oddQuotient hHJ₁ hHmarked.2.1 hJ₁.2.2.1
  have hHcoverL : H ⊔ oddCoreIn L = L :=
    sup_oddCoreIn_eq_of_full_oddQuotient hHL hHmarked.2.1 hL.2.2.1
  have hJ₁eq : J₁ = L :=
    Sol76T13.eq_of_sup_oddCoreIn_eq_components hJ₁.1 hL.1
      (hC₁ J₁ hJ₁) (hC₂ L hL) hHJ₁ hHL hHcoverJ₁ hHcoverL
      (two_le_pRank_of_marked hHmarked hTrank)
      (Subgroup.isPerfect_iff.mp hHmarked.1)
  exact hJ₁eq ▸ hJ₁

theorem markedComponents_subset_of_shared_component
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    {S : Set (Subgroup G)} (hFam : IsomorphicFamily S T)
    (hAbs : MarkedAbsorptionLocal S T) (hTrank : 2 ≤ CFSG.pRank 2 T)
    {M₁ M₂ : Subgroup G} (hM₁ne : M₁ ≠ ⊤) (hBal₁ : Balanced S T M₁)
    (hM₂ne : M₂ ≠ ⊤) (hBal₂ : Balanced S T M₂)
    (hC₁ : ∀ K ∈ markedComponents S T M₁, ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ M₁)
    (hC₂ : ∀ K ∈ markedComponents S T M₂, ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ M₂)
    {J : Subgroup G} (hJ₁ : J ∈ markedComponents S T M₁)
    (hJ₂ : J ∈ markedComponents S T M₂) :
    markedComponents S T M₁ ⊆ markedComponents S T M₂ := by
  classical
  intro I hI
  by_cases hIJ : I = J
  · rwa [hIJ]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hwJ, hw2⟩ := Sol76T13.exists_orderOf_eq_two_of_isTwoComponentIn hJ₂.1
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw2
    norm_num at hw2
  have hww : w * w = 1 := by
    rw [← sq, ← hw2, pow_orderOf_eq_one]
  have hJcoreI : J ≤ coreActionKernel I :=
    CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne hI.1 hJ₁.1 hIJ
  have hwKerI : w ∈ coreActionKernel I := hJcoreI hwJ
  have hwM₁ : w ∈ M₁ := hJ₁.1.1 hwJ
  have hwM₂ : w ∈ M₂ := hJ₂.1.1 hwJ
  set U : Subgroup G := zpowers w with hU
  have hU2 : IsPGroup 2 U :=
    Sol76.isPGroup_zpowers_of_pow (k := 1) (by simpa [pow_two] using hww)
  have hUne : U ≠ ⊥ := fun h => hw1 (zpowers_eq_bot.mp h)
  have hUK : U ≤ coreActionKernel I := zpowers_le.mpr hwKerI
  obtain ⟨H, hHcompU, hHmarked, hHclosure, hHcover⟩ :=
    markedST_of_isomorphicFamily hFam I hI.2 U hU2 hUK hUne
  let C : Subgroup G := centralizer ({w} : Set G)
  have hHcomp : IsTwoComponentIn H C := by
    simpa only [C, U, UnbalancedLayer.centralizer_zpowers_eq] using hHcompU
  have hKernM₁ : oddCoreIn C ⊔ twoLayerIn C ≤ M₁ :=
    oddCore_sup_twoLayerIn_centralizer_le_of_marked hFam hI.1 hI.2 (hC₁ I hI)
      (k := 1) (by simpa [pow_two] using hww) hw1 hwKerI
      (two_le_pRank_of_marked hI.2 hTrank)
  have hHM₁ : H ≤ M₁ :=
    (le_twoLayerIn_of_isTwoComponentIn hHcomp).trans (le_sup_right.trans hKernM₁)
  have hHM₂ : H ≤ M₂ := by
    have := hHcomp.1.trans (hC₂ J hJ₂ w hwJ hw2)
    simpa only [C] using this
  have hwKerH : w ∈ coreActionKernel H :=
    mem_coreActionKernel_of_le_centralizer (by simpa only [C] using hHcomp.1)
  obtain ⟨I₁, hI₁, hHI₁⟩ :=
    hAbs M₁ H hM₁ne hBal₁ hHmarked hHM₁ ⟨w, hwM₁, hw2, hwKerH⟩
  obtain ⟨I₂, hI₂, hHI₂⟩ :=
    hAbs M₂ H hM₂ne hBal₂ hHmarked hHM₂ ⟨w, hwM₂, hw2, hwKerH⟩
  let YI : Subgroup G := fixedShadow I U
  have hYI_I : YI ≤ I := fixedShadow_le I U
  have hYI_H : YI ≤ H := by
    rw [← hHcover]
    exact le_sup_left
  have hYI_I₁ : YI ≤ I₁ := hYI_H.trans hHI₁
  have hYI_I₂ : YI ≤ I₂ := hYI_H.trans hHI₂
  obtain ⟨eI⟩ := hI.2.2.1
  have hIq : IsQuasisimple (I ⧸ pPrimeCore 2 I) := hI.2.quotient_quasisimple hFam
  obtain ⟨hYIcoverI, -, ⟨eYI, -⟩⟩ := fixedShadow_cover_quotient hIq hU2 hUK
  have hYIq : Nonempty (YI ⧸ pPrimeCore 2 YI ≃* T) := ⟨eYI.trans eI⟩
  have hYIrank : 2 ≤ CFSG.Open.pRank 2 YI :=
    (two_le_pRank_of_marked hI.2 hTrank).trans
      (Sol76T13.pRank_le_of_sup_oddCoreIn hYI_I hYIcoverI)
  have hYIcoverI₁ : YI ⊔ oddCoreIn I₁ = I₁ :=
    sup_oddCoreIn_eq_of_full_oddQuotient hYI_I₁ hYIq hI₁.2.2.1
  have hYIcoverI₂ : YI ⊔ oddCoreIn I₂ = I₂ :=
    sup_oddCoreIn_eq_of_full_oddQuotient hYI_I₂ hYIq hI₂.2.2.1
  have hYIperf : ⁅YI, YI⁆ = YI := Subgroup.isPerfect_iff.mp (fixedShadow_perfect I U)
  have hI₁eq : I₁ = I :=
    Sol76T13.eq_of_sup_oddCoreIn_eq_components hI₁.1 hI.1
      (hC₁ I₁ hI₁) (hC₁ I hI) hYI_I₁ hYI_I hYIcoverI₁ hYIcoverI hYIrank hYIperf
  have hI₂eq : I₂ = I :=
    Sol76T13.eq_of_sup_oddCoreIn_eq_components hI₂.1 hI.1
      (hC₂ I₂ hI₂) (hC₁ I hI) hYI_I₂ hYI_I hYIcoverI₂ hYIcoverI hYIrank hYIperf
  exact hI₂eq ▸ hI₂

theorem markedComponents_eq_of_shared_component
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    {S : Set (Subgroup G)} (hFam : IsomorphicFamily S T)
    (hAbs : MarkedAbsorptionLocal S T) (hTrank : 2 ≤ CFSG.pRank 2 T)
    {M₁ M₂ : Subgroup G} (hM₁ne : M₁ ≠ ⊤) (hBal₁ : Balanced S T M₁)
    (hM₂ne : M₂ ≠ ⊤) (hBal₂ : Balanced S T M₂)
    (hC₁ : ∀ K ∈ markedComponents S T M₁, ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ M₁)
    (hC₂ : ∀ K ∈ markedComponents S T M₂, ∀ b ∈ K, orderOf b = 2 →
      centralizer ({b} : Set G) ≤ M₂)
    {J : Subgroup G} (hJ₁ : J ∈ markedComponents S T M₁)
    (hJ₂ : J ∈ markedComponents S T M₂) :
    markedComponents S T M₁ = markedComponents S T M₂ := by
  exact Set.Subset.antisymm
    (markedComponents_subset_of_shared_component hFam hAbs hTrank hM₁ne hBal₁ hM₂ne hBal₂
      hC₁ hC₂ hJ₁ hJ₂)
    (markedComponents_subset_of_shared_component hFam hAbs hTrank hM₂ne hBal₂ hM₁ne hBal₁
      hC₂ hC₁ hJ₂ hJ₁)

end CFSG.ComponentClassification.FooteMarked
