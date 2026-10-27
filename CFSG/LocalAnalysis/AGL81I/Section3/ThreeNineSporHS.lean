module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHull
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOverHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoHSU35
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open CFSG.Open
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement)

theorem statedClassicalModel_catU35 :
    StatedClassicalModel (TauCeti.CFSGIndex.lie
      CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.threeFourTwoU35Index).Group .PSU 3 5 1 := by
  have hL := CFSG.Models.lieModel_twistedA 2
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.threeFourTwoQFive
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.valid_twistedA_two_threeFourTwoQFive
    (MulEquiv.refl _)
  simp only [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
    TauCeti.LieTypeIndex.characteristic_twistedA, TauCeti.LieTypeIndex.fieldExponent_twistedA]
    at hL
  exact hL.2.resolve_right fun h => absurd h.1 (by norm_num)

theorem statedClassicalModel_psu_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {n p f : ℕ} (h : StatedClassicalModel B .PSU n p f) : StatedClassicalModel A .PSU n p f := by
  obtain ⟨hadm, F, hF, hFf, hc, ⟨e'⟩⟩ := h
  exact ⟨hadm, F, hF, hFf, hc, ⟨e.trans e'⟩⟩

theorem statedClassicalModel_oPrime_hsOUA2 :
    StatedClassicalModel (oPrimeModPrimeComplement 7 CFSG.AGLEmbeddingD2.hsOUA2) .PSU 3 5 1 := by
  have hF := CFSG.AGLEmbeddingD2.hsU35Facts
  have eM : ↥(CFSG.AGLEmbeddingD2.hsOUA.subgroupOf CFSG.AGLEmbeddingD2.hsOUA2) ≃*
      ↥CFSG.AGLEmbeddingD2.hsOUA := Subgroup.subgroupOfEquivOfLe hF.UA_le_UA2
  have hMc : Nat.card (CFSG.AGLEmbeddingD2.hsOUA.subgroupOf CFSG.AGLEmbeddingD2.hsOUA2) =
      126000 := (Nat.card_congr eM.toEquiv).trans hF.card_UA
  have hMidx : (CFSG.AGLEmbeddingD2.hsOUA.subgroupOf CFSG.AGLEmbeddingD2.hsOUA2).index = 2 := by
    have h1 := (CFSG.AGLEmbeddingD2.hsOUA.subgroupOf CFSG.AGLEmbeddingD2.hsOUA2).card_mul_index
    rw [hMc, hF.card_UA2] at h1
    omega
  have : (CFSG.AGLEmbeddingD2.hsOUA.subgroupOf CFSG.AGLEmbeddingD2.hsOUA2).Normal :=
    Subgroup.normal_of_index_eq_two hMidx
  have : IsSimpleGroup
      ↥(CFSG.AGLEmbeddingD2.hsOUA.subgroupOf CFSG.AGLEmbeddingD2.hsOUA2) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hF.simple eM
  obtain ⟨e1⟩ := nonempty_oPrimeModPrimeComplement_mulEquiv (G := Equiv.Perm (Fin 100))
    (d := 7) (by norm_num) (CFSG.AGLEmbeddingD2.hsOUA.subgroupOf CFSG.AGLEmbeddingD2.hsOUA2)
    (by rw [hMc]; norm_num) (by rw [hMidx]; norm_num)
  obtain ⟨e2⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.nonempty_hsOUA_mulEquiv_catU35
  exact statedClassicalModel_psu_of_mulEquiv ((e1.trans eM).trans e2) statedClassicalModel_catU35

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbeddingD2 (hsOR0 hsON0 hsOUA2 hsOUB2 hsOW0)
open CFSG.RankThree.Native (hs100P)

theorem conclusion_of_hs
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}
    (h : ThreeNineHyp K E D X₁ 5 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .HS) : ThreeNineConclusion K D X₁ 5 d := by
  obtain ⟨e⟩ := hs
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e
  have hcK : Nat.card ↥K = 44352000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  have hO : Nat.card (Outer ↥K) ≤ 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.HS_outer_card_le_two.1
  have hO0 : 0 < Nat.card (Outer ↥K) := Nat.card_pos
  have hdp := h.d_prime
  have hout5 : ¬ 5 ∣ Nat.card (Outer ↥K) := fun h5 => by
    have := Nat.le_of_dvd hO0 h5
    omega
  have houtd : ¬ d ∣ Nat.card (Outer ↥K) := fun hd => by
    have := Nat.le_of_dvd hO0 hd
    have := hdp.two_le
    exact h.d_ne_two (by omega)
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ houtd
  have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
  have hF := CFSG.AGLEmbeddingD2.hsU35Facts
  have hR0P : hsOR0 ≤ hs100P := hF.R0_le_UA.trans (hF.UA_le_UA2.trans CFSG.AGLEmbeddingD2.hsOUA2_le)
  have hPc : Nat.card hs100P = 44352000 := CFSG.RankThree.Native.card_hs100P
  obtain ⟨θ⟩ : Nonempty (↥K ≃* ↥hs100P) := ⟨e.trans CFSG.RankThree.Native.hs100Equiv⟩
  obtain ⟨Ebar, -, hEc, -, hN⟩ := h.exists_barE hZ hout5
  obtain ⟨S, hES⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  have hNS := hN S S.isPGroup' hES
  have hSc : Nat.card ((S : Subgroup ↥K).map θ.toMonoidHom) = 5 ^ 3 := by
    rw [Subgroup.card_map_of_injective θ.injective, Sylow.card_eq_multiplicity, hcK,
      SporCent.factorization_eq_of_pow_dvd (e := 3) Nat.prime_five (by norm_num) (by norm_num)
        (by norm_num)]
  have hR₀c : Nat.card (hsOR0.subgroupOf hs100P) = 5 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR0P).toEquiv, hF.card_R0]
    norm_num
  have hSidx : ¬ 5 ∣ (((S : Subgroup ↥K).map θ.toMonoidHom).subgroupOf ⊤).index := by
    change ¬ 5 ∣ ((S : Subgroup ↥K).map θ.toMonoidHom).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h1 := ((S : Subgroup ↥K).map θ.toMonoidHom).card_mul_index
    rw [hSc, hPc] at h1
    have h2 : ((S : Subgroup ↥K).map θ.toMonoidHom).index = 354816 := by omega
    rw [h2]
    norm_num
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq (L := ⊤) le_top
    le_top (IsPGroup.of_card hSc) (IsPGroup.of_card hR₀c) hSidx (by rw [hSc, hR₀c])
  set φ : ↥K ≃* ↥hs100P := θ.trans (MulAut.conj l) with hφ
  have hSφ : (S : Subgroup ↥K).map φ.toMonoidHom = hsOR0.subgroupOf hs100P := by
    rw [← hl, Subgroup.map_map]
    rfl
  set Y : Subgroup (Equiv.Perm (Fin 100)) :=
    ((X₁.subgroupOf K).map φ.toMonoidHom).map hs100P.subtype with hYdef
  have hYc : Nat.card Y = Nat.card (X₁.subgroupOf K) := by
    rw [hYdef, Subgroup.card_map_of_injective hs100P.subtype_injective,
      Subgroup.card_map_of_injective φ.injective]
  have hYP : Y ≤ hs100P := Subgroup.map_subtype_le _
  have hNY : hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ≤ Y := by
    rintro x ⟨hxP, hxN⟩
    have hx : (⟨x, hxP⟩ : ↥hs100P) ∈
        Subgroup.normalizer ((hsOR0.subgroupOf hs100P : Subgroup ↥hs100P) : Set ↥hs100P) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hR0P]
      exact Subgroup.mem_subgroupOf.mpr hxN
    rw [← hSφ, ← Subgroup.map_equiv_normalizer_eq] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    have hkx' : φ k = ⟨x, hxP⟩ := hkx
    exact ⟨φ k, ⟨k, hNS hk, rfl⟩, by rw [hkx']; rfl⟩
  have hcases : Y = hsOUA2 ∨ Y = hsOUB2 := by
    rcases CFSG.AGLEmbeddingD2.hs100P_normalizer_overgroups Y hNY hYP with hY | hY | hY | hY
    · exfalso
      have hc : Nat.card (X₁.subgroupOf K) = 2000 := by
        rw [← hYc, hY, ← CFSG.AGLEmbeddingD2.hsON0_eq_normalizer, CFSG.AGLEmbeddingD2.card_hsON0]
      obtain ⟨hd1, -⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
      rw [hc] at hd1
      have h' : d ∣ 2 ^ 4 * 5 ^ 3 := by norm_num; exact hd1
      rcases hdp.dvd_mul.1 h' with h2 | h5
      · exact h.d_ne_two ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 (hdp.dvd_of_dvd_pow h2))
      · exact h.d_ne ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_five).1 (hdp.dvd_of_dvd_pow h5))
    · exact Or.inl hY
    · exact Or.inr hY
    · exfalso
      have hc : Nat.card (X₁.subgroupOf K) = Nat.card ↥K := by rw [← hYc, hY, hPc, hcK]
      refine h.not_K_le fun x hx => ?_
      have : (⟨x, hx⟩ : ↥K) ∈ X₁.subgroupOf K := by
        rw [Subgroup.card_eq_iff_eq_top] at hc
        rw [hc]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have hc1 : Nat.card (X₁.subgroupOf K) = 252000 := by
    rcases hcases with hY | hY
    · rw [← hYc, hY, CFSG.AGLEmbeddingD2.card_hsOUA2]
    · rw [← hYc, hY, CFSG.AGLEmbeddingD2.card_hsOUB2]
  obtain ⟨hd1, -⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
  rw [hc1] at hd1
  have hidxX : (X₁.subgroupOf K).index = 176 := by
    have h1 := (X₁.subgroupOf K).card_mul_index
    rw [hc1, hcK] at h1
    omega
  have hmod := (h.isBorelDLocal hZ hout5).index_modEq_one_of_dvd hdp
    (hd1.trans (hc1 ▸ Subgroup.card_subgroup_dvd_card (X₁.subgroupOf K)))
  rw [hidxX] at hmod
  have hd7 : d = 7 := by
    have h' : d ∣ 2 ^ 5 * (3 ^ 2 * (5 ^ 3 * 7)) := by norm_num; exact hd1
    rcases hdp.dvd_mul.1 h' with h2 | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 (hdp.dvd_of_dvd_pow h2))
        h.d_ne_two
    rcases hdp.dvd_mul.1 h' with h3 | h'
    · have h3' := (Nat.prime_dvd_prime_iff_eq hdp Nat.prime_three).1 (hdp.dvd_of_dvd_pow h3)
      subst h3'
      exact absurd hmod (by decide)
    rcases hdp.dvd_mul.1 h' with h5 | h7
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_five).1 (hdp.dvd_of_dvd_pow h5))
        h.d_ne
    · exact (Nat.prime_dvd_prime_iff_eq hdp (by norm_num)).1 h7
  subst hd7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hDc : Nat.card D = 7 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_D
    have hdvd : 7 ^ k ∣ 44352000 := hk ▸ hcK ▸ Subgroup.card_dvd_of_le hDK
    have hk1 : k ≤ 1 := by
      by_contra hk2
      exact absurd ((pow_dvd_pow 7 (by omega : 2 ≤ k)).trans hdvd) (by norm_num)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact h.D_ne_bot (Subgroup.eq_bot_of_card_eq D (by rw [hk, pow_zero]))
    rw [hk, show k = 1 by omega, pow_one]
  refine ⟨isCyclic_of_prime_card hDc, hDK, Or.inr (Or.inl ⟨rfl, rfl, ⟨e⟩, ?_⟩)⟩
  obtain ⟨e3⟩ : Nonempty (↥Y ≃* ↥hsOUA2) := by
    rcases hcases with hY | hY
    · exact ⟨MulEquiv.subgroupCongr hY⟩
    · exact ⟨(MulEquiv.subgroupCongr (hY.trans CFSG.AGLEmbeddingD2.hsOUB2_eq_map)).trans
        (hsOUA2.equivMapOfInjective _ (MulAut.conj hsOW0).injective).symm⟩
  have e1 : ↥X₁ ≃* ↥(X₁.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hX₁K).symm
  have e2 : ↥(X₁.subgroupOf K) ≃* ↥Y :=
    ((X₁.subgroupOf K).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (((X₁.subgroupOf K).map φ.toMonoidHom).equivMapOfInjective hs100P.subtype
        hs100P.subtype_injective)
  obtain ⟨e4⟩ := oPrimeModPrimeComplement_congr 7 ((e1.trans e2).trans e3)
  exact SporCent.statedClassicalModel_psu_of_mulEquiv e4 SporCent.statedClassicalModel_oPrime_hsOUA2

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
