module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolRepoint

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup FooteLit CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem sup_conjugate_eq_of_fixedLayer {a b : G} {Y X B : Subgroup G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hYa : Y ≤ centralizer ({a} : Set G))
    (hYpc : IsPComponent 2 (Y.subgroupOf (centralizer ({a} : Set G))))
    (hXb : X ≤ centralizer ({b} : Set G))
    (hXpc : IsPComponent 2 (X.subgroupOf (centralizer ({b} : Set G))))
    (hBb : IsTwoComponentAt b B) (hbN : b ∈ normalizer (Y : Set G))
    (hbO : ∀ j ∈ Y, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 Y).map Y.subtype)
    (hTX : UnbalancedGS.gsFixedLayer Y b ≤ X ⊔ conjugate X a)
    (hTB : UnbalancedGS.gsFixedLayer Y b ≤ B ⊔ conjugate B a) :
    B ⊔ conjugate B a = X ⊔ conjugate X a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cb := centralizer ({b} : Set G) with hCb
  set T := UnbalancedGS.gsFixedLayer Y b with hT
  have haCb : a ∈ Cb := mem_centralizer_singleton_iff.mpr hab
  have hbCa : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hB : IsTwoComponentIn B Cb := ⟨hBb.2.1, hBb.2.2⟩
  have hBa : IsTwoComponentIn (conjugate B a) Cb :=
    ⟨UnbalancedCorr.conjugate_le_of_mem hBb.2.1 haCb,
      UnbalancedCorr.isPComponent_conjugate_subgroupOf haCb hBb.2.2⟩
  have hX : IsTwoComponentIn X Cb := ⟨hXb, hXpc⟩
  have hXa : IsTwoComponentIn (conjugate X a) Cb :=
    ⟨UnbalancedCorr.conjugate_le_of_mem hXb haCb,
      UnbalancedCorr.isPComponent_conjugate_subgroupOf haCb hXpc⟩
  have hYq := isQuasisimple_quotient_of_isPComponent hYa hYpc
  have hYsub : (Y.subgroupOf (centralizer ({a} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hYpc
    exact hs
  have hTpc := UnbalancedCorr.gsFixedLayer_isPComponent hYa hYsub hbCa hb hbN hYq hbO
  have hTle : T ≤ centralizer ({a} : Set G) ⊓ Cb :=
    le_inf ((UnbalancedGS.gsFixedLayer_le_inf Y b).trans (inf_le_left.trans hYa))
      ((UnbalancedGS.gsFixedLayer_le_inf Y b).trans inf_le_right)
  have hTperf : ⁅T, T⁆ = T := UnbalancedCorr.commutator_eq_of_isPComponent hTle hTpc
  have hTne : T ≠ ⊥ := ne_bot_of_isQuasisimple (isQuasisimple_quotient_of_isPComponent hTle hTpc)
  have hTL : T ≤ twoLayerIn Cb :=
    hTB.trans (sup_le (le_twoLayerIn_of_isTwoComponentIn hB)
      (le_twoLayerIn_of_isTwoComponentIn hBa))
  obtain ⟨V, hV, hmv⟩ : ∃ V, IsTwoComponentIn V Cb ∧ ¬ T ≤ coreActionKernel V := by
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    exact hTne (eq_bot_iff.mpr ((le_iSup_moved hTL hTperf).trans
      (iSup₂_le fun K hK => absurd (hno K hK.1) hK.2)))
  rw [← sup_conjugate_eq_of_mem_pair haa (mem_pair_of_moved hB hBa hV hTB hmv),
    sup_conjugate_eq_of_mem_pair haa (mem_pair_of_moved hX hXa hV hTX hmv)]

theorem footePointedMaximal_of_commute {z a : G} {A : Subgroup G} (hz : FootePointedMaximal z A)
    (ha : IsTwoComponentAt a A) (hza : z * a = a * z) : FootePointedMaximal a A := by
  by_cases hne : z = a
  · exact hne ▸ hz
  have haA := GSLit.mem_coreActionKernel_of_le_centralizer ha.2.1
  have hcorr : GrSLit.GSWeakCorr z A a A :=
    ⟨hz.1.1, ha.1, hza, hz.1.2.1, hz.1.2.2, ha.2.1, ha.2.2, (mem_coreActionKernel.mp haA).1,
      (mem_coreActionKernel.mp haA).2,
      (UnbalancedGS.gsFixedLayer_le_inf A a).trans (inf_le_left.trans le_sup_left)⟩
  exact hz.of_reach (FootePointedReach.single (footePointedStep_of_gsWeakCorr hcorr hne))

theorem footePointedMaximal_of_conj {z g : G} {A : Subgroup G} (hz : FootePointedMaximal z A)
    (hg : g ∈ normalizer (A : Set G)) : FootePointedMaximal (g⁻¹ * z * g) A := by
  have h := hz.conjugate g
  rwa [UnbalancedLayer.conjugate_eq_of_mem_normalizer hg] at h

end CFSG.ComponentClassification.Foote5.SolMax

