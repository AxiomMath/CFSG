module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHeNCenC
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHeNCompV
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURDiagInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RCenterTrivial

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Certified


namespace HeNT

variable {X : Type} [Group X] [Finite X]

theorem false_of_diagonal (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hIC : L34InvolutionCentralizerFact) (hD : L34RankTwoCentralFixedInput) {L : Subgroup X}
    (hset : HeldEndSetting X L) {a u : X} {M : Subgroup X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) {c w : X}
    (hc2 : orderOf c = 2) (hw2 : orderOf w = 2) (hcw : c * w = w * c)
    (hMc : M ≤ centralizer ({c} : Set X)) {N : Subgroup X} (hNw : N ≤ centralizer ({w} : Set X))
    (hNp : IsPComponent 2 (N.subgroupOf (centralizer ({w} : Set X))))
    (hNc : conjugate N c ≠ N) (hNfix : gsFixedLayer (N ⊔ conjugate N c) c = M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hsimp, hnab, hK, -⟩, -⟩ := id hset
  have hcc : c * c = 1 := by rw [← pow_two, ← hc2, pow_orderOf_eq_one]
  set N₂ := conjugate N c with hN₂
  have hcC : c ∈ centralizer ({w} : Set X) := mem_centralizer_singleton_iff.mpr hcw
  obtain ⟨hN₂w, -⟩ := UGSChain.conjugate_isPComponent_centralizer hcw hNw hNp
  have hON := oddCore_central_of_swap hS hUO hheld hIC hset ha hLa hLc hu hMu hMp hne hfix hc
    hw2 hc2 hcw hNw hNp hNc hNfix
  have hNcomp : IsComponent (N.subgroupOf (centralizer ({w} : Set X))) :=
    HeUC.isComponent_of_central hNw hNp hON
  have hN₂c : IsComponent (N₂.subgroupOf (centralizer ({w} : Set X))) :=
    HeKP.isComponent_conjugate hNcomp hcC
  have hNN₂ := HeKP.commute_of_components hNw hN₂w hNcomp hN₂c (Ne.symm hNc)
  have hNq : IsQuasisimple ↥N :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hNw) hNcomp.1
  have hcN : ∀ y ∈ N, c * y * c⁻¹ ∈ N₂ := fun y hy => by
    rw [hN₂, HeKP.mem_conjugate,
      show c * (c * y * c⁻¹) * c⁻¹ = (c * c) * y * (c * c)⁻¹ by group, hcc]
    simpa using hy
  have hcN₂ : ∀ y ∈ N₂, c * y * c⁻¹ ∈ N := fun y hy => HeKP.mem_conjugate.mp hy
  obtain ⟨-, v, hvZ', -, -, hv2', -, hv1, -, -, -⟩ :=
    HeKMC.type_and_pair hset ha hLa hLc hu hMu hMp hne hfix hc
  obtain ⟨-, -, -, hMq, -⟩ := diag_data ha hLa hu hMu hMp hne hfix hc
  have hOM : pPrimeCore 2 ↥M ≤ center ↥M := fun y hy => mem_center_iff.mpr fun g =>
    Subtype.ext (hc _ (mem_map_of_mem _ hy) g g.2).symm
  have hZM : Open.fusionZStar ↥M = center ↥M :=
    GrS5.fusionZStar_eq_center_of_le hMq.1.commutator_eq_top hOM
  have hvM : v ∈ M := map_subtype_le _ hvZ'
  have hvZ : ∀ m ∈ M, v * m = m * v := by
    rw [hZM] at hvZ'
    obtain ⟨y, hy, rfl⟩ := hvZ'
    intro m hm
    exact (congrArg Subtype.val (mem_center_iff.mp hy ⟨m, hm⟩)).symm
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2') hv1
  obtain ⟨hMv, hMvp⟩ := isPComponent_of_center hS hUO hheld hD hset ha hLa hLc hu hMu hMp hne
    hfix hc hv2 hvM hvZ
  have hMvc : IsComponent (M.subgroupOf (centralizer ({v} : Set X))) :=
    HeUC.isComponent_of_central hMv hMvp hc
  have hMne : gsFixedLayer (N ⊔ N₂) c ≠ ⊥ := by
    rw [hNfix]
    intro h
    rw [h, mem_bot] at hvM
    exact hv1 hvM
  have hMδ : M = (HeDQ.delta hNN₂ hcN).range :=
    hNfix.symm.trans (HeDG.gsFixedLayer_eq_range hcc hNN₂ hcN hcN₂ hNq hMne)
  have hvN : N ≤ centralizer ({v} : Set X) := by
    have hvδ : v ∈ (HeDQ.delta hNN₂ hcN).range := hMδ ▸ hvM
    obtain ⟨n₀, hn₀⟩ := hvδ
    have hn₀Z : n₀ ∈ center ↥N := by
      apply HeDG.mem_center_of_delta hNN₂ hcN hNq
      intro y
      rw [hn₀]
      have hyM : HeDQ.delta hNN₂ hcN y ∈ M := by
        rw [hMδ]
        exact ⟨y, rfl⟩
      exact hvZ _ hyM
    intro n hn
    rw [mem_centralizer_singleton_iff, ← hn₀, HeDQ.delta_apply]
    have h1 : n * (n₀ : X) = n₀ * n := congrArg Subtype.val (mem_center_iff.mp hn₀Z ⟨n, hn⟩)
    have h2 : n * (c * n₀ * c⁻¹) = (c * n₀ * c⁻¹) * n := hNN₂ n hn _ (hcN n₀ n₀.2)
    calc n * ((n₀ : X) * (c * n₀ * c⁻¹)) = (n * n₀) * (c * n₀ * c⁻¹) := (mul_assoc _ _ _).symm
      _ = (n₀ * n) * (c * n₀ * c⁻¹) := by rw [h1]
      _ = n₀ * (n * (c * n₀ * c⁻¹)) := mul_assoc _ _ _
      _ = n₀ * ((c * n₀ * c⁻¹) * n) := by rw [h2]
      _ = (n₀ : X) * (c * n₀ * c⁻¹) * n := (mul_assoc _ _ _).symm
  have hvtop := HeKC.centralizer_ne_top hsimp hnab hv1
  have hMw : M ≤ centralizer ({w} : Set X) := by
    rw [← hNfix]
    exact (gsFixedLayer_le_inf _ c).trans (inf_le_left.trans (sup_le hNw hN₂w))
  have hwv : w * v = v * w := (mem_centralizer_singleton_iff.mp (hMw hvM)).symm
  have hNwv : N ≤ centralizer ({w} : Set X) ⊓ centralizer ({v} : Set X) := le_inf hNw hvN
  obtain ⟨R, hRv, hRp, hNR, -⟩ := HeK.exists_pump hS hK hw2 hwv hvtop hNwv
    (UnbalancedCorr.isPComponent_subgroupOf_of_le hNwv inf_le_left hNp)
  have hMwc : conjugate M w = M := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hMw
  by_cases hRM : R = M
  ·
    rw [hRM, hMwc, sup_idem] at hNR
    exact hNc (UnbalancedCorr.conjugate_eq_self_of_le_centralizer
      ((hNR.trans inf_le_left).trans hMc))
  have hwCv : w ∈ centralizer ({v} : Set X) := mem_centralizer_singleton_iff.mpr hwv
  have hRwv : conjugate R w ≤ centralizer ({v} : Set X) :=
    UnbalancedCorr.conjugate_le_of_mem hRv hwCv
  have hRwp : IsPComponent 2 ((conjugate R w).subgroupOf (centralizer ({v} : Set X))) :=
    UnbalancedCorr.isPComponent_conjugate_subgroupOf hwCv hRp
  have hRwM : conjugate R w ≠ M := by
    intro h
    apply hRM
    apply UnbalancedLayer.conjugate_injective (g := w)
    rw [h, hMwc]
  have hRC : R ≤ centralizer (M : Set X) := fun r hr => mem_centralizer_iff.mpr fun m hm =>
    commute_of_isComponent hMv hRv hMvc hMvp hRp (Ne.symm hRM) m hm r hr
  have hRwC : conjugate R w ≤ centralizer (M : Set X) := fun r hr =>
    mem_centralizer_iff.mpr fun m hm =>
      commute_of_isComponent hMv hRwv hMvc hMvp hRwp (Ne.symm hRwM) m hm r hr
  have hNC : N ≤ centralizer (M : Set X) := (hNR.trans inf_le_left).trans (sup_le hRC hRwC)
  have hNab : ⁅N, N⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr fun n₁ hn₁ =>
    mem_centralizer_iff.mpr fun n₂ hn₂ => by
      have hδ : HeDQ.delta hNN₂ hcN ⟨n₂, hn₂⟩ ∈ M := by
        rw [hMδ]
        exact ⟨_, rfl⟩
      have h1 := mem_centralizer_iff.mp (hNC hn₁) _ hδ
      rw [HeDQ.delta_apply] at h1
      change n₂ * (c * n₂ * c⁻¹) * n₁ = n₁ * (n₂ * (c * n₂ * c⁻¹)) at h1
      have h2 : n₁ * (c * n₂ * c⁻¹) = (c * n₂ * c⁻¹) * n₁ := hNN₂ n₁ hn₁ _ (hcN n₂ hn₂)
      refine mul_right_cancel (b := c * n₂ * c⁻¹) ?_
      calc n₂ * n₁ * (c * n₂ * c⁻¹) = n₂ * (n₁ * (c * n₂ * c⁻¹)) := mul_assoc _ _ _
        _ = n₂ * ((c * n₂ * c⁻¹) * n₁) := by rw [h2]
        _ = n₂ * (c * n₂ * c⁻¹) * n₁ := (mul_assoc _ _ _).symm
        _ = n₁ * (n₂ * (c * n₂ * c⁻¹)) := h1
        _ = n₁ * n₂ * (c * n₂ * c⁻¹) := (mul_assoc _ _ _).symm
  have hNperf : ⁅N, N⁆ = N := GSThmB.commutator_eq_self_of_isPComponent hNw hNp
  have hNbot : N = ⊥ := hNperf.symm.trans hNab
  apply hNc
  rw [hN₂, hNbot]
  exact UnbalancedCorr.conjugate_eq_self_of_le_centralizer
    (bot_le : (⊥ : Subgroup X) ≤ centralizer ({c} : Set X))

end HeNT

theorem heldKDiagonalPumpUpDiagonalResidue_of_involutionFact (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hIC : L34InvolutionCentralizerFact) (hDC : L34ProperFixedCenterTrivial) :
    HeldKDiagonalPumpUpDiagonalResidue := by
  intro X _ _ L hset a u M ha hLa hLp hu hMu hMp hne hfix hc c w hc2 hw2 hcw _ hMc _ N hNw hNp
    _ _ hNc hNfix
  exact HeNT.false_of_diagonal hS hUO hheld hIC (l34RankTwoCentralFixedInput_of_centerTrivial hDC)
    hset ha hLa hLp hu hMu hMp hne hfix hc hc2 hw2 hcw hMc hNw hNp hNc hNfix

end Certified

end CFSG.ComponentClassification.GrSLit
