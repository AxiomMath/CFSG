module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolIdent
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolPsp4
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSolomonFamily
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalance
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddFixedNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitWeakMaximal

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup FooteLit CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem mem_pair_of_moved {H T K V : Subgroup G} {a : G} (hK : IsTwoComponentIn K H)
    (hKa : IsTwoComponentIn (conjugate K a) H) (hV : IsTwoComponentIn V H)
    (hTK : T ≤ K ⊔ conjugate K a) (hmv : ¬ T ≤ coreActionKernel V) :
    V = K ∨ V = conjugate K a := by
  by_contra hne
  obtain ⟨h1, h2⟩ := not_or.mp hne
  exact hmv (hTK.trans (sup_le (le_coreActionKernel_of_ne hV hK h1)
    (le_coreActionKernel_of_ne hV hKa h2)))

omit [Finite G] in
theorem sup_conjugate_eq_of_mem_pair {K V : Subgroup G} {a : G} (ha : a * a = 1)
    (h : V = K ∨ V = conjugate K a) : V ⊔ conjugate V a = K ⊔ conjugate K a := by
  rcases h with rfl | rfl
  · rfl
  · rw [UnbalancedLayer.conjugate_conjugate_self_of_mul_self ha, sup_comm]

theorem gsFixedLayer_common_component_of_gsWeakCorr {a b : G} {Y X : Subgroup G}
    (h : GSWeakCorr a Y b X) :
    IsTwoComponentIn (gsFixedLayer Y b)
      (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨ha, hb, hab, hYa, hYp, hXb, hXp, hbN, hcomm, _hTK⟩ := h
  have hYsub : (Y.subgroupOf (Subgroup.centralizer ({a} : Set G))).IsSubnormal :=
    hYp.choose_spec.2.1
  have hYq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y) :=
    isQuasisimple_quotient_of_isPComponent hYa hYp
  have hbCa : b ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hab.symm
  have hpc := UnbalancedCorr.gsFixedLayer_isPComponent (X := Subgroup.centralizer ({a} : Set G))
    hYa hYsub hbCa hb hbN hYq hcomm
  refine ⟨?_, ?_⟩
  · exact (gsFixedLayer_le_inf Y b).trans (le_inf (inf_le_left.trans hYa) inf_le_right)
  · exact hpc

theorem footePointedStep_of_gsWeakCorr {a b : G} {Y X : Subgroup G}
    (h : GrSLit.GSWeakCorr a Y b X) (hne : a ≠ b) : FootePointedStep a Y b X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ha, hb, hab, hYa, hYpc, hXb, hXpc, hbN, hbO, hTX⟩ := h
  have hbY : b ∈ coreActionKernel Y := mem_coreActionKernel.mpr ⟨hbN, hbO⟩
  obtain ⟨B, hBb, -, hTB, hcl, -⟩ :=
    exists_footeStep footeLBalanceInput_holds ⟨ha, hYa, hYpc⟩ hb hab hne hbY
  refine ⟨⟨ha, hYa, hYpc⟩, ⟨hb, hXb, hXpc⟩, hab, hne, hbY, hcl.trans ?_⟩
  set Cb := centralizer ({b} : Set G) with hCb
  set T := UnbalancedGS.gsFixedLayer Y b with hT
  have haCb : a ∈ Cb := mem_centralizer_singleton_iff.mpr hab
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hB : IsTwoComponentIn B Cb := ⟨hBb.2.1, hBb.2.2⟩
  have hBa : IsTwoComponentIn (conjugate B a) Cb :=
    ⟨UnbalancedCorr.conjugate_le_of_mem hBb.2.1 haCb,
      UnbalancedCorr.isPComponent_conjugate_subgroupOf haCb hBb.2.2⟩
  have hX : IsTwoComponentIn X Cb := ⟨hXb, hXpc⟩
  have hXa : IsTwoComponentIn (conjugate X a) Cb :=
    ⟨UnbalancedCorr.conjugate_le_of_mem hXb haCb,
      UnbalancedCorr.isPComponent_conjugate_subgroupOf haCb hXpc⟩
  have hTcommon := gsFixedLayer_common_component_of_gsWeakCorr
    ⟨ha, hb, hab, hYa, hYpc, hXb, hXpc, hbN, hbO, hTX⟩
  have hTle : T ≤ centralizer ({a} : Set G) ⊓ Cb := hTcommon.1
  have hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ Cb)) :=
    hTcommon.2
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

end CFSG.ComponentClassification.Foote5.SolMax
