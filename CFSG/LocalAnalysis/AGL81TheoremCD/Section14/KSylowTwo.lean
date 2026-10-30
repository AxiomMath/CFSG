module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenTwo
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Sylow
import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

@[expose] def PLayerNotLeAt (M : Subgroup G) : Prop :=
  ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H → ¬ pLayerIn q H ≤ M

@[expose] def NormalizerSylowKLeAt (M : Subgroup G) : Prop :=
  ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H →
    ∃ A : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q A (kSub q M H) ∧
      Subgroup.normalizer (A : Set G) ⊓ kSub q M H ≤ M

namespace HypCGen

variable {M : Subgroup G} {q : ℕ} {E H : Subgroup G}

theorem relPPrimeCore_le (h : HypCGen G M q E H) : relPPrimeCore q H ≤ M := by
  haveI : Fact q.Prime := ⟨h.prime⟩
  have hcard : q ^ (1 + 1) ≤ Nat.card E := by
    calc q ^ (1 + 1) = q ^ 2 := by norm_num
      _ = Nat.card E := h.card.symm
      _ ≤ Nat.card E := le_rfl
  refine CFSG.LocalAnalysis.AGL81TheoremC.relPPrimeCore_le_of_glbCore_le
    (p := q) (k := 1) (E := E) (H := H) (M := M) h.elem hcard h.E_le_H ?_
  simpa only [rankThreeGamma] using h.gamma

end HypCGen

theorem not_kSub_le_of_not_pLayerIn_le {p : ℕ} {M H : Subgroup G}
    (h : ¬ pLayerIn p H ≤ M) : ¬ kSub p M H ≤ M := by
  have hex : ∃ L : Subgroup ↥H, CFSG.IsPComponent p L ∧ ¬ L.map H.subtype ≤ M := by
    by_contra hcon
    push Not at hcon
    apply h
    unfold pLayerIn CFSG.pLayer
    rw [sSup_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hL => hcon L hL
  obtain ⟨L, hL, hLM⟩ := hex
  have hLmem : L.map H.subtype ∈ {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M} := by
    refine ⟨⟨Subgroup.map_subtype_le L, ?_⟩, hLM⟩
    have hsub : (L.map H.subtype).subgroupOf H = L :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
    rw [hsub]
    exact hL
  unfold kSub
  rw [if_neg h]
  intro hk
  exact hLM ((le_sSup hLmem).trans hk)

theorem pPrimeCore_map_le_relPPrimeCore {p : ℕ} [Fact p.Prime] {K H : Subgroup G}
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    (CFSG.pPrimeCore p ↥K).map K.subtype ≤ relPPrimeCore p H := by
  have hN : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  have hinf : (CFSG.pPrimeCore p (K.subgroupOf H)).map (K.subgroupOf H).subtype ≤
      CFSG.pPrimeCore p ↥H := by
    rw [CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := p) (H := ↥H) hN]
    exact inf_le_right
  have hHmap : (CFSG.pPrimeCore p ↥H).map H.subtype ≤ relPPrimeCore p H := by
    unfold relPPrimeCore
    refine le_sSup ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · have hsub : (((CFSG.pPrimeCore p ↥H).map H.subtype).subgroupOf H) =
          CFSG.pPrimeCore p ↥H :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      rw [hsub]
      infer_instance
    · rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
  calc (CFSG.pPrimeCore p ↥K).map K.subtype
      = ((CFSG.pPrimeCore p (K.subgroupOf H)).map
          (K.subgroupOf H).subtype).map H.subtype :=
        (CFSG.pPrimeCore_map_subgroupOf p K H hKH).symm
    _ ≤ (CFSG.pPrimeCore p ↥H).map H.subtype := Subgroup.map_mono hinf
    _ ≤ relPPrimeCore p H := hHmap


theorem kSylowTwoNotLeAt_of {M : Subgroup G} (hpre : PreambleTypes M)
    (h14 : ∀ H ∈ H2StarAll M, CaseThree M H) (hK : KNormalAt M) (hL : PLayerNotLeAt M)
    (hA : NormalizerSylowKLeAt M) : KSylowTwoNotLeAt M := by
  intro q E H hdata S hS
  have hq3 : q = 3 := eq_three_of_mem hpre hdata.mem_QSet hdata.mem
  subst q
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH2 : H ∈ H2StarAll M := ⟨3, E, hdata.mem_QSet, hdata.mem⟩
  have hC3 : CaseThree M H := h14 H hH2
  have hO : (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype ≤ M :=
    (pPrimeCore_map_le_relPPrimeCore (p := 3) (K := kSub 3 M H) (H := H)
      (kSub_le 3 M H) (hK 3 E H hdata)).trans (HypCGen.relPPrimeCore_le hdata)
  have hKM : ¬ kSub 3 M H ≤ M :=
    not_kSub_le_of_not_pLayerIn_le (p := 3) (hL 3 E H hdata)
  obtain ⟨A, hAsyl, hNA⟩ := hA 3 E H hdata
  exact IsL34Star.not_le_of_isSylowOf_two (K := kSub 3 M H) (M := M) (A := A) (S := S)
    hC3.2 hO hKM hAsyl hNA hS

theorem agl81FourteenFifteen_of_inputs
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        PreambleTypes M ∧ ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M ∧
        FourteenFifteenOneAt M ∧ FourteenFifteenNormAt M ∧ KNormalAt M ∧ PLayerNotLeAt M ∧
        NormalizerSylowKLeAt M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_parts ?_
  intro G _ _ hC M hM hσ
  obtain ⟨hpre, hch, h1, h2, h1At, hN, hK, hL, hA⟩ := h G hC M hM hσ
  have h14 := caseThree_of_cases hpre hch h1 h2
  exact ⟨h1At, hN, hK, kSylowTwoNotLeAt_of hpre h14 hK hL hA⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
