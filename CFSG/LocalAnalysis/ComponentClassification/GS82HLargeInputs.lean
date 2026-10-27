module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HLargeDatum
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP3Pump
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigCore

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def TypChev (r : ℕ) (K : Type) [Group K] : Prop :=
  HarrisLit.IsSimpleChevalleyOver r (K ⧸ Open.fusionZStar K) ∧
    ¬ GH74.GLS.InChev2 (K ⧸ Open.fusionZStar K)

theorem typChev_of_mulEquiv {r : ℕ} {A B : Type} [Group A] [Group B] (hA : TypChev r A)
    (e : A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B) : TypChev r B :=
  GS82PumpInputs.chev_of_mulEquiv hA.1 hA.2 e

theorem coreInvariant_typChev (r : ℕ) : GS82PumpInputs.CoreInvariant (TypChev r) := by
  intro A B _ _ ⟨e⟩ hA
  obtain ⟨eA⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar A
  obtain ⟨eB⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar B
  have hc : (center (A ⧸ pPrimeCore 2 A)).map e.toMonoidHom = center (B ⧸ pPrimeCore 2 B) :=
    Subgroup.map_center_eq e
  exact typChev_of_mulEquiv hA ((eA.symm.trans (QuotientGroup.congr _ _ e hc)).trans eB)

theorem diagonalTransfer_typChev (r q₀ : ℕ) : GS82PumpInputs.DiagonalTransfer q₀ (TypChev r) := by
  intro A B _ _ _ _ _ _ hA ⟨e⟩ _ _ _ _ _ _ _ _
  exact typChev_of_mulEquiv hA e

theorem verticalCentral_typChev (hP2 : GS82PumpInputs.ChevOddCentralPumpInput) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) : GS82PumpInputs.VerticalCentral (TypChev r) := by
  intro H _ _ hH M hM x hx hxM T hTM hTx hTc hT w hw hwT hwM
  exact hP2 H hH M hM x hx hxM T hTM hTx hTc r hr hr2 hT.1 hT.2 w hw hwT hwM

variable {X : Type} [Group X] [Finite X]

theorem typChev_of_gs82HConfig (hP3 : GS82PumpInputs.KGSLTwoInput) {r e : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (he : 1 ≤ e) (hq : r ^ e ∉ ({3, 5, 7, 9} : Finset ℕ)) {t : X}
    {K R T : Subgroup X} {w : X} (h : GS82HConfig (r ^ e) t K R T w)
    (hKg : SectionRank.IsKGroupCat ↥(centralizer ({t} : Set X))) : TypChev r ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hKt, hKc, hR2, hRt, hRK, hTKR, hTc, hSL, -, -, -⟩ := h
  have hTt : T ≤ centralizer ({t} : Set X) := (hTKR.trans inf_le_left).trans hKt
  have hKRt : K ⊓ centralizer (R : Set X) ≤ centralizer ({t} : Set X) := inf_le_left.trans hKt
  have hB : IsPGroup 2 (R.subgroupOf (centralizer ({t} : Set X))) :=
    hR2.of_equiv (subgroupOfEquivOfLe hRt).symm
  have hBM : R.subgroupOf (centralizer ({t} : Set X)) ≤
      normalizer ((K.subgroupOf (centralizer ({t} : Set X)) : Subgroup _) : Set _) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro x
    rw [mem_subgroupOf, mem_subgroupOf]
    have h1 := mem_normalizer_iff.mp (hRK (mem_subgroupOf.mp hb)) (x : X)
    simpa using h1
  have hMB : (K.subgroupOf (centralizer ({t} : Set X))) ⊓
      centralizer ((R.subgroupOf (centralizer ({t} : Set X)) : Subgroup _) : Set _) =
      (K ⊓ centralizer (R : Set X)).subgroupOf (centralizer ({t} : Set X)) := by
    ext x
    rw [mem_inf, mem_subgroupOf, mem_subgroupOf, mem_inf, mem_centralizer_iff,
      mem_centralizer_iff]
    constructor
    · rintro ⟨hxK, hxR⟩
      exact ⟨hxK, fun r hr => congrArg Subtype.val (hxR ⟨r, hRt hr⟩ (mem_subgroupOf.mpr hr))⟩
    · rintro ⟨hxK, hxR⟩
      exact ⟨hxK, fun r hr => Subtype.ext (hxR r (mem_subgroupOf.mp hr))⟩
  have hTM : T.subgroupOf (centralizer ({t} : Set X)) ≤ (K.subgroupOf (centralizer ({t} : Set X))) ⊓
      centralizer ((R.subgroupOf (centralizer ({t} : Set X)) : Subgroup _) : Set _) := by
    rw [hMB]
    intro x hx
    exact mem_subgroupOf.mpr (hTKR (mem_subgroupOf.mp hx))
  have hTc' : IsPComponent 2 ((T.subgroupOf (centralizer ({t} : Set X))).subgroupOf
      ((K.subgroupOf (centralizer ({t} : Set X))) ⊓
        centralizer ((R.subgroupOf (centralizer ({t} : Set X)) : Subgroup _) : Set _))) := by
    rw [hMB]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hKRt 2 Nat.prime_two).mpr hTc
  have hSL' : HarrisLit.IsSLTwoOver (r ^ e) (↥(T.subgroupOf (centralizer ({t} : Set X))) ⧸
      pPrimeCore 2 ↥(T.subgroupOf (centralizer ({t} : Set X)))) :=
    HConfig.isSLTwoOver_of_mulEquiv (subgroupOfEquivOfLe hTt).symm hSL
  have h1 := hP3 _ hKg _ hKc _ hB hBM _ hTM hTc' r e hr hr2 he hq hSL'
  obtain ⟨eK⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hKt)
  exact typChev_of_mulEquiv h1 eK

theorem gs82LargeStatement_of_inputs (hD' : GS82PumpInputs.TheoremDPrime)
    (hH1 : HarrisLit.Harris82Theorem1KProper) (hP2 : GS82PumpInputs.ChevOddCentralPumpInput)
    (hP3 : GS82PumpInputs.KGSLTwoInput) (hP4 : GS82PumpInputs.MTypeOfSLTwoSection) :
    GS82LargeStatement := by
  intro X _ _ hamb r e hr hr2 he hq t K R T w h
  obtain ⟨hsimple, hnonab, hKP, hcat, -, -⟩ := hamb
  haveI := hsimple
  have hKg : ∀ v : X, orderOf v = 2 → SectionRank.IsKGroupCat ↥(centralizer ({v} : Set X)) :=
    fun v hv => isKGroupCat_of_ne_top' hKP (Helpers.centralizer_ne_top_of_involution X hnonab v hv)
  have hTypK : TypChev r ↥K :=
    typChev_of_gs82HConfig hP3 hr hr2 he hq h (hKg t h.1)
  have hodd : Odd (r ^ e) := (hr.odd_of_ne_two hr2).pow
  have h5 : 5 ≤ r ^ e := by
    have h3 : 3 ≤ r ^ e := by
      have hr3 : 3 ≤ r := by
        have := hr.two_le
        rcases Nat.lt_or_ge r 3 with h' | h'
        · exact absurd (by omega : r = 2) hr2
        · exact h'
      exact hr3.trans (Nat.le_self_pow (by omega) r)
    have h3' : r ^ e ≠ 3 := fun h' => hq (by rw [h']; decide)
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨w', J, N', hJd, hw'J, hTypJ⟩ := hD' (TypChev r) (r ^ e) hodd h5
    (verticalCentral_typChev hP2 hr hr2) (coreInvariant_typChev r)
    (diagonalTransfer_typChev r (r ^ e)) X hKg t K _ w (isDatum_of_gs82HConfig h) hTypK
  obtain ⟨hw', hJw', hJc, hN'J, -, hN'SL, -, hw'N', -, hw'Z⟩ := hJd
  have hJ := (HarrisLit.isTwoComponentIn_iff hJw').mpr hJc
  have hSLJ : HarrisLit.IsSLTwoOver (r ^ e)
      (↥(N'.subgroupOf J) ⧸ pPrimeCore 2 ↥(N'.subgroupOf J)) :=
    HConfig.isSLTwoOver_of_mulEquiv (subgroupOfEquivOfLe hN'J).symm hN'SL
  have hcZ : (⟨w', hw'J⟩ : ↥J) ∈ Open.fusionZStar ↥J := by
    obtain ⟨k, hk, hkw⟩ := hw'Z
    have : k = ⟨w', hw'J⟩ := Subtype.ext hkw
    rwa [← this]
  have hM := hP4 ↥J hJ.2.2 r hr hr2 hTypJ.1 (N'.subgroupOf J) (r ^ e) hodd h5 hSLJ ⟨w', hw'J⟩
    (by rw [Subgroup.orderOf_mk]; exact hw') (mem_subgroupOf.mpr hw'N') hcZ
  exact HarrisLit.not_isMTypeSchur_of_kProper hH1 hnonab hKP hcat hw' hJ hw'J hr hr2 hM

end CFSG.ComponentClassification.GSThmB
