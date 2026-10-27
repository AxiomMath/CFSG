module

public import CFSG.CGT.Stroth77.Sections34AssemblyGH227P
public import CFSG.CGT.Stroth77.Section47HinvProved
public import CFSG.CGT.Stroth77.Section47CaseK
public import CFSG.CGT.Stroth77.Section47Fus
public import CFSG.CGT.Stroth77.Stroth34T200
public import CFSG.CGT.Stroth77.Sections34Assembly
public import CFSG.CGT.Stroth77.Section224FrameExports
public import CFSG.CGT.Stroth77.Section227NI
public import CFSG.CGT.Stroth77.Section226AllConj
public import CFSG.CGT.Stroth77.Section225FrameExports

public import CFSG.LocalAnalysis.GH72.AssemblyFinal
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionNormalQuaternion
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open CFSG.OddStandard.HigherRank.YamadaG23 (StrothSigma6)


theorem strothSigma6_of_h224
    (H2a : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 1 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ z ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G),
        z * z = 1 → z ∈ omegaIn 1 D)
    (H2b : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 1 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ (k : ℕ), k ≤ τ.n - 1 → ∀ (B : Subgroup G),
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
        Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) →
        B ≤ D) :
    StrothSigma6 := by
  have h226p : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D' : Subgroup G)
      (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ') (B : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n := by
    intro G _ _ F D' τ' dD' B h hns hBR hBn hne hconj
    exact h.stroth_2_26_frame_of_contracts H2b
      (fun h' hfam hm hns' k hk B' hBR' hB' =>
        h'.stroth_2_25_frame_two hfam hm hns' k hk B' hBR' hB')
      (fun h' hfam hm hns' hne' =>
        h'.stroth_2_25_frame_three hfam hm hns' hne')
      hns hBR hBn hne hconj
  have h227p : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n := by
    intro G _ _ F D τ dD h hns hall
    exact h227plus_of_h226_of_ni h226p
      (ni_of_h224a_of_h225_of_hC5 H2a
        (fun h' hfam hm hns' => h'.mem_omegaIn_one_of_familyTwo hfam hm hns')
        (fun F D τ dD h hτ hns x hx =>
          h.conj_eq_of_mem_centralizer_A_of_t2m1 hτ hns hx))
      F D τ dD h hns hall
  exact strothSigma6_of_sections_v3_r0_h32_h228_hcharB_g_h227p h226p h227p
      (stroth_4_7R_of_hinv stroth_4_7_hinv) CFSG.GH72.hMason_holds

theorem strothSigma6_holds : StrothSigma6 :=
  strothSigma6_of_h224
    (fun h hmn hm hns => h.stroth_2_24_frame_a hmn hm hns)
    (fun h hmn hm hns k hk B hBR hB => h.stroth_2_24_frame_b hmn hm hns k hk B hBR hB)

end CFSG.CGT.Stroth77
