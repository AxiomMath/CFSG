module

public import CFSG.CGT.Stroth77.Sections34Assembly
public import CFSG.CGT.Stroth77.Sections34AssemblyR0
public import CFSG.CGT.Stroth77.Section43CoreE
public import CFSG.CGT.Stroth77.Section43CoreIII
public import CFSG.CGT.Stroth77.Section43CoreIV
public import CFSG.CGT.Stroth77.Section43Fus
public import CFSG.CGT.Stroth77.Section43Sc
public import CFSG.CGT.Stroth77.Section44Facts
public import CFSG.CGT.Stroth77.Section44FactsII
public import CFSG.CGT.Stroth77.Section44FactsIII
public import CFSG.CGT.Stroth77.Stroth34T201
public import CFSG.CGT.Stroth76.FrameMain
public import CFSG.CGT.Stroth77.Section1NonSplit
public import CFSG.CGT.Stroth77.Section41Exit
public import CFSG.CGT.Stroth77.Section47
public import CFSG.CGT.Stroth77.Sigma6Transport
public import CFSG.CGT.Stroth77.Stroth35to39
public import CFSG.CGT.Stroth77.StrothFrameExists
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisCore
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisE16e
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhCaseOne
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.SU43Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.Recognition.HSType17m
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Data.Y2L.Coset
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix5

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open CFSG.OddStandard.HigherRank.YamadaG23 (LitPSLU4S StrothSigma6)

section Goldschmidt

theorem stroth_4_3_he_holds :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      ∀ m e, τ = .t100 m → e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G) ^ 2 ^ (m - 1))) → False :=
  stroth_4_3_he_of_core
    (@fun _ _ _ _ _ dD _ hm _ huv ht hu hc ha hb hee =>
      ⟨dD.ii_h1 hm huv ht hu hc ha hb hee, dD.ii_h2 hm huv ht hu hc ha hb hee,
        dD.ii_h4 hm huv ht hu hc ha hb hee, (dD.iiAction huv ht hu hc ha hb hee).mul_self_mem_or,
        dD.ii_h6' hm huv ht hu hc ha hb hee, dD.ii_h7 hm huv ht hu hc ha hb hee,
        dD.ii_h8 hm huv ht hu hc ha hb hee, dD.ii_h9 hm huv ht hu hc ha hb hee⟩)
    (@fun _ _ _ _ _ dD _ hm _ huv ht hu hc ha hb hee =>
      ⟨dD.iii_h1 hm huv ht hu hc ha hb hee, dD.iii_h2 hm huv ht hu hc ha hb hee,
        dD.iii_h1' hm huv ht hu hc ha hb hee, dD.iii_h2' hm huv ht hu hc ha hb hee,
        dD.iii_h4 hm huv ht hu hc ha hb hee, (dD.iiiAction huv ht hu hc ha hb hee).mul_self_mem_or,
        dD.iii_h8 hm huv ht hu hc ha hb hee, dD.iii_h9 hm huv ht hu hc ha hb hee,
        dD.t100_iii_hC2 hm huv ht hu hc ha hb hee,
        dD.t100_iii_hC2c (by omega) huv ht hu hc ha hb hee,
        dD.t100_iii_hC4 hm huv ht hu hc ha hb hee, dD.t100_iii_hC6 hm huv ht hu hc ha hb hee,
        dD.t100_iii_hC7 hm huv ht hu hc ha hb hee, dD.t100_iii_hC10 hm huv ht hu hc ha hb hee,
        dD.t100_iii_hC11 hm hu hc ha hb hee, dD.t100_iii_hC13 (by omega),
        dD.t100_iii_hC14 (by omega), dD.t100_iii_hC15 hm huv ht hu hc ha hb hee,
        dD.t100_iii_hr2, dD.t100_iii_hrue huv hu hc ha hb hee,
        dD.t100_iii_hrta huv ht hu hc ha hb hee, dD.t100_iii_hF hm,
        dD.t100_iii_hM hm hu hc ha hb hee⟩)
    (@fun _ _ _ _ _ dD _ hm _ huv ht hu hc ha hb hee =>
      ⟨dD.iv_h1 hm huv ht hu hc ha hb hee, dD.iv_h2 hm huv ht hu hc ha hb hee,
        (dD.ivAction huv ht hu hc ha hb hee).mul_self_mem_or, dD.iv_h6' hm huv ht hu hc ha hb hee,
        dD.iv_h7 hm huv ht hu hc ha hb hee, dD.iv_h9 hm huv ht hu hc ha hb hee, dD.iv_hc₂ hm⟩)
    stroth_4_3_fusIII stroth_4_3_scIV

end Goldschmidt

theorem stroth_4_4_of_fusion
    (hfus201 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t201 m)), F.IsD D dD →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    (hR0 : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
      {dD : StrothWeakTypeData D (.t201 m)}, F.IsD D dD → 1 ≤ m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      (∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) →
      ∀ {e : G}, e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
        Rel34i dD e (2 ^ (m + 1)) →
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e)
    (ht201fusion : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t201 m)),
      1 ≤ m → F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      (∀ y ∈ Subgroup.closure
        {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t},
        y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ (m + 1))) ∧
      IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)) ∧
      IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ (m + 1))) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G) (m : ℕ)
      (dD : StrothWeakTypeData D (.t201 m)), 1 ≤ m → F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      ∃ e ∈ (F.S : Subgroup G),
        (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u, e} ∧
        e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
        e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) ∧
        e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ (m + 1) ∧
        e * e = 1 ∧ e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv ∧
        e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t ∧ e⁻¹ * dD.u * e = dD.u := by
  refine stroth_4_4_of_parts'
    (@fun _ _ _ F _ _ dD h hm hns hfus => stroth_3_4_t201 F dD h hm hns hfus)
    hfus201 hR0 ?_ ?_ ?_
  · intro G _ _ F D m dD hm h hns hmax hSN hnc h11
    obtain ⟨hE, hu, hzu⟩ := ht201fusion F dD hm h hns hmax hSN hnc h11
    exact h.false_of_t201_A hnc hE hu hzu
  · intro G _ _ F D m dD hm h hns hmax hSN hnc h11
    obtain ⟨hE, hu, hzu⟩ := ht201fusion F dD hm h hns hmax hSN hnc h11
    exact h.false_of_t201_ii hnc hE hu hzu
  · intro G _ _ F D m dD hm h hns hmax hSN hnc h11
    obtain ⟨hE, hu, hzu⟩ := ht201fusion F dD hm h hns hmax hSN hnc h11
    exact h.false_of_t201_iii' hnc hE hu hzu

end CFSG.CGT.Stroth77
