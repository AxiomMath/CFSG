module

public import CFSG.GH74.Uniqueness.SU.SU10Stmts
public import CFSG.GH74.Uniqueness.SU.SU10Bar
public import CFSG.GH74.Uniqueness.SU.SU10Prod
public import CFSG.GH74.Uniqueness.SU.SU0GH
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.SU.SU4Stmts
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.JRAssembly
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8 CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section Hyp21Basic

variable {S : Sylow 2 G} {M : Subgroup G} {z : G}

theorem Hyp21.z_mem (h : Hyp21 S M z) : z ∈ (S : Subgroup G) := by
  have hz1 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.z_invol, sq] at this
  have hz2 : IsPGroup 2 (zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, h.z_invol]
    simp
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz1
  have hc : ∀ y ∈ (S : Subgroup G), z * y * z⁻¹ = y := fun y hy => by
    have := h.z_center y hy
    rw [← this, mul_inv_cancel_right]
  have hzN : z ∈ normalizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hc x hx]
      exact hx
    · intro hx
      have h3 := hc _ hx
      have h4 : z * (z * x * z⁻¹) * z⁻¹ = x := by
        rw [hzi]
        calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
          _ = x := by rw [hz1]; group
      rw [h4] at h3
      rw [h3]
      exact hx
  have hmem : z ∈ zpowers z ⊓ normalizer ((S : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers z, hzN⟩
  have key : zpowers z ⊓ normalizer ((S : Subgroup G) : Set G) = zpowers z ⊓ (S : Subgroup G) :=
    hz2.inf_normalizer_sylow S
  rw [key] at hmem
  exact (Subgroup.mem_inf.mp hmem).2

theorem Hyp21.z_ne_one (h : Hyp21 S M z) : z ≠ 1 := by
  intro h1
  have := h.z_invol
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem Hyp21.S_le_centralizer (h : Hyp21 S M z) :
    (S : Subgroup G) ≤ centralizer ({z} : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h.z_center s hs

theorem Hyp21.centralizer_ne_top (h : Hyp21 S M z) : centralizer ({z} : Set G) ≠ ⊤ := by
  intro htop
  have hz : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({z} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  have := h.simple
  rw [CFSG.TwoRankLowerBound.Helpers.center_eq_bot_of_nonabelian_simple G h.nonab,
    Subgroup.mem_bot] at hz
  exact h.z_ne_one hz

theorem Hyp21.isSylowIn (h : Hyp21 S M z) :
    IsSylowIn (centralizer ({z} : Set G)) (S : Subgroup G) := by
  refine ⟨h.S_le_centralizer, S.isPGroup', ?_⟩
  have hdvd : (S : Subgroup G).relIndex (centralizer ({z} : Set G)) ∣ (S : Subgroup G).index :=
    Subgroup.relIndex_dvd_index_of_le h.S_le_centralizer
  exact Nat.not_even_iff_odd.mp fun hev =>
    S.not_dvd_index (dvd_trans (even_iff_two_dvd.mp hev) hdvd)

end Hyp21Basic

section Bar

variable {Hh P M : Subgroup G}

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 Hh)

theorem coe_sylowMap_sylowIn (hP : IsSylowIn Hh P) :
    (sylowMap (sylowIn hP) : Subgroup (Hbar Hh)) = hbarImage Hh P := by
  rw [coe_sylowMap]
  rfl

omit [Finite G] in
theorem isPGroup_subgroupOf (hP : IsSylowIn Hh P) : IsPGroup 2 (P.subgroupOf Hh) :=
  hP.2.1.comap_subtype

theorem pRank_subgroupOf_eq (hPH : P ≤ Hh) :
    Open.pRank 2 (P.subgroupOf Hh) = Open.pRank 2 P := by
  have hinj : Set.InjOn Hh.subtype (P.subgroupOf Hh) := fun x _ y _ hxy => Subtype.ext hxy
  have := pRank_map_of_injOn hinj
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPH] at this
  exact this.symm

theorem oddCore_le_of_sylow (hP : IsSylowIn Hh P) (hrank : 3 ≤ Open.pRank 2 P)
    (h21A : ∀ Q : Subgroup G, Q ≤ P → 2 ≤ Open.pRank 2 Q → normalizer (Q : Set G) ⊓ Hh ≤ M) :
    (pPrimeCore 2 ↥Hh).map Hh.subtype ≤ M := by
  set D : Subgroup G := (pPrimeCore 2 ↥Hh).map Hh.subtype with hDdef
  have hDH : D ≤ Hh := Subgroup.map_subtype_le _
  have hHN : Hh ≤ normalizer (D : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨(⟨g, hg⟩ : ↥Hh) * d * (⟨g, hg⟩ : ↥Hh)⁻¹,
        (inferInstance : (pPrimeCore 2 ↥Hh).Normal).conj_mem d hd ⟨g, hg⟩, rfl⟩
    · rintro hx
      have hxH : x ∈ Hh := by
        have : g * x * g⁻¹ ∈ Hh := hDH hx
        have h2 : g⁻¹ * (g * x * g⁻¹) * g ∈ Hh := Hh.mul_mem (Hh.mul_mem (Hh.inv_mem hg) this) hg
        have h3 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [h3] at h2
        exact h2
      obtain ⟨d, hd, hdx⟩ := hx
      have hconj : (⟨g, hg⟩ : ↥Hh)⁻¹ * d * (⟨g, hg⟩ : ↥Hh) ∈ pPrimeCore 2 ↥Hh := by
        have := (inferInstance : (pPrimeCore 2 ↥Hh).Normal).conj_mem d hd (⟨g, hg⟩ : ↥Hh)⁻¹
        simpa using this
      refine ⟨(⟨g, hg⟩ : ↥Hh)⁻¹ * d * (⟨g, hg⟩ : ↥Hh), hconj, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hdx ⊢
      calc (g : G)⁻¹ * (d : G) * g = g⁻¹ * (g * x * g⁻¹) * g := by rw [hdx]
        _ = x := by group
  obtain ⟨E, hEP, hE, hEcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two hrank
  have hEH : E ≤ Hh := hEP.trans hP.1
  have hAD : E ≤ normalizer (D : Set G) := hEH.trans hHN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEcomm := hE.1
  have hEel : IsElementaryAbelian 2 E :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hE.2 x x.2) }
  have hEnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hEcard]; norm_num)
  let _ : MulDistribMulAction E D := Subgroup.conjMulDistribMulActionOfLeNormalizer E D hAD
  have hDcard : Nat.card D = Nat.card (pPrimeCore 2 ↥Hh) :=
    Subgroup.card_map_of_injective Hh.subtype_injective
  have hpD : ¬ 2 ∣ Nat.card D := by
    rw [hDcard]
    exact Nat.prime_two.coprime_iff_not_dvd.mp coprime_card_pPrimeCore
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := E) (H := D) hpD
  have hle : ⨆ (B : Subgroup E) (_ : B.index = 2), CFSG.fixedPointSubgroup B D ≤
      M.comap D.subtype := by
    refine iSup₂_le fun B hB => ?_
    have hBcard : Nat.card B = 4 := by
      have := B.card_mul_index
      rw [hB, hEcard] at this
      omega
    set R : Subgroup G := B.map E.subtype with hRdef
    have hRE : R ≤ E := Subgroup.map_subtype_le B
    have hRel : Open.IsElemAbelian 2 R := SU1.IsElemAbelian.mono hRE hE
    have hRcard : Nat.card R = 2 ^ 2 := by
      rw [hRdef, Subgroup.card_map_of_injective E.subtype_injective, hBcard]
      norm_num
    have hR2 : 2 ≤ Open.pRank 2 R := SU1.le_pRank (by norm_num) le_rfl hRel hRcard
    intro x hx
    have hcen : (x : G) ∈ centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hbx := congrArg Subtype.val (hx ⟨b, hb⟩)
      change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hbx
      calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
        _ = (x : G) * (b : G) := by rw [hbx]
    exact h21A R (hRE.trans hEP) hR2 ⟨CFSG.centralizer_le_normalizer R hcen, hDH x.2⟩
  intro d hd
  have hd' : (⟨d, hd⟩ : D) ∈ (⊤ : Subgroup D) := Subgroup.mem_top _
  rw [← hgen] at hd'
  exact hle hd'


theorem three_le_twoRank_hbar (hP : IsSylowIn Hh P) (hrank : 3 ≤ Open.pRank 2 P) :
    3 ≤ Open.twoRank (Hbar Hh) := by
  have h1 : Open.pRank 2 (P.subgroupOf Hh) = Open.pRank 2 P := pRank_subgroupOf_eq hP.1
  have h2 : Open.pRank 2 ((P.subgroupOf Hh).map π) = Open.pRank 2 (P.subgroupOf Hh) :=
    pRank_map_pPrimeCore (isPGroup_subgroupOf hP)
  have h3 : Open.pRank 2 ((P.subgroupOf Hh).map π) ≤ Open.pRank 2 (⊤ : Subgroup (Hbar Hh)) :=
    SU1.pRank_mono (by norm_num) le_top
  unfold Open.twoRank
  omega

theorem center_hbar_ne_bot {w : G} (hw : orderOf w = 2) (hwH : w ∈ Hh)
    (hwc : ∀ x ∈ Hh, x * w = w * x) : center (Hbar Hh) ≠ ⊥ := by
  intro hbot
  have hmem : π ⟨w, hwH⟩ ∈ center (Hbar Hh) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥Hh) q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hwc x.1 x.2)
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  have h2 : orderOf (⟨w, hwH⟩ : ↥Hh) = 2 := (Subgroup.orderOf_coe (⟨w, hwH⟩ : ↥Hh)).symm.trans hw
  have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥Hh) hmem
  rw [h2] at hdvd
  exact (Nat.prime_two.coprime_iff_not_dvd.mp coprime_card_pPrimeCore) hdvd

omit [Finite G] in
theorem hbarImage_ne_top (hD : (pPrimeCore 2 ↥Hh).map Hh.subtype ≤ M) (hHM : ¬ Hh ≤ M) :
    hbarImage Hh M ≠ ⊤ := by
  intro htop
  apply hHM
  have hker : (π).ker ≤ M.subgroupOf Hh := by
    rw [QuotientGroup.ker_mk']
    intro o ho
    exact hD ⟨o, ho, rfl⟩
  have e := Subgroup.comap_map_eq π (M.subgroupOf Hh)
  rw [show (M.subgroupOf Hh).map π = ⊤ from htop, Subgroup.comap_top,
    sup_eq_left.mpr hker] at e
  intro g hg
  have : (⟨g, hg⟩ : ↥Hh) ∈ M.subgroupOf Hh := e.symm ▸ Subgroup.mem_top _
  exact this

theorem gamma_le_hbarImage (hP : IsSylowIn Hh P)
    (h21A : ∀ Q : Subgroup G, Q ≤ P → 2 ≤ Open.pRank 2 Q → normalizer (Q : Set G) ⊓ Hh ≤ M) :
    Open.properTwoGenCoreGamma (sylowMap (sylowIn hP) : Subgroup (Hbar Hh)) 2 ≤
      hbarImage Hh M := by
  unfold Open.properTwoGenCoreGamma
  refine iSup₂_le fun Q' hQ' => iSup_le fun hr => ?_
  rw [coe_sylowMap_sylowIn] at hQ'
  have hP'p : IsPGroup 2 (P.subgroupOf Hh) := isPGroup_subgroupOf hP
  have hQ''map : (P.subgroupOf Hh ⊓ Q'.comap π).map π = Q' := map_inf_comap_eq hQ'
  have hQ''p : IsPGroup 2 ↥(P.subgroupOf Hh ⊓ Q'.comap π) := hP'p.to_le inf_le_left
  have hrk : 2 ≤ Open.pRank 2 (P.subgroupOf Hh ⊓ Q'.comap π) := by
    rw [← pRank_map_pPrimeCore hQ''p, hQ''map]
    exact hr
  rw [← hQ''map, normalizer_map_eq hQ''p]
  rintro _ ⟨n, hn, rfl⟩
  have hinj : Set.InjOn Hh.subtype (P.subgroupOf Hh ⊓ Q'.comap π) :=
    fun x _ y _ hxy => Subtype.ext hxy
  have hRP : (P.subgroupOf Hh ⊓ Q'.comap π).map Hh.subtype ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hRrk : 2 ≤ Open.pRank 2 ((P.subgroupOf Hh ⊓ Q'.comap π).map Hh.subtype) := by
    rw [pRank_map_of_injOn hinj]
    exact hrk
  have hnR : (n : G) ∈ normalizer (((P.subgroupOf Hh ⊓ Q'.comap π).map Hh.subtype : Subgroup G) :
      Set G) :=
    Subgroup.le_normalizer_map Hh.subtype ⟨n, hn, rfl⟩
  have hnM : (n : G) ∈ M := h21A _ hRP hRrk ⟨hnR, n.2⟩
  exact ⟨n, hnM, rfl⟩

end Bar

section Ki6

variable {Hh P M : Subgroup G}

@[expose] def Ki6Concl (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (H₀ : Subgroup H) :
    Prop :=
  ∃ K₁ : Subgroup H, IsComponent K₁ ∧ ¬ K₁ ≤ H₀ ∧
    Open.pRank 2 (centralizer (K₁ : Set H)) = 1 ∧
    (((K₁.Normal ∧ (K.IsSL25 ↥K₁ ∨ CFSG.BenderSuzuki.IsBenderGroup ↥K₁) ∧
        centralizer (K₁ : Set H) ≤ H₀ ∧
        Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤
          K₁ ⊔ centralizer (K₁ : Set H)) ∨
      (K.IsSL25 ↥K₁ ∧ ∃ K₂ : Subgroup H, IsComponent K₂ ∧ K₂ ≠ K₁ ∧ K.IsSL25 ↥K₂ ∧
        generalizedFitting H = K₁ ⊔ K₂ ∧
        Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤ generalizedFitting H) ∨
      (K₁ = ⊤ ∧ K.IsTwoAlt ↥K₁ 9 ∧ K.IsTwoAlt ↥H₀ 8) ∨
      (K.IsTwoSz8 ↥K₁ ∧ K₁ ⊔ centralizer (K₁ : Set H) = ⊤ ∧
        Subgroup.closure {g : H | g ∈ (T : Subgroup H) ∧ g * g = 1} ≤ K₁)) ∧
      (CFSG.BenderSuzuki.IsBenderGroup ↥K₁ ∨ IsCyclic ↥(center ↥(T : Subgroup H))))

theorem ki6_concl (hKI6 : K.KI6) (hKGH : KGH G) (hHne : Hh ≠ ⊤) (hP : IsSylowIn Hh P)
    (hrank : 3 ≤ Open.pRank 2 P) {w : G} (hw : orderOf w = 2) (hwH : w ∈ Hh)
    (hwc : ∀ x ∈ Hh, x * w = w * x)
    (h21A : ∀ Q : Subgroup G, Q ≤ P → 2 ≤ Open.pRank 2 Q → normalizer (Q : Set G) ⊓ Hh ≤ M)
    (hHM : ¬ Hh ≤ M) :
    (pPrimeCore 2 ↥Hh).map Hh.subtype ≤ M ∧
      Ki6Concl (Hbar Hh) (sylowMap (sylowIn hP)) (hbarImage Hh M) := by
  have hD := oddCore_le_of_sylow hP hrank h21A
  refine ⟨hD, ?_⟩
  have hGH : SU0.GHGroup (Hbar Hh) := SU0.GHGroup.of_kgh_quotient hKGH hHne (pPrimeCore 2 ↥Hh)
  have hO : pPrimeCore 2 (Hbar Hh) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  exact hKI6 (Hbar Hh) hGH hO (three_le_twoRank_hbar hP hrank) (center_hbar_ne_bot hw hwH hwc)
    (sylowMap (sylowIn hP)) (hbarImage Hh M) (gamma_le_hbarImage hP h21A)
    (hbarImage_ne_top hD hHM)

end Ki6

end CFSG.GH74.Uniqueness.SU.SU10
