module

public import CFSG.HardMathSupport.Solomon.Coordinator.Prop42
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.Open.StatedDefs
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Fischer.Classification.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.CaseSplit
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

namespace CaseThreeNs

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

abbrev Cb {G : Type*} [Group G] (b : G) : Subgroup G := Subgroup.centralizer ({b} : Set G)

@[expose] def fixSub {K : Type*} [Group K] (φ : MulAut K) : Subgroup K where
  carrier := {x | φ x = x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [map_inv, ha]

@[expose] def IsDFourTwo (X : Type) [Group X] : Prop := StatedClassicalModel X .POmegaPlus 4 2 1

@[expose] noncomputable def weakCoreIn {G : Type*} [Group G] [Finite G] (p : ℕ) (P K : Subgroup G) :
    Subgroup G :=
  ⨆ (Q : Subgroup G) (_ : Q ≤ P ∧ 2 ≤ CFSG.Open.pRank p Q ∧
      3 ≤ CFSG.Open.pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G)))), K ⊓ Subgroup.normalizer (Q : Set G)

@[expose] def IsMT {G : Type*} [Group G] [Finite G] (b : G) (L : Subgroup G) : Prop :=
  GLAPComponent 5 (Cb b) L ∧ IsFiTwentyTwo (barOf 5 L)

@[expose] def HasM {G : Type*} [Group G] (M : Subgroup G) (b : G) (M' : Subgroup G) : Prop :=
  (∃ g : G, M' = GLBConj g M) ∧ Cb b ≤ M'

@[expose] def Input10_21 : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), GLAPLayer 5 K = K →
      IsFiTwentyTwo (barOf 5 K) → 5 ≤ CFSG.Open.pRank 3 K) ∧
  (∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), GLAPLayer 5 K = K →
      IsDFourTwo (barOf 5 K) → 4 ≤ CFSG.Open.pRank 3 K)

@[expose] def Input24_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), CFSG.Open.IsKGroup ↥K →
    GLAPLayer 5 K = K → IsFiTwentyTwo (barOf 5 K) → P ≤ K → IsPGroup 3 P →
    Nat.card P = 3 ^ (Nat.card K).factorization 3 → K ≤ weakCoreIn 3 P K

@[expose] def Input24_2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsFiTwentyTwo K → ∀ A : Subgroup (MulAut K),
    IsElemAbelian 5 A → Nat.card A = 5 ^ 2 →
      ∃ Y : Subgroup K, Y ≤ (⨆ φ ∈ A, ⨆ (_ : φ ≠ 1), fixSub φ) ∧ IsDFourTwo Y

@[expose] def InputUniq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p → 3 ∈ GLABeta (m + 1) G →
    ∀ P : Sylow 3 G, ∀ M : Subgroup G, GLAIsMaxTwoLocal M → GLAWeakCore 3 (P : Subgroup G) ≤ M →
      ∀ g : G, 3 ≤ CFSG.Open.pRank 3 (M ⊓ GLBConj g M) → GLBConj g M = M

@[expose] def InputD4Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsDFourTwo X →
    CFSG.Open.IsQuasisimple X ∧ IsSimpleGroup X ∧ 5 ∣ Nat.card X

structure Inputs : Prop where
  h31 : Lemma31
  h43 : Lemma43
  h44 : Lemma44
  h22 : Prop22
  i1021 : Input10_21
  i247 : Input24_7
  i242 : Input24_2
  iU : InputUniq
  iD4 : InputD4Two

structure Ctx (G : Type) [Group G] [Finite G] (B M : Subgroup G) : Prop where
  S : GLStanding G 4 5
  B1 : IsBOneMax 5 B
  hM : GLAIsMaxTwoLocal M
  W : ∃ P : Sylow 3 G, GLAWeakCore 3 (P : Subgroup G) ≤ M
  β : 3 ∈ GLABeta (4 + 1) G

section G1

variable {G : Type} [Group G] [Finite G]

theorem isFiTwentyTwo_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsFiTwentyTwo X) : IsFiTwentyTwo Y := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem isDFourTwo_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsDFourTwo X) : IsDFourTwo Y := by
  obtain ⟨hadm, h⟩ := h
  refine ⟨hadm, ?_⟩
  obtain ⟨K, x, hfin, hK, ⟨f⟩⟩ := h
  exact ⟨K, x, hfin, hK, ⟨e.symm.trans f⟩⟩

theorem glaPPrimeCoreOf_eq_inf_of_isSubnormal {p : ℕ} (hp : p.Prime) {S Y : Subgroup G}
    (h : IsSubnormal S Y) : GLAPPrimeCoreOf p S = S ⊓ GLAPPrimeCoreOf p Y := by
  exact (glaPPrimeCoreOf_inf_eq_of_isSubnormal hp h).symm

theorem barOf_equiv_barX {p : ℕ} (hp : p.Prime) {S Y : Subgroup G} (h : IsSubnormal S Y) :
    Nonempty (barOf p S ≃* ↥(barX p Y S)) := by
  exact ⟨quotEquivBarX hp (isSubnormal_le' h) h⟩

theorem glaPComponent_self {p : ℕ} (hp : p.Prime) {Y K : Subgroup G}
    (h : GLAPComponent p Y K) : GLAPComponent p K K := by
  exact glaPComponent_of_le hp h le_rfl h.1

theorem glaPLayer_eq_of_glaPComponent {p : ℕ} (hp : p.Prime) {Y K : Subgroup G}
    (h : GLAPComponent p Y K) : GLAPLayer p K = K := by
  exact le_antisymm (sSup_le fun L hL => hL.1) (le_sSup (glaPComponent_self hp h))

theorem isQuasisimple_barOf_of_glaPComponent {p : ℕ} (hp : p.Prime) {Y K : Subgroup G}
    (h : GLAPComponent p Y K) : CFSG.Open.IsQuasisimple (barOf p K) := by
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (quotEquivBarX hp h.1 h.2.1).symm h.2.2.1.2.2

private theorem mem_sup_iff_mul_g1b {G : Type*} [Group G] {Y R : Subgroup G}
    (hYR : Y ≤ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ Y ⊔ R) :
    ∃ y ∈ Y, ∃ z ∈ R, y * z = x := by
  have := Subgroup.coe_mul_of_left_le_normalizer_right Y R hYR
  have hx' : x ∈ (↑(Y ⊔ R) : Set G) := hx
  rw [this] at hx'
  obtain ⟨y, hy, z, hz, h⟩ := Set.mem_mul.1 hx'
  exact ⟨y, hy, z, hz, h⟩

theorem barOf_equiv_of_cover {p : ℕ} (hp : p.Prime) {Y T : Subgroup G} (hYT : Y ≤ T)
    (hcov : T ≤ Y ⊔ GLAPPrimeCoreOf p T) :
    GLAPPrimeCoreOf p Y = Y ⊓ GLAPPrimeCoreOf p T ∧ Nonempty (barOf p Y ≃* barOf p T) := by
  set f : ↥Y →* barOf p T :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥T)).comp (Subgroup.inclusion hYT) with hf
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥T) q
    obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup_iff_mul_g1b
      (hYT.trans (le_normalizer_glaPPrimeCoreOf p T)) (hcov t.2)
    obtain ⟨z', hz', hzz⟩ := hz
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [hf, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (Subgroup.inclusion hYT ⟨y, hy⟩)⁻¹ * t = z' := by
      apply Subtype.ext
      have h1 : (z' : G) = z := hzz
      simp [Subgroup.coe_inclusion, h1, ← hyz]
    rw [this]
    exact hz'
  have hker : f.ker = GLAPPrimeCore p ↥Y := by
    apply le_antisymm
    · have hnorm : f.ker.Normal := MonoidHom.normal_ker f
      have hcop : Nat.Coprime p (Nat.card f.ker) := by
        have hle : f.ker.map (Subgroup.inclusion hYT) ≤ GLAPPrimeCore p ↥T := by
          rintro _ ⟨x, hx, rfl⟩
          have : QuotientGroup.mk' (GLAPPrimeCore p ↥T) (Subgroup.inclusion hYT x) = 1 := hx
          exact (QuotientGroup.eq_one_iff _).1 this
        have h1 : Nat.card (f.ker.map (Subgroup.inclusion hYT)) = Nat.card f.ker :=
          Subgroup.card_map_of_injective (Subgroup.inclusion_injective hYT)
        have h2 : Nat.card f.ker ∣ Nat.card (GLAPPrimeCore p ↥T) :=
          h1 ▸ Subgroup.card_dvd_of_le hle
        exact Nat.Coprime.coprime_dvd_right h2 (coprime_card_gLAPPrimeCore_aux p ↥T)
      exact le_sSup ⟨hnorm, hcop⟩
    · set N := (GLAPPrimeCore p ↥Y).map f with hN
      have hNn : N.Normal := (GLAPPrimeCore.normal p ↥Y).map f hsurj
      have hNc : Nat.Coprime p (Nat.card N) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (GLAPPrimeCore p ↥Y) f)
          (coprime_card_gLAPPrimeCore_aux p ↥Y)
      have hN0 : N ≤ GLAPPrimeCore p (barOf p T) := le_sSup ⟨hNn, hNc⟩
      rw [glaPPrimeCore_quotient_eq_bot hp] at hN0
      intro x hx
      have h1 : f x ∈ N := ⟨x, hx, rfl⟩
      have h2 := hN0 h1
      rw [Subgroup.mem_bot] at h2
      exact h2
  refine ⟨?_, ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : y ∈ f.ker := hker ▸ hy
    have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥T) (Subgroup.inclusion hYT y) = 1 := h1
    refine ⟨y.2, ⟨Subgroup.inclusion hYT y, (QuotientGroup.eq_one_iff _).1 h2, rfl⟩⟩
  · rintro ⟨hxY, t, ht, hxt⟩
    have h1 : (⟨x, hxY⟩ : ↥Y) ∈ f.ker := by
      show QuotientGroup.mk' (GLAPPrimeCore p ↥T) (Subgroup.inclusion hYT ⟨x, hxY⟩) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have : Subgroup.inclusion hYT ⟨x, hxY⟩ = t := Subtype.ext hxt.symm
      rw [this]
      exact ht
    rw [hker] at h1
    exact ⟨⟨x, hxY⟩, h1, rfl⟩

theorem exists_glaPComponent_of_isQuasisimple_barOf {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (barOf p Y)) :
    ∃ K : Subgroup G, GLAPComponent p Y K ∧ Nonempty (barOf p K ≃* barOf p Y) := by
  have hcomp : IsComponentOf (⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)) ⊤ := by
    refine ⟨le_rfl, IsSubnormal.refl _, ?_⟩
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv).symm hq
  obtain ⟨K, hK, hbar⟩ := exists_glaPComponent_barX_eq (p := p) Y hcomp
  refine ⟨K, hK, ⟨?_⟩⟩
  exact (quotEquivBarX hp hK.1 hK.2.1).trans
    ((MulEquiv.subgroupCongr hbar).trans Subgroup.topEquiv)

theorem exists_layer_eq_component {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (barOf p Y)) :
    ∃ K : Subgroup G, GLAPComponent p Y K ∧ GLAPLayer p Y = K ∧
      Nonempty (barOf p K ≃* barOf p Y) := by
  obtain ⟨K, hK, hKe⟩ := exists_glaPComponent_of_isQuasisimple_barOf hp hq
  have htopq : CFSG.Open.IsQuasisimple (↥(⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y))) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv).symm hq
  have htop : ∀ L : Subgroup G, GLAPComponent p Y L → barX p Y L = ⊤ := fun L hL =>
    CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple hL.2.2.1 htopq
  refine ⟨K, hK, ?_, hKe⟩
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    exact (glaPComponent_unique hL hK ((htop L hL).trans (htop K hK).symm)).le
  · exact le_sSup hK

theorem exists_component_of_cover {p : ℕ} (hp : p.Prime) {Y T : Subgroup G} (hYT : Y ≤ T)
    (hcov : T ≤ Y ⊔ GLAPPrimeCoreOf p T) (hq : CFSG.Open.IsQuasisimple (barOf p T)) :
    ∃ K : Subgroup G, K ≤ Y ∧ GLAPComponent p Y K ∧ Nonempty (barOf p K ≃* barOf p T) := by
  obtain ⟨-, ⟨e⟩⟩ := barOf_equiv_of_cover hp hYT hcov
  have hqY : CFSG.Open.IsQuasisimple (barOf p Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq
  obtain ⟨K, hK, ⟨e'⟩⟩ := exists_glaPComponent_of_isQuasisimple_barOf hp hqY
  exact ⟨K, hK.1, hK, ⟨e'.trans e⟩⟩

end G1

section G2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_mem_centralizer_of_coprime {p : ℕ} (hp : p.Prime) {P R : Subgroup G}
    (hP : IsPGroup p P) (hR : ¬ p ∣ Nat.card R) (hPR : P ≤ Subgroup.normalizer (R : Set G))
    {g : G} (hg : ∀ x ∈ P, g⁻¹ * (x * g * x⁻¹) ∈ R) :
    ∃ r ∈ R, g * r ∈ Subgroup.centralizer (P : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ (x : ↥P) (r : ↥R), g⁻¹ * ((x : G) * (g * (r : G)) * (x : G)⁻¹) ∈ R := by
    intro x r
    have h1 := hg x x.2
    have h2 : (x : G) * (r : G) * (x : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.1 (hPR x.2) (r : G)).1 r.2
    have h3 := R.mul_mem h1 h2
    have : g⁻¹ * ((x : G) * (g * (r : G)) * (x : G)⁻¹) =
        g⁻¹ * ((x : G) * g * (x : G)⁻¹) * ((x : G) * (r : G) * (x : G)⁻¹) := by group
    rw [this]
    exact h3
  let : MulAction ↥P ↥R :=
    { smul := fun x r => ⟨g⁻¹ * ((x : G) * (g * (r : G)) * (x : G)⁻¹), hmem x r⟩
      one_smul := fun r => by
        apply Subtype.ext
        show g⁻¹ * (((1 : ↥P) : G) * (g * (r : G)) * ((1 : ↥P) : G)⁻¹) = (r : G)
        simp
      mul_smul := fun x y r => by
        apply Subtype.ext
        show g⁻¹ * (((x * y : ↥P) : G) * (g * (r : G)) * ((x * y : ↥P) : G)⁻¹) =
          g⁻¹ * ((x : G) * (g * (g⁻¹ * ((y : G) * (g * (r : G)) * (y : G)⁻¹))) * (x : G)⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group }
  obtain ⟨r, hr⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card ↥R hR
  refine ⟨r, r.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := hr ⟨x, hx⟩
  have h' : g⁻¹ * (x * (g * (r : G)) * x⁻¹) = (r : G) := congrArg Subtype.val h
  have : x * (g * (r : G)) * x⁻¹ = g * (r : G) := by
    calc x * (g * (r : G)) * x⁻¹ = g * (g⁻¹ * (x * (g * (r : G)) * x⁻¹)) := by group
      _ = g * (r : G) := by rw [h']
  calc x * (g * (r : G)) = (x * (g * (r : G)) * x⁻¹) * x := by group
    _ = g * (r : G) * x := by rw [this]

theorem le_inf_centralizer_sup_of_acts_trivially {p : ℕ} (hp : p.Prime) {L P : Subgroup G}
    (hP : IsPGroup p P) (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (htriv : ∀ x ∈ P, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p L) :
    L ≤ (L ⊓ Subgroup.centralizer (P : Set G)) ⊔ GLAPPrimeCoreOf p L := by
  intro l hl
  have hRL : GLAPPrimeCoreOf p L ≤ L := Subgroup.map_subtype_le _
  have hR : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p L) := not_dvd_card_glaPPrimeCoreOf hp L
  have hPR : P ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := by
    intro x hx
    have h1 := hPL hx
    rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
    rw [← glaPPrimeCoreOf_gLBConj, h1]
  have hg : ∀ x ∈ P, l⁻¹ * (x * l * x⁻¹) ∈ GLAPPrimeCoreOf p L := by
    intro x hx
    have h1 := htriv x hx l hl
    have h2 := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf p L (inv_mem hl)) _).1 h1
    have : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
    rw [this] at h2
    exact h2
  obtain ⟨r, hr, hcent⟩ := exists_mul_mem_centralizer_of_coprime hp hP hR hPR hg
  have hlr : l * r ∈ L ⊓ Subgroup.centralizer (P : Set G) := ⟨L.mul_mem hl (hRL hr), hcent⟩
  have : l = (l * r) * r⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem_sup hlr ((GLAPPrimeCoreOf p L).inv_mem hr)

theorem layer_cent {p : ℕ} (hp : p.Prime) {L P : Subgroup G} (hP : IsPGroup p P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (htriv : ∀ x ∈ P, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p L)
    (hq : CFSG.Open.IsQuasisimple (barOf p L)) :
    GLAPComponent p (L ⊓ Subgroup.centralizer (P : Set G))
        (GLAPLayer p (L ⊓ Subgroup.centralizer (P : Set G))) ∧
      Nonempty (barOf p (GLAPLayer p (L ⊓ Subgroup.centralizer (P : Set G))) ≃* barOf p L) := by
  have hcov := le_inf_centralizer_sup_of_acts_trivially hp hP hPL htriv
  obtain ⟨-, ⟨e⟩⟩ := barOf_equiv_of_cover hp
    (inf_le_left : L ⊓ Subgroup.centralizer (P : Set G) ≤ L) hcov
  have hqY : CFSG.Open.IsQuasisimple (barOf p (L ⊓ Subgroup.centralizer (P : Set G))) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq
  obtain ⟨K, hK, hKe, ⟨e'⟩⟩ := exists_layer_eq_component hp hqY
  rw [hKe]
  exact ⟨hK, ⟨e'.trans e⟩⟩

omit [Finite G] in
theorem mem_cBarB_iff {p : ℕ} {B L : Subgroup G} {x : G} :
    x ∈ cBarB p B L ↔ x ∈ B ∧ ∃ h : x ∈ Subgroup.normalizer (L : Set G),
      barAut p L ⟨x, h⟩ = 1 := by
  have hxU : x ∈ Subgroup.normalizer (L : Set G) → x ∈ Subgroup.normalizer
      (GLAPPrimeCoreOf p L : Set G) := by
    intro h1
    rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
    rw [← glaPPrimeCoreOf_gLBConj, h1]
  have key : ∀ l : G, l ∈ L → (l * x * l⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L ↔
      x * l⁻¹ * x⁻¹ * l ∈ GLAPPrimeCoreOf p L) := by
    intro l hl
    have h1 := Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p L hl)
    have h2 := Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p L (inv_mem hl))
    constructor
    · intro hu
      have := (h2 _).1 hu
      have e : l⁻¹ * (l * x * l⁻¹ * x⁻¹) * l⁻¹⁻¹ = x * l⁻¹ * x⁻¹ * l := by group
      rwa [e] at this
    · intro hv
      have := (h1 _).1 hv
      have e : l * (x * l⁻¹ * x⁻¹ * l) * l⁻¹ = l * x * l⁻¹ * x⁻¹ := by group
      rwa [e] at this
  unfold cBarB
  rw [Subgroup.mem_inf]
  show x ∈ B ∧ (x ∈ Subgroup.normalizer (L : Set G) ∧
      x ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) ∧
      ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L) ↔ _
  constructor
  · rintro ⟨hxB, hxN, -, hx⟩
    refine ⟨hxB, hxN, ?_⟩
    apply MulEquiv.ext
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    rw [barAut_mk]
    show QuotientGroup.mk (L.normalizerMonoidHom ⟨x, hxN⟩ l) = QuotientGroup.mk l
    rw [QuotientGroup.eq]
    have hu := (key l l.2).1 (hx l l.2)
    refine (Subgroup.mem_map_iff_mem L.subtype_injective).1 ?_
    show ((L.normalizerMonoidHom ⟨x, hxN⟩ l)⁻¹ * l : ↥L).1 ∈ GLAPPrimeCoreOf p L
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe,
      mul_inv_rev, inv_inv]
    have e : x * (l : G)⁻¹ * x⁻¹ * (l : G) = x * (l : G)⁻¹ * x⁻¹ * l := rfl
    simpa [mul_assoc] using hu
  · rintro ⟨hxB, hxN, h1⟩
    refine ⟨hxB, hxN, hxU hxN, fun l hl => ?_⟩
    have h2 := congrArg (fun φ : MulAut (↥L ⧸ GLAPPrimeCore p ↥L) => φ (QuotientGroup.mk ⟨l, hl⟩)) h1
    simp only [barAut_mk, MulAut.one_apply] at h2
    have h3 := (QuotientGroup.eq).1 h2
    have h4 : x * l⁻¹ * x⁻¹ * l ∈ GLAPPrimeCoreOf p L := by
      refine ⟨_, h3, ?_⟩
      simp [mul_assoc]
    exact (key l hl).2 h4

private theorem zpowers_fix_coset_g2 {G : Type*} [Group G] {R : Subgroup G} {l a : G}
    (haR : a ∈ Subgroup.normalizer (R : Set G)) (h : l⁻¹ * (a * l * a⁻¹) ∈ R) :
    ∀ x ∈ Subgroup.zpowers a, l⁻¹ * (x * l * x⁻¹) ∈ R := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (R : Set G) ∧ l⁻¹ * (x * l * x⁻¹) ∈ R}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
        refine ⟨mul_mem hxN hyN, ?_⟩
        have h2 : x * (l⁻¹ * (y * l * y⁻¹)) * x⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.1 hxN _).1 hy
        have h3 := R.mul_mem hx h2
        have e : l⁻¹ * (x * l * x⁻¹) * (x * (l⁻¹ * (y * l * y⁻¹)) * x⁻¹) =
            l⁻¹ * (x * y * l * (x * y)⁻¹) := by group
        rwa [e] at h3
      inv_mem' := by
        rintro x ⟨hxN, hx⟩
        refine ⟨inv_mem hxN, ?_⟩
        have h2 : x⁻¹ * (l⁻¹ * (x * l * x⁻¹))⁻¹ * x⁻¹⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) _).1 (R.inv_mem hx)
        have e : x⁻¹ * (l⁻¹ * (x * l * x⁻¹))⁻¹ * x⁻¹⁻¹ = l⁻¹ * (x⁻¹ * l * x⁻¹⁻¹) := by group
        rwa [e] at h2 }
  have : Subgroup.zpowers a ≤ S := (Subgroup.zpowers_le).2 ⟨haR, h⟩
  intro x hx
  exact (this hx).2

theorem fixSub_barAut_le_map {p : ℕ} (hp : p.Prime) {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hord : IsPGroup p (Subgroup.zpowers a)) :
    fixSub (barAut p L ⟨a, ha⟩) ≤
      ((L ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) := by
  intro q hq
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hq' : (barAut p L ⟨a, ha⟩) (QuotientGroup.mk l) = QuotientGroup.mk l := hq
  rw [barAut_mk, QuotientGroup.eq] at hq'
  have hRL : GLAPPrimeCoreOf p L ≤ L := Subgroup.map_subtype_le _
  have hR : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p L) := not_dvd_card_glaPPrimeCoreOf hp L
  have hPN : ∀ x : G, x ∈ Subgroup.normalizer (L : Set G) →
      x ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := by
    intro x h1
    rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
    rw [← glaPPrimeCoreOf_gLBConj, h1]
  have haR := hPN a ha
  have hPR : Subgroup.zpowers a ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    (Subgroup.zpowers_le).2 haR
  have hl : (l : G) ∈ L := l.2
  have hfix : (l : G)⁻¹ * (a * l * a⁻¹) ∈ GLAPPrimeCoreOf p L := by
    have h1 := (GLAPPrimeCore p ↥L).inv_mem hq'
    refine ⟨_, h1, ?_⟩
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe, mul_assoc]
  obtain ⟨r, hr, hcent⟩ := exists_mul_mem_centralizer_of_coprime hp hord hR hPR (g := (l : G))
    (zpowers_fix_coset_g2 haR hfix)
  obtain ⟨r', hr', rfl⟩ := hr
  have hlr : (l : G) * (r' : G) ∈ L := L.mul_mem hl r'.2
  refine ⟨⟨(l : G) * r', hlr⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine ⟨hlr, ?_⟩
    show (l : G) * r' ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (Subgroup.mem_centralizer_iff.1 hcent) h (Subgroup.mem_zpowers h)
  · show QuotientGroup.mk (⟨(l : G) * r', hlr⟩ : ↥L) = QuotientGroup.mk l
    rw [QuotientGroup.eq]
    have : (⟨(l : G) * r', hlr⟩ : ↥L)⁻¹ * l = r'⁻¹ := by
      apply Subtype.ext
      simp
    rw [this]
    exact (GLAPPrimeCore p ↥L).inv_mem hr'

end G2

section G3

variable {G : Type} [Group G] [Finite G]

theorem isTwoLocal_gLBConj {H : Subgroup G} (h : IsTwoLocal H) (g : G) :
    IsTwoLocal (GLBConj g H) := by
  obtain ⟨S, hS, hS2, rfl⟩ := h
  refine ⟨GLBConj g S, ?_, ?_, (normalizer_gLBConj g S).symm⟩
  · intro h0
    exact hS ((gLBConj_eq_bot_iff g S).1 h0)
  · have hcard : Nat.card (GLBConj g S) = Nat.card S :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hS2)
    exact IsPGroup.iff_card.2 ⟨n, by rw [hcard, hn]⟩

theorem isMaxTwoLocal_gLBConj {M : Subgroup G} (h : GLAIsMaxTwoLocal M) (g : G) :
    GLAIsMaxTwoLocal (GLBConj g M) := by
  refine ⟨isTwoLocal_gLBConj h.1 g, fun H hH hle => ?_⟩
  have h1 := isTwoLocal_gLBConj hH g⁻¹
  have h2 : M ≤ GLBConj g⁻¹ H := by
    have := gLBConj_mono g⁻¹ hle
    rwa [gLBConj_inv_gLBConj] at this
  have h3 := h.2 _ h1 h2
  have h4 := congrArg (GLBConj g) h3
  rwa [gLBConj_gLBConj_inv] at h4

theorem mem_of_gLBConj_eq {M : Subgroup G} (h : GLAIsMaxTwoLocal M) {g : G}
    (hg : GLBConj g M = M) : g ∈ M := by
  obtain ⟨S, hS, hS2, hMS⟩ := h.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSle : S ≤ pCoreOf 2 M := by
    rw [hMS]
    exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 S hS2
  have hTne : pCoreOf 2 M ≠ ⊥ := fun h0 => hS (le_bot_iff.1 (h0 ▸ hSle))
  have hT2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMT : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hNT : Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
    h.2 _ ⟨_, hTne, hT2, rfl⟩ hMT
  have hgT : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq, ← pCoreOf_gLBConj, hg]
  rw [← hNT]
  exact hgT

theorem pRank_gLBConj {p : ℕ} (hp : p.Prime) (H : Subgroup G) (g : G) :
    CFSG.Open.pRank p (GLBConj g H) = CFSG.Open.pRank p H := by
  have hp1 : 1 < p := hp.one_lt
  have hle : ∀ (H : Subgroup G) (g : G), CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (GLBConj g H) :=
    fun H g => CFSG.SectionRank.pRank_le_map hp1 (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective H
  refine le_antisymm ?_ (hle H g)
  have := hle (GLBConj g H) g⁻¹
  rwa [gLBConj_inv_gLBConj] at this

private theorem gLBConj_sup_g3 {G : Type*} [Group G] (h : G) (A B : Subgroup G) :
    GLBConj h (A ⊔ B) = GLBConj h A ⊔ GLBConj h B := Subgroup.map_sup _ _ _

private theorem gLBConj_inf_g3 {G : Type*} [Group G] (h : G) (A B : Subgroup G) :
    GLBConj h (A ⊓ B) = GLBConj h A ⊓ GLBConj h B :=
  Subgroup.map_inf A B (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective

theorem glaWeakCore_gLBConj {p : ℕ} (hp : p.Prime) (P : Subgroup G) (g : G) :
    GLAWeakCore p (GLBConj g P) = GLBConj g (GLAWeakCore p P) := by
  have key : ∀ (g : G) (P : Subgroup G),
      GLAWeakCore p (GLBConj g P) ≤ GLBConj g (GLAWeakCore p P) := by
    intro g P
    refine sSup_le ?_
    rintro N ⟨Q, hQP, h2, h3, rfl⟩
    have hQ₀P : GLBConj g⁻¹ Q ≤ P := by
      have := gLBConj_mono g⁻¹ hQP
      rwa [gLBConj_inv_gLBConj] at this
    have hr2 : 2 ≤ CFSG.Open.pRank p (GLBConj g⁻¹ Q) := by
      rw [pRank_gLBConj hp]; exact h2
    have hr3 : 3 ≤ CFSG.Open.pRank p
        (GLBConj g⁻¹ Q ⊔ (P ⊓ Subgroup.centralizer (GLBConj g⁻¹ Q : Set G))) := by
      have e : GLBConj g⁻¹ Q ⊔ (P ⊓ Subgroup.centralizer (GLBConj g⁻¹ Q : Set G)) =
          GLBConj g⁻¹ (Q ⊔ (GLBConj g P ⊓ Subgroup.centralizer (Q : Set G))) := by
        rw [gLBConj_sup_g3, gLBConj_inf_g3, gLBConj_inv_gLBConj, gLBConj_centralizer]
      rw [e, pRank_gLBConj hp]
      exact h3
    have hle : Subgroup.normalizer (GLBConj g⁻¹ Q : Set G) ≤ GLAWeakCore p P :=
      le_sSup ⟨_, hQ₀P, hr2, hr3, rfl⟩
    have h4 := gLBConj_mono g hle
    rwa [← normalizer_gLBConj, gLBConj_gLBConj_inv] at h4
  refine le_antisymm (key g P) ?_
  have h5 := key g⁻¹ (GLBConj g P)
  rw [gLBConj_inv_gLBConj] at h5
  have h6 := gLBConj_mono g h5
  rwa [gLBConj_gLBConj_inv] at h6

theorem glaWeakCore_mono {p : ℕ} (hp : p.Prime) {P P' : Subgroup G} (h : P ≤ P') :
    GLAWeakCore p P ≤ GLAWeakCore p P' := by
  refine sSup_le_sSup ?_
  rintro N ⟨Q, hQP, h2, h3, rfl⟩
  refine ⟨Q, hQP.trans h, h2, ?_, rfl⟩
  exact h3.trans (CFSG.SectionRank.pRank_mono hp.one_lt
    (sup_le_sup_left (inf_le_inf_right _ h) _))

theorem normalizer_le_glaWeakCore {p : ℕ} {P : Subgroup G} (h : 3 ≤ CFSG.Open.pRank p P) :
    Subgroup.normalizer (P : Set G) ≤ GLAWeakCore p P := by
  refine le_sSup ⟨P, le_rfl, (by norm_num : 2 ≤ 3).trans h, ?_, rfl⟩
  rw [sup_eq_left.2 inf_le_left]
  exact h

theorem weakCoreIn_le_glaWeakCore (p : ℕ) (P K : Subgroup G) :
    weakCoreIn p P K ≤ GLAWeakCore p P := by
  refine iSup₂_le fun Q hQ => ?_
  exact inf_le_right.trans (le_sSup ⟨Q, hQ.1, hQ.2.1, hQ.2.2, rfl⟩)

theorem le_sup_normalizer_of_sylow {p : ℕ} (hp : p.Prime) {I C Q : Subgroup G} (hIC : I ≤ C)
    (hn : (I.subgroupOf C).Normal) (hQI : Q ≤ I) (_hQ : IsPGroup p Q)
    (hcard : Nat.card Q = p ^ (Nat.card I).factorization p) :
    C ≤ I ⊔ Subgroup.normalizer (Q : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hQC : Q ≤ C := hQI.trans hIC
  set Ĩ : Subgroup ↥C := I.subgroupOf C with hĨ
  have : Ĩ.Normal := hn
  have hQĨ : Q.subgroupOf C ≤ Ĩ := fun x hx => (Subgroup.mem_subgroupOf).2 (hQI ((Subgroup.mem_subgroupOf).1 hx))
  let Q' : Subgroup ↥Ĩ := (Q.subgroupOf C).subgroupOf Ĩ
  have hcardQ' : Nat.card Q' = p ^ (Nat.card Ĩ).factorization p := by
    have h1 : Nat.card Q' = Nat.card Q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQĨ).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv]
    have h2 : Nat.card Ĩ = Nat.card I := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIC).toEquiv
    rw [h1, h2, hcard]
  let P : Sylow p ↥Ĩ := Sylow.ofCard Q' hcardQ'
  have hfr := Sylow.normalizer_sup_eq_top P
  have hmap : (P : Subgroup ↥Ĩ).map Ĩ.subtype = Q.subgroupOf C :=
    Subgroup.map_subgroupOf_eq_of_le hQĨ
  rw [hmap] at hfr
  intro c hc
  have hcmem : (⟨c, hc⟩ : ↥C) ∈ Subgroup.normalizer ((Q.subgroupOf C : Subgroup ↥C) : Set ↥C) ⊔ Ĩ := by
    rw [hfr]; trivial
  obtain ⟨n, hnN, i, hi, hni⟩ := Subgroup.mem_sup_of_normal_right.1 hcmem
  have hnQ : (n : G) ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := Subgroup.mem_normalizer_iff.1 hnN
    constructor
    · intro hg
      have := (h1 ⟨g, hQC hg⟩).1 ((Subgroup.mem_subgroupOf).2 hg)
      exact (Subgroup.mem_subgroupOf).1 this
    · intro hg
      have hgC : g ∈ C := by
        have := C.mul_mem (C.mul_mem (C.inv_mem n.2) (hQC hg)) n.2
        simpa [mul_assoc] using this
      have := (h1 ⟨g, hgC⟩).2 ((Subgroup.mem_subgroupOf).2 hg)
      exact (Subgroup.mem_subgroupOf).1 this
  have hiI : (i : G) ∈ I := (Subgroup.mem_subgroupOf).1 hi
  have hceq : c = (n : G) * i := by
    have := congrArg (fun z : ↥C => (z : G)) hni
    simpa using this.symm
  rw [hceq, sup_comm]
  exact Subgroup.mul_mem_sup hnQ hiI

theorem exists_sylow_ge {p : ℕ} (hp : p.Prime) {K E : Subgroup G} (hEK : E ≤ K)
    (hE : IsPGroup p E) :
    ∃ Q : Subgroup G, E ≤ Q ∧ Q ≤ K ∧ IsPGroup p Q ∧
      Nat.card Q = p ^ (Nat.card K).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hE' : IsPGroup p (E.subgroupOf K) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm
  obtain ⟨S, hS⟩ := hE'.exists_le_sylow
  refine ⟨(S : Subgroup ↥K).map K.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hEK hx⟩, hS ((Subgroup.mem_subgroupOf).2 hx), rfl⟩
  · exact S.isPGroup'.map K.subtype
  · rw [Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity S]

end G3

section G4

variable {G : Type} [Group G] [Finite G]

theorem three_mem_beta {m : ℕ} (hm : m = 4) {N : Subgroup G} (hN : IsTwoLocal N)
    (hr : 5 ≤ CFSG.Open.pRank 3 N) : 3 ∈ GLABeta (m + 1) G := by
  subst hm
  refine ⟨Nat.prime_three, by norm_num, ?_, ?_⟩
  · obtain ⟨E, hEN, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) N
    have h1 : 3 ∣ Nat.card E := by
      rw [hcard]
      exact dvd_pow_self 3 (by omega)
    exact h1.trans (Subgroup.card_subgroup_dvd_card E)
  · exact (by norm_num : 4 + 1 ≤ 5).trans
      (hr.trans (pRank_le_glaTwoLocalRank_of_isTwoLocal Nat.prime_three hN))

private theorem pCoreOf_ne_bot_of_isTwoLocal_g4 {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : IsTwoLocal H) : pCoreOf 2 H ≠ ⊥ := by
  obtain ⟨S, hS, hS2, rfl⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h0
  have hSle := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 S hS2
  exact hS (le_bot_iff.1 (h0 ▸ hSle))

theorem exists_setting {m p : ℕ} (hS : GLStanding G m p) (hm : m = 4) {N : Subgroup G}
    (hN : IsTwoLocal N) (hr : 5 ≤ CFSG.Open.pRank 3 N) :
    ∃ M : Subgroup G, GLAIsMaxTwoLocal M ∧
      ∃ P : Sylow 3 G, GLAWeakCore 3 (P : Subgroup G) ≤ M := by
  have hβ := three_mem_beta hm hN hr
  have hW := hS.weakCoreLocal 3 hβ
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  obtain ⟨H, hH, hle⟩ := hW.2 P
  obtain ⟨M, hM, hHM⟩ := exists_isMaxTwoLocal_of_pCoreOf_ne_bot (pCoreOf_ne_bot_of_isTwoLocal_g4 hH)
  exact ⟨M, hM, P, hle.trans hHM⟩

theorem uniq_conj (iU : InputUniq) {m p : ℕ} (hS : GLStanding G m p)
    (hβ : 3 ∈ GLABeta (m + 1) G) {M : Subgroup G} (hM : GLAIsMaxTwoLocal M) (P : Sylow 3 G)
    (hP : GLAWeakCore 3 (P : Subgroup G) ≤ M) {M₁ M₂ : Subgroup G}
    (h₁ : ∃ g : G, M₁ = GLBConj g M) (h₂ : ∃ g : G, M₂ = GLBConj g M)
    (hr : 3 ≤ CFSG.Open.pRank 3 (M₁ ⊓ M₂)) : M₁ = M₂ := by
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  have hM12 : GLBConj g₁ M ⊓ GLBConj g₂ M = GLBConj g₁ (M ⊓ GLBConj (g₂ * g₁⁻¹) M) := by
    rw [gLBConj_inf_g3, gLBConj_gLBConj, mul_assoc, inv_mul_cancel, mul_one]
  rw [hM12, pRank_gLBConj Nat.prime_three] at hr
  have h := iU G m _ hS hβ P M hM hP (g₂ * g₁⁻¹) hr
  have h2 : GLBConj g₂ M = GLBConj g₁ (GLBConj (g₂ * g₁⁻¹) M) := by
    rw [gLBConj_gLBConj, mul_assoc, inv_mul_cancel, mul_one]
  rw [h2, h]

theorem exists_conj_ge {M : Subgroup G} (P : Sylow 3 G)
    (hP : GLAWeakCore 3 (P : Subgroup G) ≤ M) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hr : 3 ≤ CFSG.Open.pRank 3 Q) :
    ∃ M' : Subgroup G, (∃ g : G, M' = GLBConj g M) ∧ Q ≤ M' ∧ GLAWeakCore 3 Q ≤ M' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hQP', -, hP'p, hP'card⟩ := exists_sylow_ge Nat.prime_three (le_top : Q ≤ ⊤) hQ
  have hcardG : Nat.card P' = 3 ^ (Nat.card G).factorization 3 := by
    rw [hP'card, Subgroup.card_top]
  let P'' : Sylow 3 G := Sylow.ofCard P' hcardG
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P''
  have hP'' : (P'' : Subgroup G) = GLBConj g⁻¹ (P : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    simp [GLBConj]
    rfl
  have hQP'' : Q ≤ (P'' : Subgroup G) := hQP'
  have hrk : 3 ≤ CFSG.Open.pRank 3 (P'' : Subgroup G) :=
    hr.trans (CFSG.SectionRank.pRank_mono (by norm_num) hQP'')
  have hW : GLAWeakCore 3 (P'' : Subgroup G) ≤ GLBConj g⁻¹ M := by
    rw [hP'', glaWeakCore_gLBConj Nat.prime_three]
    exact gLBConj_mono g⁻¹ hP
  refine ⟨GLBConj g⁻¹ M, ⟨g⁻¹, rfl⟩, ?_, ?_⟩
  · exact hQP''.trans (Subgroup.le_normalizer.trans ((normalizer_le_glaWeakCore hrk).trans hW))
  · exact (glaWeakCore_mono Nat.prime_three hQP'').trans hW

end G4

section G5

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_barOf_mt {b : G} {L : Subgroup G} (h : IsMT b L) :
    CFSG.Open.IsQuasisimple (barOf 5 L) := by
  exact isQuasisimple_barOf_of_glaPComponent (by norm_num : Nat.Prime 5) h.1

omit [Finite G] in
theorem mem_cBarB_of_le_centralizer {B L : Subgroup G} {b : G} (hb : b ∈ B) (hL : L ≤ Cb b) :
    b ∈ cBarB 5 B L := by
  have hcomm : ∀ x ∈ L, b * x = x * b := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hL hx)).symm
  have hN : b ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hbx : b * x * b⁻¹ = x ∨ x ∉ L := by
      by_cases hx : x ∈ L
      · left
        rw [hcomm x hx]; group
      · right; exact hx
    constructor
    · intro hx
      rw [hcomm x hx]
      simpa using hx
    · intro hx
      have h1 := hcomm _ hx
      have h2 : x = b⁻¹ * (b * x * b⁻¹) * b := by group
      have h3 : b⁻¹ * (b * x * b⁻¹) * b = b * x * b⁻¹ := by
        have : b * (b * x * b⁻¹) = (b * x * b⁻¹) * b := h1
        calc b⁻¹ * (b * x * b⁻¹) * b = b⁻¹ * ((b * x * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [this]
          _ = b * x * b⁻¹ := by group
      rw [h2, h3]
      exact hx
  refine (mem_cBarB_iff).2 ⟨hb, hN, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  rw [barAut_mk]
  show QuotientGroup.mk (L.normalizerMonoidHom ⟨b, hN⟩ l) = QuotientGroup.mk l
  congr 1
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcomm l l.2]
  group

theorem mt_structure (h43 : Lemma43) {m : ℕ} (hS : GLStanding G m 5) (hm : m = 4)
    {B : Subgroup G} (hB : IsBOneMax 5 B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G}
    (hL : IsMT b L) :
    B ≤ Subgroup.normalizer (L : Set G) ∧ cBarB 5 B L ≤ B ∧ Nat.card (cBarB 5 B L) = 5 ^ 2 ∧
      Nat.card ↥(B ⊓ L) = 5 ^ 2 ∧ cBarB 5 B L ⊓ (B ⊓ L) = ⊥ := by
  have hp : Nat.Prime 5 := by norm_num
  subst hm
  obtain ⟨⟨hsup, hinf, hFpl, hFcard⟩, -, -, -⟩ := h43 G 4 5 hS rfl B hB b hb hb1 L hL.1 hL.2
  have hAB : cBarB 5 B L ≤ B := inf_le_left
  have hBel : IsElemAbelian 5 B := hB.1.1
  have hcardB : Nat.card B = 5 ^ 4 := hS.card_eq hB
  have h1 := card_sup_eq_mul_of_commute (A := cBarB 5 B L) (F := B ⊓ L)
    (fun a ha f hf => elemAbelian_comm hBel (hAB ha) ((inf_le_left : B ⊓ L ≤ B) hf)) hinf
  rw [hsup, hcardB, hFpl.2] at h1
  have hAcard : Nat.card (cBarB 5 B L) = 5 ^ 2 := by
    have h3 : (5 : ℕ) ^ 4 = 5 ^ 2 * 5 ^ 2 := by norm_num
    rw [h3] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  have hAN : cBarB 5 B L ≤ Subgroup.normalizer (L : Set G) := fun x hx => hx.2.1
  refine ⟨?_, hAB, hAcard, hFpl.2, hinf⟩
  rw [← hsup]
  exact sup_le hAN (inf_le_right.trans Subgroup.le_normalizer)

theorem mt_unique (h43 : Lemma43) {m : ℕ} (hS : GLStanding G m 5) (hm : m = 4)
    {B : Subgroup G} (hB : IsBOneMax 5 B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {L₁ L₂ : Subgroup G} (h₁ : IsMT b L₁) (h₂ : IsMT b L₂) : L₁ = L₂ := by
  by_contra hne
  have hp : Nat.Prime 5 := by norm_num
  obtain ⟨hN₁, hA₁B, hA₁c, hF₁c, hA₁F₁⟩ := mt_structure h43 hS hm hB hb hb1 h₁
  obtain ⟨hN₂, hA₂B, hA₂c, hF₂c, hA₂F₂⟩ := mt_structure h43 hS hm hB hb hb1 h₂
  have hF₂A₁ : B ⊓ L₂ ≤ cBarB 5 B L₁ := by
    intro f hf
    have hfB : f ∈ B := hf.1
    have hfL₂ : f ∈ L₂ := hf.2
    refine (mem_cBarB_iff).2 ⟨hfB, hN₁ hfB, ?_⟩
    apply MulEquiv.ext
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    rw [barAut_mk]
    show QuotientGroup.mk (L₁.normalizerMonoidHom ⟨f, hN₁ hfB⟩ l) = QuotientGroup.mk l
    rw [QuotientGroup.eq]
    have hcomm : ⁅f, (l : G)⁻¹⁆ ∈ GLAPPrimeCoreOf 5 (Cb b) := by
      have h1 := commutator_le_gLAPPrimeCore_of_ne hp h₁.1 h₂.1 hne
      rw [Subgroup.commutator_comm] at h1
      exact h1 (Subgroup.commutator_mem_commutator hfL₂ (L₁.inv_mem l.2))
    have hzL : f * (l : G) * f⁻¹ ∈ L₁ := by
      have := (Subgroup.mem_normalizer_iff.1 (hN₁ hfB) (l : G)).1 l.2
      simpa using this
    have hL₁ : ⁅f, (l : G)⁻¹⁆ ∈ L₁ := by
      have e : ⁅f, (l : G)⁻¹⁆ = (f * (l : G) * f⁻¹)⁻¹ * l := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact L₁.mul_mem (L₁.inv_mem hzL) l.2
    have hO : ⁅f, (l : G)⁻¹⁆ ∈ GLAPPrimeCoreOf 5 L₁ := by
      rw [glaPPrimeCoreOf_eq_inf_of_isSubnormal hp h₁.1.2.1]
      exact ⟨hL₁, hcomm⟩
    refine (Subgroup.mem_map_iff_mem L₁.subtype_injective).1 ?_
    show ((L₁.normalizerMonoidHom ⟨f, hN₁ hfB⟩ l)⁻¹ * l : ↥L₁).1 ∈ GLAPPrimeCoreOf 5 L₁
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have e : ⁅f, (l : G)⁻¹⁆ = (f * (l : G) * f⁻¹)⁻¹ * l := by
      simp [commutatorElement_def, mul_assoc]
    rw [← e]
    exact hO
  have hEq : B ⊓ L₂ = cBarB 5 B L₁ :=
    Subgroup.eq_of_le_of_card_ge hF₂A₁ (by rw [hA₁c, hF₂c])
  have hbA₁ : b ∈ cBarB 5 B L₁ := mem_cBarB_of_le_centralizer hb h₁.1.1
  have hbA₂ : b ∈ cBarB 5 B L₂ := mem_cBarB_of_le_centralizer hb h₂.1.1
  have hbF₂ : b ∈ B ⊓ L₂ := hEq ▸ hbA₁
  have : b ∈ cBarB 5 B L₂ ⊓ (B ⊓ L₂) := ⟨hbA₂, hbF₂⟩
  rw [hA₂F₂] at this
  exact hb1 (Subgroup.mem_bot.1 this)

omit [Finite G] in
theorem cb_conj (b g : G) : Cb (g⁻¹ * b * g) = GLBConj g (Cb b) := by
  exact centralizer_singleton_gLBConj g b

theorem mt_conj {b : G} {L : Subgroup G} (h : IsMT b L) (g : G) :
    IsMT (g⁻¹ * b * g) (GLBConj g L) := by
  refine ⟨?_, isFiTwentyTwo_of_equiv (conjQuotEquiv 5 g L) h.2⟩
  rw [cb_conj]
  exact glaPComponent_gLBConj g h.1

theorem mt_normal (h43 : Lemma43) {m : ℕ} (hS : GLStanding G m 5) (hm : m = 4)
    {B : Subgroup G} (hB : IsBOneMax 5 B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {L : Subgroup G} (hL : IsMT b L) : (L.subgroupOf (Cb b)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.1).2 ?_
  intro c hc
  have hcb : b * c = c * b := (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
  have hb' : c⁻¹ * b * c = b := by
    calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
      _ = c⁻¹ * (c * b) := by rw [hcb]
      _ = b := by group
  have h1 := mt_conj hL c
  rw [hb'] at h1
  have h2 := mt_unique h43 hS hm hB hb hb1 h1 hL
  rw [mem_normalizer_iff_gLBConj_eq]
  exact h2

end G5

section G6

variable {G : Type} [Group G] [Finite G]

theorem mt_rank (i1021 : Input10_21) {b : G} {L : Subgroup G} (h : IsMT b L) :
    5 ≤ CFSG.Open.pRank 3 L := by
  exact i1021.1 G L (glaPLayer_eq_of_glaPComponent (by norm_num) h.1) h.2

private theorem cBarB_triv_g6 {G : Type} [Group G] [Finite G] {p : ℕ} {B L : Subgroup G} {x : G}
    (hx : x ∈ cBarB p B L) : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
  intro l hl
  have hxi : x⁻¹ ∈ cBarB p B L := inv_mem hx
  have h1 : l * x⁻¹ * l⁻¹ * x⁻¹⁻¹ ∈ GLAPPrimeCoreOf p L := hxi.2.2.2 l hl
  have h2 := (Subgroup.mem_normalizer_iff.1 hx.2.2.1 _).1 h1
  have e : x * (l * x⁻¹ * l⁻¹ * x⁻¹⁻¹) * x⁻¹ = x * l * x⁻¹ * l⁻¹ := by group
  rwa [e] at h2

private theorem isPGroup_zpowers_g6 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {a : G}
    (h : a ^ p = 1) : IsPGroup p (Subgroup.zpowers a) := by
  have : Fact p.Prime := ⟨hp⟩
  have hd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact IsPGroup.iff_card.2 ⟨0, by rw [Nat.card_zpowers, h1]; simp⟩
  · exact IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, h1]; simp⟩

theorem mt_rank_cent (h43 : Lemma43) (i1021 : Input10_21) {m : ℕ} (hS : GLStanding G m 5)
    (hm : m = 4) {B : Subgroup G} (hB : IsBOneMax 5 B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {L : Subgroup G} (hL : IsMT b L) {a : G} (ha : a ∈ cBarB 5 B L) :
    ∃ K : Subgroup G, K ≤ L ⊓ Cb a ∧ 5 ≤ CFSG.Open.pRank 3 K := by
  have hp : Nat.Prime 5 := by norm_num
  obtain ⟨-, hAB, -, -, -⟩ := mt_structure h43 hS hm hB hb hb1 hL
  have haB : a ∈ B := hAB ha
  have hap : a ^ 5 = 1 := hB.1.1.2 a haB
  have hPp : IsPGroup 5 (Subgroup.zpowers a) := isPGroup_zpowers_g6 hp hap
  have hPA : Subgroup.zpowers a ≤ cBarB 5 B L := (Subgroup.zpowers_le).2 ha
  have hPN : Subgroup.zpowers a ≤ Subgroup.normalizer (L : Set G) := fun x hx => (hPA hx).2.1
  have htriv : ∀ x ∈ Subgroup.zpowers a, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf 5 L :=
    fun x hx => cBarB_triv_g6 (hPA hx)
  obtain ⟨hcomp, ⟨e⟩⟩ := layer_cent hp hPp hPN htriv (isQuasisimple_barOf_mt hL)
  have hKL : GLAPLayer 5 (L ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set G)) ≤
      L ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set G) := sSup_le fun _ hX => hX.1
  refine ⟨_, hKL.trans (inf_le_inf_left L (Subgroup.centralizer_le ?_)), ?_⟩
  · exact Set.singleton_subset_iff.2 (Subgroup.mem_zpowers a)
  · exact i1021.1 G _ (glaPLayer_eq_of_glaPComponent hp hcomp)
      (isFiTwentyTwo_of_equiv e.symm hL.2)

theorem exists_twoLocal_rank_five (h43 : Lemma43) (i1021 : Input10_21) {m : ℕ}
    (hS : GLStanding G m 5) (hm : m = 4) {B : Subgroup G} (hB : IsBOneMax 5 B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G} (hL : IsMT b L) :
    ∃ N : Subgroup G, IsTwoLocal N ∧ 5 ≤ CFSG.Open.pRank 3 N := by
  have hp : Nat.Prime 5 := by norm_num
  subst hm
  obtain ⟨-, hAB, -, -, -⟩ := mt_structure h43 hS rfl hB hb hb1 hL
  obtain ⟨-, -, ⟨N, hN, hBN, hcov⟩, -⟩ := h43 G 4 5 hS rfl B hB b hb hb1 L hL.1 hL.2
  have hPel : IsElemAbelian 5 (cBarB 5 B L) := isElemAbelian_mono hB.1.1 hAB
  have hPp : IsPGroup 5 (cBarB 5 B L) := GL83.isPGroup_of_isElemAbelian hPel
  have hPN : cBarB 5 B L ≤ Subgroup.normalizer (L : Set G) := fun x hx => hx.2.1
  obtain ⟨hcomp, ⟨e⟩⟩ := layer_cent hp hPp hPN (fun x hx => cBarB_triv_g6 hx)
    (isQuasisimple_barOf_mt hL)
  have hq : CFSG.Open.IsQuasisimple (barOf 5 (GLAPLayer 5
      (L ⊓ Subgroup.centralizer (cBarB 5 B L : Set G)))) :=
    isQuasisimple_barOf_of_glaPComponent hp hcomp
  obtain ⟨K, hKle, hK, ⟨eK⟩⟩ := exists_component_of_cover hp
    (inf_le_right : N ⊓ GLAPLayer 5 (L ⊓ Subgroup.centralizer (cBarB 5 B L : Set G)) ≤ _)
    hcov hq
  have hFi : IsFiTwentyTwo (barOf 5 K) := isFiTwentyTwo_of_equiv (e.symm.trans eK.symm) hL.2
  have h5 : 5 ≤ CFSG.Open.pRank 3 K :=
    i1021.1 G K (glaPLayer_eq_of_glaPComponent hp hK) hFi
  exact ⟨N, hN, h5.trans (CFSG.SectionRank.pRank_mono (by norm_num) (hKle.trans inf_le_left))⟩

theorem exists_hasM (h43 : Lemma43) (i1021 : Input10_21) (i247 : Input24_7) {m : ℕ}
    (hS : GLStanding G m 5) (hm : m = 4) {B : Subgroup G} (hB : IsBOneMax 5 B)
    {M : Subgroup G} (P : Sylow 3 G) (hP : GLAWeakCore 3 (P : Subgroup G) ≤ M)
    {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G} (hL : IsMT b L) :
    ∃ M' : Subgroup G, HasM M b M' := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hp5 : Nat.Prime 5 := by norm_num
  have hr5 := mt_rank i1021 hL
  obtain ⟨E, hEL, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp3.one_lt L
  have hEp : IsPGroup 3 E := GL83.isPGroup_of_isElemAbelian hE
  obtain ⟨Q, hEQ, hQL, hQp, hQcard⟩ := exists_sylow_ge hp3 hEL hEp
  have hQr : 3 ≤ CFSG.Open.pRank 3 Q :=
    (by norm_num : 3 ≤ 5).trans (hr5.trans (CFSG.SectionRank.le_pRank hp3.one_lt hEQ hE hEcard))
  obtain ⟨M', ⟨g, hg⟩, hQM', hWM'⟩ := exists_conj_ge P hP hQp hQr
  have hLK : GLAPLayer 5 L = L := glaPLayer_eq_of_glaPComponent hp5 hL.1
  have hLne : L ≠ ⊤ := fun h => centralizer_singleton_ne_top hS hb1 (top_le_iff.1 (h ▸ hL.1.1))
  have hLKG : CFSG.Open.IsKGroup ↥L := isKGroup_of_isKProper hS.kProper hLne
  have h247 := i247 G L Q hLKG hLK hL.2 hQL hQp hQcard
  have hLM' : L ≤ M' := h247.trans ((weakCoreIn_le_glaWeakCore 3 Q L).trans hWM')
  have hnorm := mt_normal h43 hS hm hB hb hb1 hL
  have hFr := le_sup_normalizer_of_sylow hp3 hL.1.1 hnorm hQL hQp hQcard
  have hNQ : Subgroup.normalizer (Q : Set G) ≤ M' := (normalizer_le_glaWeakCore hQr).trans hWM'
  exact ⟨M', ⟨g, hg⟩, hFr.trans (sup_le hLM' hNQ)⟩

end G6

section G7

variable {G : Type} [Group G] [Finite G]

theorem mt_of_mem_cBarB (h43 : Lemma43) {m : ℕ} (hS : GLStanding G m 5)
    (hm : m = 4) {B : Subgroup G} (hB : IsBOneMax 5 B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {L : Subgroup G} (hL : IsMT b L) {a : G} (ha : a ∈ cBarB 5 B L) (ha1 : a ≠ 1) :
    ∃ K : Subgroup G, IsMT a K ∧ cBarB 5 B L ≤ cBarB 5 B K := by
  have hp : Nat.Prime 5 := by norm_num
  subst hm
  obtain ⟨-, hAB, -, -, -⟩ := mt_structure h43 hS rfl hB hb hb1 hL
  have haB : a ∈ B := hAB ha
  set A := cBarB 5 B L with hA
  set J := GLAPLayer 5 (L ⊓ Subgroup.centralizer (A : Set G)) with hJ
  set Ka := ⨆ g ∈ GLAPLayer 5 (Cb a), GLBConj g J with hKa
  obtain ⟨-, hii, -, -⟩ := h43 G 4 5 hS rfl B hB b hb hb1 L hL.1 hL.2
  obtain ⟨hKcomp, hcov⟩ := hii a ha ha1
  have hPel : IsElemAbelian 5 A := isElemAbelian_mono hB.1.1 hAB
  have hPp : IsPGroup 5 A := GL83.isPGroup_of_isElemAbelian hPel
  have hPN : A ≤ Subgroup.normalizer (L : Set G) := fun x hx => hx.2.1
  obtain ⟨hcomp, ⟨e⟩⟩ := layer_cent hp hPp hPN (fun x hx => cBarB_triv_g6 hx)
    (isQuasisimple_barOf_mt hL)
  have hJKa : J ≤ Ka := by
    have h1 : GLBConj 1 J ≤ Ka :=
      le_iSup₂_of_le (f := fun g (_ : g ∈ GLAPLayer 5 (Cb a)) => GLBConj g J) 1
        (Subgroup.one_mem _) le_rfl
    rwa [gLBConj_one] at h1
  have hJLA : J ≤ L ⊓ Subgroup.centralizer (A : Set G) := sSup_le fun _ hX => hX.1
  obtain ⟨-, ⟨e2⟩⟩ := barOf_equiv_of_cover hp hJKa hcov
  have hFi : IsFiTwentyTwo (barOf 5 Ka) := isFiTwentyTwo_of_equiv (e.symm.trans e2) hL.2
  have hMT : IsMT a Ka := ⟨hKcomp, hFi⟩
  refine ⟨Ka, hMT, ?_⟩
  obtain ⟨hBN, -, -, -, -⟩ := mt_structure h43 hS rfl hB haB ha1 hMT
  have hNU : ∀ x ∈ Subgroup.normalizer (Ka : Set G),
      x ∈ Subgroup.normalizer (GLAPPrimeCoreOf 5 Ka : Set G) := by
    intro x h1
    rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
    rw [← glaPPrimeCoreOf_gLBConj, h1]
  intro α hα
  have hαB : α ∈ B := hAB hα
  show α ∈ B ⊓ centralizerQuot Ka (GLAPPrimeCoreOf 5 Ka)
  refine ⟨hαB, hBN hαB, hNU α (hBN hαB), fun k hk => ?_⟩
  obtain ⟨j, hj, r, hr, hjr⟩ := mem_sup_iff_mul_g1b
    (hJKa.trans (le_normalizer_glaPPrimeCoreOf 5 Ka)) (hcov hk)
  have hjc : α * j = j * α := Subgroup.mem_centralizer_iff.1 (hJLA hj).2 α hα
  have hjα : α * j * α⁻¹ = j := by rw [hjc]; group
  have e1 : α * j⁻¹ * α⁻¹ = j⁻¹ := by
    calc α * j⁻¹ * α⁻¹ = (α * j * α⁻¹)⁻¹ := by group
      _ = j⁻¹ := by rw [hjα]
  have hr' : α * r * α⁻¹ ∈ GLAPPrimeCoreOf 5 Ka :=
    (Subgroup.mem_normalizer_iff.1 (hNU α (hBN hαB)) r).1 hr
  have hr'' : α * r⁻¹ * α⁻¹ ∈ GLAPPrimeCoreOf 5 Ka := by
    have := (GLAPPrimeCoreOf 5 Ka).inv_mem hr'
    simpa [mul_assoc] using this
  have hkeq : k * α * k⁻¹ * α⁻¹ =
      j * (r * (α * r⁻¹ * α⁻¹)) * j⁻¹ := by
    have h2 : (j * r) * α * (j * r)⁻¹ * α⁻¹ =
        (j * (r * (α * r⁻¹ * α⁻¹))) * (α * j⁻¹ * α⁻¹) := by group
    rw [e1, hjr] at h2
    exact h2
  rw [hkeq]
  have hmem : r * (α * r⁻¹ * α⁻¹) ∈ GLAPPrimeCoreOf 5 Ka :=
    (GLAPPrimeCoreOf 5 Ka).mul_mem hr hr''
  have := (Subgroup.mem_normalizer_iff.1
    (le_normalizer_glaPPrimeCoreOf 5 Ka (hJKa hj)) _).1 hmem
  simpa [mul_assoc] using this

theorem cBarB_eq_of_le (h43 : Lemma43) {m : ℕ} (hS : GLStanding G m 5) (hm : m = 4)
    {B : Subgroup G} (hB : IsBOneMax 5 B) {b a : G} (hb : b ∈ B) (hb1 : b ≠ 1) (ha : a ∈ B)
    (ha1 : a ≠ 1) {L K : Subgroup G} (hL : IsMT b L) (hK : IsMT a K)
    (hle : cBarB 5 B L ≤ cBarB 5 B K) : cBarB 5 B L = cBarB 5 B K := by
  obtain ⟨-, -, hLc, -, -⟩ := mt_structure h43 hS hm hB hb hb1 hL
  obtain ⟨-, -, hKc, -, -⟩ := mt_structure h43 hS hm hB ha ha1 hK
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hLc, hKc])

theorem inf_cBarB_eq_bot (h43 : Lemma43) {m : ℕ} (hS : GLStanding G m 5)
    (hm : m = 4) {B : Subgroup G} (hB : IsBOneMax 5 B) {b₁ b₂ : G} (hb₁ : b₁ ∈ B)
    (hb₁1 : b₁ ≠ 1) (hb₂ : b₂ ∈ B) (hb₂1 : b₂ ≠ 1) {L₁ L₂ : Subgroup G} (hL₁ : IsMT b₁ L₁)
    (hL₂ : IsMT b₂ L₂) (hn : b₂ ∉ cBarB 5 B L₁) : cBarB 5 B L₁ ⊓ cBarB 5 B L₂ = ⊥ := by
  by_contra hne
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨hxA₁, hxA₂⟩ := hx
  obtain ⟨-, hA₁B, -, -, -⟩ := mt_structure h43 hS hm hB hb₁ hb₁1 hL₁
  have hxB : x ∈ B := hA₁B hxA₁
  obtain ⟨K₁, hK₁, hle₁⟩ := mt_of_mem_cBarB h43 hS hm hB hb₁ hb₁1 hL₁ hxA₁ hx1'
  obtain ⟨K₂, hK₂, hle₂⟩ := mt_of_mem_cBarB h43 hS hm hB hb₂ hb₂1 hL₂ hxA₂ hx1'
  have hK : K₁ = K₂ := mt_unique h43 hS hm hB hxB hx1' hK₁ hK₂
  subst hK
  have e₁ := cBarB_eq_of_le h43 hS hm hB hb₁ hb₁1 hxB hx1' hL₁ hK₁ hle₁
  have e₂ := cBarB_eq_of_le h43 hS hm hB hb₂ hb₂1 hxB hx1' hL₂ hK₁ hle₂
  have hb₂A₂ : b₂ ∈ cBarB 5 B L₂ := mem_cBarB_of_le_centralizer hb₂ hL₂.1.1
  rw [e₂, ← e₁] at hb₂A₂
  exact hn hb₂A₂

end G7

section G8

variable {G : Type} [Group G] [Finite G]

private theorem barOf_equiv_of_surj_simple_g8 {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {T : Subgroup G} {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hpS : p ∣ Nat.card S) (f : ↥T →* S) (hf : Function.Surjective f)
    (hker : ¬ p ∣ Nat.card f.ker) :
    GLAPPrimeCore p ↥T = f.ker ∧ Nonempty (barOf p T ≃* S) := by
  have heq : GLAPPrimeCore p ↥T = f.ker := by
    apply le_antisymm
    · set N := (GLAPPrimeCore p ↥T).map f with hN
      have hNn : N.Normal := (GLAPPrimeCore.normal p ↥T).map f hf
      have hNc : Nat.Coprime p (Nat.card N) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (GLAPPrimeCore p ↥T) f)
          (coprime_card_gLAPPrimeCore_aux p ↥T)
      have := hNn
      rcases hS.eq_bot_or_eq_top_of_normal N with h0 | h1
      · intro x hx
        have h2 : f x ∈ N := ⟨x, hx, rfl⟩
        rw [h0, Subgroup.mem_bot] at h2
        exact h2
      · exfalso
        have h3 : Nat.card N = Nat.card S := by rw [h1, Subgroup.card_top]
        rw [← h3] at hpS
        exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hNc hpS)
    · exact le_sSup ⟨MonoidHom.normal_ker f, (Nat.Prime.coprime_iff_not_dvd hp).2 hker⟩
  exact ⟨heq, ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩⟩

theorem mt_rank_four (h43 : Lemma43) (i1021 : Input10_21) (i242 : Input24_2) (iD4 : InputD4Two) {m : ℕ}
    (hS : GLStanding G m 5) (hm : m = 4) {B : Subgroup G} (hB : IsBOneMax 5 B) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ B) (hb₁1 : b₁ ≠ 1) (hb₂ : b₂ ∈ B) (hb₂1 : b₂ ≠ 1) {L₁ L₂ : Subgroup G}
    (hL₁ : IsMT b₁ L₁) (hL₂ : IsMT b₂ L₂) (hdisj : cBarB 5 B L₁ ⊓ cBarB 5 B L₂ = ⊥) :
    ∃ K : Subgroup G, 4 ≤ CFSG.Open.pRank 3 K ∧
      K ≤ ⨆ a ∈ cBarB 5 B L₁, ⨆ (_ : a ≠ 1), (L₂ ⊓ Cb a) := by
  have hp : Nat.Prime 5 := by norm_num
  subst hm
  obtain ⟨hBN₁, hA₁B, hA₁c, -, -⟩ := mt_structure h43 hS rfl hB hb₁ hb₁1 hL₁
  obtain ⟨hBN₂, hA₂B, hA₂c, -, -⟩ := mt_structure h43 hS rfl hB hb₂ hb₂1 hL₂
  set A₁ := cBarB 5 B L₁ with hA₁
  set N₂ := Subgroup.normalizer (L₂ : Set G) with hN₂
  set R₂ := GLAPPrimeCoreOf 5 L₂ with hR₂
  have hA₁N : A₁ ≤ N₂ := hA₁B.trans hBN₂
  have hA₁el : IsElemAbelian 5 A₁ := isElemAbelian_mono hB.1.1 hA₁B
  set Ā : Subgroup (MulAut (barOf 5 L₂)) := (A₁.subgroupOf N₂).map (barAut 5 L₂) with hĀ
  have hĀel : IsElemAbelian 5 Ā :=
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hA₁el N₂) _
  have hinj : Function.Injective ((barAut 5 L₂).comp (A₁.subgroupOf N₂).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    have hker' : barAut 5 L₂ x = 1 := hker
    have hxA₂ : (x : G) ∈ cBarB 5 B L₂ :=
      (mem_cBarB_iff).2 ⟨hA₁B hx, x.2, hker'⟩
    have : (x : G) ∈ A₁ ⊓ cBarB 5 B L₂ := ⟨hx, hxA₂⟩
    rw [hdisj] at this
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext (Subtype.ext this)
  have hĀcard : Nat.card Ā = 5 ^ 2 := by
    have h1 : Ā = ((barAut 5 L₂).comp (A₁.subgroupOf N₂).subtype).range := by
      rw [hĀ, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁N).toEquiv, hA₁c]
  obtain ⟨Y, hYle, hYD4⟩ := i242 (barOf 5 L₂) hL₂.2 Ā hĀel hĀcard
  obtain ⟨hYqs, hYsimple, hY5⟩ := iD4 ↥Y hYD4
  set X : Subgroup G := ⨆ a ∈ A₁, ⨆ (_ : a ≠ 1), (L₂ ⊓ Cb a) with hX
  have hXL : X ≤ L₂ := iSup₂_le fun a _ => iSup_le fun _ => inf_le_left
  have hYX : Y ≤ (X.subgroupOf L₂).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥L₂)) := by
    refine hYle.trans (iSup₂_le fun φ hφ => iSup_le fun hφ1 => ?_)
    obtain ⟨⟨a, haN⟩, haA, rfl⟩ := hφ
    have haA' : a ∈ A₁ := haA
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hφ1 (map_one _)
    have hord : IsPGroup 5 (Subgroup.zpowers a) :=
      isPGroup_zpowers_g6 hp (hB.1.1.2 a (hA₁B haA'))
    refine (fixSub_barAut_le_map hp haN hord).trans (Subgroup.map_mono ?_)
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have hle : L₂ ⊓ Cb a ≤ X := le_iSup₂_of_le a haA' (le_iSup (fun _ : a ≠ 1 => L₂ ⊓ Cb a) ha1)
    exact hle hz
  set T' : Subgroup G := (Y.comap (QuotientGroup.mk' (GLAPPrimeCore 5 ↥L₂))).map L₂.subtype
    with hT'
  have hT'L : T' ≤ L₂ := Subgroup.map_subtype_le _
  have hmemT' : ∀ t : G, t ∈ T' ↔ ∃ l : ↥L₂, QuotientGroup.mk' (GLAPPrimeCore 5 ↥L₂) l ∈ Y ∧
      (l : G) = t := by
    intro t
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, rfl⟩
  have hRT : R₂ ≤ T' := by
    rintro r ⟨r', hr', rfl⟩
    refine (hmemT' _).2 ⟨r', ?_, rfl⟩
    have : QuotientGroup.mk' (GLAPPrimeCore 5 ↥L₂) r' = 1 := (QuotientGroup.eq_one_iff r').2 hr'
    rw [this]
    exact Y.one_mem
  have hmk : ∀ t : ↥T', QuotientGroup.mk' (GLAPPrimeCore 5 ↥L₂) (Subgroup.inclusion hT'L t) ∈ Y := by
    intro t
    obtain ⟨l, hl, hlt⟩ := (hmemT' _).1 t.2
    have : Subgroup.inclusion hT'L t = l := Subtype.ext hlt.symm
    rw [this]
    exact hl
  let f : ↥T' →* ↥Y :=
    MonoidHom.codRestrict ((QuotientGroup.mk' (GLAPPrimeCore 5 ↥L₂)).comp
      (Subgroup.inclusion hT'L)) Y hmk
  have hfval : ∀ t : ↥T', ((f t : ↥Y) : barOf 5 L₂) =
      QuotientGroup.mk' (GLAPPrimeCore 5 ↥L₂) (Subgroup.inclusion hT'L t) := fun t => rfl
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 5 ↥L₂) y.1
    refine ⟨⟨(l : G), (hmemT' _).2 ⟨l, ?_, rfl⟩⟩, ?_⟩
    · rw [hl]; exact y.2
    · apply Subtype.ext
      rw [hfval]
      exact hl
  have hkerR : ∀ t : ↥T', t ∈ f.ker → (t : G) ∈ R₂ := by
    intro t ht
    have h1 : ((f t : ↥Y) : barOf 5 L₂) = 1 := by rw [MonoidHom.mem_ker.1 ht]; rfl
    rw [hfval] at h1
    exact ⟨Subgroup.inclusion hT'L t, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have hkercard : ¬ 5 ∣ Nat.card f.ker := by
    have hle : f.ker.map T'.subtype ≤ R₂ := by
      rintro _ ⟨t, ht, rfl⟩
      exact hkerR t ht
    have h1 : Nat.card (f.ker.map T'.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective T'.subtype_injective
    intro hd
    exact not_dvd_card_glaPPrimeCoreOf hp L₂ (hd.trans (h1 ▸ Subgroup.card_dvd_of_le hle))
  have : Finite ↥Y := inferInstance
  obtain ⟨hOT, ⟨e'⟩⟩ := barOf_equiv_of_surj_simple_g8 hp hYsimple hY5 f hf hkercard
  have hqT' : CFSG.Open.IsQuasisimple (barOf 5 T') :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e'.symm hYqs
  have hRO : R₂ ≤ GLAPPrimeCoreOf 5 T' := by
    intro r hr
    have hrT := hRT hr
    refine ⟨⟨r, hrT⟩, ?_, rfl⟩
    have hmem : (⟨r, hrT⟩ : ↥T') ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hfval]
      show QuotientGroup.mk' (GLAPPrimeCore 5 ↥L₂) (Subgroup.inclusion hT'L ⟨r, hrT⟩) = 1
      refine (QuotientGroup.eq_one_iff _).2 ?_
      obtain ⟨r', hr', hrr⟩ := hr
      have : Subgroup.inclusion hT'L ⟨r, hrT⟩ = r' := Subtype.ext hrr.symm
      rw [this]
      exact hr'
    show (⟨r, hrT⟩ : ↥T') ∈ GLAPPrimeCore 5 ↥T'
    rw [hOT]
    exact hmem
  have hcov : T' ≤ (X ⊓ T') ⊔ GLAPPrimeCoreOf 5 T' := by
    intro t ht
    obtain ⟨l, hl, hlt⟩ := (hmemT' t).1 ht
    obtain ⟨z, hz, hzl⟩ := hYX hl
    have hzX : (z : G) ∈ X := (Subgroup.mem_subgroupOf).1 hz
    have hzT : (z : G) ∈ T' := (hmemT' _).2 ⟨z, by rw [hzl]; exact hl, rfl⟩
    have hrt : (z : G)⁻¹ * t ∈ R₂ := by
      refine ⟨z⁻¹ * l, (QuotientGroup.eq).1 hzl, ?_⟩
      simp [hlt]
    have : t = (z : G) * ((z : G)⁻¹ * t) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ⟨hzX, hzT⟩ (hRO hrt)
  obtain ⟨K, hKX₀, hKcomp, ⟨eK⟩⟩ := exists_component_of_cover hp
    (inf_le_right : X ⊓ T' ≤ T') hcov hqT'
  have hD4 : IsDFourTwo (barOf 5 K) := isDFourTwo_of_equiv (e'.symm.trans eK.symm) hYD4
  exact ⟨K, i1021.2 G K (glaPLayer_eq_of_glaPComponent hp hKcomp) hD4, hKX₀.trans inf_le_left⟩

end G8


section G9

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_mem_inf {B Q A : Subgroup G} (hB : IsElemAbelian 5 B)
    (hBcard : Nat.card B = 5 ^ 4) (hQB : Q ≤ B) (hQ3 : 3 ≤ CFSG.Open.pRank 5 Q)
    (hAB : A ≤ B) (hAcard : Nat.card A = 5 ^ 2) : ∃ x ∈ Q ⊓ A, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hinf : Q ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hcon x hx)
  obtain ⟨E, hEQ, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) Q
  have hQcard : 5 ^ 3 ≤ Nat.card Q := by
    calc 5 ^ 3 ≤ 5 ^ (CFSG.Open.pRank 5 Q) := Nat.pow_le_pow_right (by norm_num) hQ3
      _ = Nat.card E := hEcard.symm
      _ ≤ Nat.card Q := Subgroup.card_le_of_le hEQ
  have hcomm : ∀ q ∈ Q, ∀ a ∈ A, q * a = a * q := fun q hq a ha =>
    elemAbelian_comm hB (hQB hq) (hAB ha)
  have h1 := card_sup_eq_mul_of_commute hcomm hinf
  have h2 : Nat.card ↥(Q ⊔ A) ≤ Nat.card B := Subgroup.card_le_of_le (sup_le hQB hAB)
  rw [h1, hAcard, hBcard] at h2
  have h3 := Nat.mul_le_mul_right (5 ^ 2) hQcard
  norm_num at h3 h2
  omega

private theorem normalizer_le_of_hyperplane_g9 {G : Type} [Group G] [Finite G] {m p : ℕ}
    (hS : GLStanding G m p) {B M₀ : Subgroup G} (hB : IsBOneMax p B)
    (hΓ : GLBCore p 3 B ≤ M₀) {K : Subgroup G} (hKB : K ≤ B)
    (hidx : (K.subgroupOf B).index = p) : Subgroup.normalizer (K : Set G) ≤ M₀ := by
  have hp := hS.prime
  have hm4 := hS.four_le
  have hB' : Nat.card B = p ^ ((m - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact hS.card_eq hB
  have hKcard := card_eq_of_index_eq hp hKB hidx hB'
  have hKel : IsElemAbelian p K := isElemAbelian_mono hB.1.1 hKB
  have h3 : 3 ≤ CFSG.Open.pRank p K := by
    have := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hKel hKcard
    omega
  exact (le_sSup ⟨K, hKB, h3, rfl⟩ : Subgroup.normalizer (K : Set G) ≤ GLBCore p 3 B).trans hΓ

private theorem le_of_normalized_g9 {G : Type} [Group G] [Finite G] {m p : ℕ}
    (hS : GLStanding G m p) {B M₀ : Subgroup G} (hB : IsBOneMax p B)
    (hΓ : GLBCore p 3 B ≤ M₀) {Y : Subgroup G} (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hY : ¬ p ∣ Nat.card Y) : Y ≤ M₀ := by
  have : Fact p.Prime := ⟨hS.prime⟩
  have := hS.nontrivial hB
  refine (le_iSup_inf_centralizer_hyperplane hB.1.1 hBY hY).trans (iSup₂_le fun K hK => ?_)
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_of_hyperplane_g9 hS hB hΓ hK.1 hK.2))

theorem isPreUniquenessSubgroup_of (h31 : Lemma31) (hS : GLStanding G 4 5) {B : Subgroup G}
    (hB : IsBOneMax 5 B) {M₀ : Subgroup G} (hM₀ : IsTwoLocal M₀) (hΓ : GLBCore 5 3 B ≤ M₀)
    (hC : ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G, IsMT b L → L ≤ M₀) :
    IsPreUniquenessSubgroup 5 B M₀ := by
  have hp : Nat.Prime 5 := by norm_num
  have hBel : IsElemAbelian 5 B := hB.1.1
  refine ⟨?_, hΓ, even_card_glaPPrimeCoreOf_of_isTwoLocal hp (by norm_num) hM₀⟩
  have hsc : IsSCp 5 ⊤ B := isSCp_of_isBOneMax hS hB
  have hBmax : GLAIsBmax 5 B := hB.1
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
  have hBCb : B ≤ Cb b := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hBel hx hb)
  have hBCB : B ≤ Subgroup.centralizer (B : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => elemAbelian_comm hBel hy hx
  refine sup_le (sup_le ?_ ?_) ?_
  ·
    rw [lambdaOf_eq_psiOf_sup_lambdaMOf_of_five h31 hS hBmax hsc hb hb1]
    refine sup_le (sSup_le fun L hL => ?_) (sSup_le fun L hL => ?_)
    ·
      have hG1 : IsInGOne 5 B L := hL.2.2
      have hLB : L ≤ bClosure B L := by
        have h1 : GLBConj 1 L ≤ bClosure B L :=
          le_iSup₂_of_le (f := fun g (_ : g ∈ B) => GLBConj g L) 1 B.one_mem le_rfl
        rwa [gLBConj_one] at h1
      have h2 : bClosure B L ≤ coreIn 5 3 B (bClosure B L) := hG1.le
      have h3 : coreIn 5 3 B (bClosure B L) ≤ GLBCore 5 3 B :=
        iSup₂_le fun Q hQ => inf_le_right.trans (le_sSup ⟨Q, hQ.1, hQ.2, rfl⟩)
      exact hLB.trans (h2.trans (h3.trans hΓ))
    · exact hC b hb hb1 L ⟨hL.1, hL.2.2.2.2⟩
  · exact le_of_normalized_g9 hS hB hΓ (hBCb.trans (le_normalizer_glaPPrimeCoreOf 5 _))
      (not_dvd_card_glaPPrimeCoreOf hp _)
  · exact le_of_normalized_g9 hS hB hΓ (hBCB.trans (le_normalizer_glaPPrimeCoreOf 5 _))
      (not_dvd_card_glaPPrimeCoreOf hp _)

theorem caseA (hI : Inputs) {B M : Subgroup G} (c : Ctx G B M) {b₁ b₂ : G} (hb₁ : b₁ ∈ B)
    (hb₁1 : b₁ ≠ 1) {L₁ : Subgroup G} (hL₁ : IsMT b₁ L₁) (hb₂ : b₂ ∈ cBarB 5 B L₁)
    {M₁ M₂ : Subgroup G} (hM₁ : HasM M b₁ M₁) (hM₂ : HasM M b₂ M₂) : M₁ = M₂ := by
  obtain ⟨K, hK, hr⟩ := mt_rank_cent hI.h43 hI.i1021 c.S rfl c.B1 hb₁ hb₁1 hL₁ hb₂
  obtain ⟨P, hP⟩ := c.W
  refine uniq_conj hI.iU c.S c.β c.hM P hP hM₁.1 hM₂.1 ?_
  refine (by norm_num : 3 ≤ 5).trans (hr.trans (CFSG.SectionRank.pRank_mono (by norm_num) ?_))
  exact le_inf ((hK.trans inf_le_left).trans (hL₁.1.1.trans hM₁.2))
    (hK.trans (inf_le_right.trans hM₂.2))

theorem claim (hI : Inputs) {B M : Subgroup G} (c : Ctx G B M) {b₁ b₂ : G} (hb₁ : b₁ ∈ B)
    (hb₁1 : b₁ ≠ 1) (hb₂ : b₂ ∈ B) (hb₂1 : b₂ ≠ 1) {L₁ L₂ : Subgroup G} (hL₁ : IsMT b₁ L₁)
    (hL₂ : IsMT b₂ L₂) {M₁ M₂ : Subgroup G} (hM₁ : HasM M b₁ M₁) (hM₂ : HasM M b₂ M₂) :
    M₁ = M₂ := by
  by_cases hA : b₂ ∈ cBarB 5 B L₁
  · exact caseA hI c hb₁ hb₁1 hL₁ hA hM₁ hM₂
  · have hdisj := inf_cBarB_eq_bot hI.h43 c.S rfl c.B1 hb₁ hb₁1 hb₂ hb₂1 hL₁ hL₂ hA
    obtain ⟨K, hr4, hKX⟩ := mt_rank_four hI.h43 hI.i1021 hI.i242 hI.iD4 c.S rfl c.B1 hb₁ hb₁1 hb₂ hb₂1
      hL₁ hL₂ hdisj
    obtain ⟨P, hP⟩ := c.W
    refine uniq_conj hI.iU c.S c.β c.hM P hP hM₁.1 hM₂.1 ?_
    have hK1 : K ≤ M₁ := by
      refine hKX.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
      obtain ⟨Ka, hKa, -⟩ := mt_of_mem_cBarB hI.h43 c.S rfl c.B1 hb₁ hb₁1 hL₁ ha ha1
      have haB : a ∈ B := (mt_structure hI.h43 c.S rfl c.B1 hb₁ hb₁1 hL₁).2.1 ha
      obtain ⟨Ma, hMa⟩ := exists_hasM hI.h43 hI.i1021 hI.i247 c.S rfl c.B1 P hP haB ha1 hKa
      have h1 : M₁ = Ma := caseA hI c hb₁ hb₁1 hL₁ ha hM₁ hMa
      exact inf_le_right.trans (hMa.2.trans h1.symm.le)
    have hK2 : K ≤ M₂ :=
      hKX.trans (iSup₂_le fun a _ => iSup_le fun _ => inf_le_left.trans (hL₂.1.1.trans hM₂.2))
    exact (by norm_num : 3 ≤ 4).trans
      (hr4.trans (CFSG.SectionRank.pRank_mono (by norm_num) (le_inf hK1 hK2)))

theorem exists_M₀ (hI : Inputs) {B M : Subgroup G} (c : Ctx G B M) {b₀ : G} (hb₀ : b₀ ∈ B)
    (hb₀1 : b₀ ≠ 1) {L₀ : Subgroup G} (hL₀ : IsMT b₀ L₀) :
    ∃ M₀ : Subgroup G, (∃ g : G, M₀ = GLBConj g M) ∧
      ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G, IsMT b L → Cb b ≤ M₀ := by
  obtain ⟨P, hP⟩ := c.W
  obtain ⟨M₀, hM₀⟩ := exists_hasM hI.h43 hI.i1021 hI.i247 c.S rfl c.B1 P hP hb₀ hb₀1 hL₀
  refine ⟨M₀, hM₀.1, fun b hb hb1 L hL => ?_⟩
  obtain ⟨Mb, hMb⟩ := exists_hasM hI.h43 hI.i1021 hI.i247 c.S rfl c.B1 P hP hb hb1 hL
  have := claim hI c hb₀ hb₀1 hb hb1 hL₀ hL hM₀ hMb
  rw [this]
  exact hMb.2

theorem normalizer_le (hI : Inputs) {B M : Subgroup G} (c : Ctx G B M) {M₀ : Subgroup G}
    (hM₀ : ∃ g : G, M₀ = GLBConj g M)
    (hC : ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G, IsMT b L → Cb b ≤ M₀) {Q : Subgroup G}
    (hQB : Q ≤ B) {x : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1) {K : Subgroup G} (hK : IsMT x K) :
    Subgroup.normalizer (Q : Set G) ≤ M₀ := by
  intro g hg
  obtain ⟨P, hP⟩ := c.W
  have hmax : GLAIsMaxTwoLocal M₀ := by
    obtain ⟨g₀, rfl⟩ := hM₀
    exact isMaxTwoLocal_gLBConj c.hM g₀
  have hyQ : g * x * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg x).1 hxQ
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  have hKy := mt_conj hK g⁻¹
  rw [inv_inv] at hKy
  have hCy : Cb (g * x * g⁻¹) ≤ M₀ := hC _ (hQB hyQ) hy1 _ hKy
  have hcb : Cb (g * x * g⁻¹) = GLBConj g⁻¹ (Cb x) := by
    have := cb_conj x g⁻¹
    rwa [inv_inv] at this
  have hCx : Cb x ≤ M₀ := hC x (hQB hxQ) hx1 K hK
  have hCx' : Cb x ≤ GLBConj g M₀ := by
    have h1 : GLBConj g⁻¹ (Cb x) ≤ M₀ := hcb ▸ hCy
    have h2 := gLBConj_mono g h1
    rwa [gLBConj_gLBConj_inv] at h2
  have hr : 3 ≤ CFSG.Open.pRank 3 (M₀ ⊓ GLBConj g M₀) := by
    have h5 := mt_rank hI.i1021 hK
    refine (h5.trans' (by norm_num)).trans (CFSG.SectionRank.pRank_mono (by norm_num) ?_)
    exact le_inf (hK.1.1.trans hCx) (hK.1.1.trans hCx')
  have hconj : ∃ g' : G, GLBConj g M₀ = GLBConj g' M := by
    obtain ⟨g₀, rfl⟩ := hM₀
    exact ⟨g₀ * g, by rw [gLBConj_gLBConj]⟩
  have heq := uniq_conj hI.iU c.S c.β c.hM P hP hM₀ hconj hr
  exact mem_of_gLBConj_eq hmax heq.symm

end G9

end CaseThreeNs

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal CaseThreeNs in
theorem prop42CaseThree_of_inputs (h31 : Lemma31) (h43 : Lemma43) (h44 : Lemma44)
    (h22 : Coordinator.Prop22) (i1021 : Input10_21) (i247 : Input24_7) (i242 : Input24_2)
    (iU : InputUniq) (iD4 : InputD4Two) : Coordinator.Prop42CaseThree := by
  have hI : Inputs := ⟨h31, h43, h44, h22, i1021, i247, i242, iU, iD4⟩
  intro G _ _ m p hS hIII
  obtain ⟨rfl, hr4, hnc⟩ := hIII
  have hm : m = 4 := by have := hS.rank_eq; omega
  subst hm
  obtain ⟨B, hB0, -⟩ := h22 G 4 5 hS
  have hB1 : IsBOneMax 5 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by omega) hB0
  obtain ⟨b₀, hb₀, hb₀1, L₀, hL₀, hM₀⟩ := h44 G 4 5 hS rfl hnc B hB1
  have hMT : IsMT b₀ L₀ := ⟨hL₀, hM₀⟩
  obtain ⟨N, hN, hrN⟩ := exists_twoLocal_rank_five h43 i1021 hS rfl hB1 hb₀ hb₀1 hMT
  obtain ⟨M, hM, P, hP⟩ := exists_setting hS rfl hN hrN
  have c : Ctx G B M := ⟨hS, hB1, hM, ⟨P, hP⟩, three_mem_beta rfl hN hrN⟩
  obtain ⟨M₀, hM₀conj, hC⟩ := exists_M₀ hI c hb₀ hb₀1 hMT
  have hM₀max : GLAIsMaxTwoLocal M₀ := by
    obtain ⟨g₀, rfl⟩ := hM₀conj
    exact isMaxTwoLocal_gLBConj hM g₀
  have hΓ : GLBCore 5 3 B ≤ M₀ := by
    refine sSup_le ?_
    rintro _ ⟨Q, hQB, hQ3, rfl⟩
    have hB1' := hB1.1
    have hBcard : Nat.card B = 5 ^ 4 := hS.card_eq hB1
    obtain ⟨hBn, hAB, hAcard, -, -⟩ := mt_structure h43 hS rfl hB1 hb₀ hb₀1 hMT
    obtain ⟨x, hxQA, hx1⟩ := exists_ne_one_mem_inf hB1'.1 hBcard hQB hQ3 hAB hAcard
    obtain ⟨K, hK, -⟩ := mt_of_mem_cBarB h43 hS rfl hB1 hb₀ hb₀1 hMT hxQA.2 hx1
    exact normalizer_le hI c hM₀conj hC hQB hxQA.1 hx1 hK
  refine ⟨B, hB1, M₀, isPreUniquenessSubgroup_of h31 hS hB1 hM₀max.1 hΓ ?_⟩
  intro b hb hb1 L hL
  exact hL.1.1.trans (hC b hb hb1 L hL)

end CFSG.HardMathSupport.Solomon.LocalBalance
