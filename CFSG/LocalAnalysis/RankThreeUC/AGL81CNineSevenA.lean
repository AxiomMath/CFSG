module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.ThompsonAxBFaithful
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduced
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRNoX
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec4.T444.Statement
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem centralizes_of_hyperplane {p : ℕ} [Fact p.Prime] {P D : Subgroup X} [P.Normal]
    (hP : IsPGroup p P) (hD : IsPGroup p D) {a : X} (ha : Nat.Coprime (orderOf a) p)
    (haD : a ∈ centralizer (D : Set X))
    (hfix : ∀ c ∈ P ⊓ centralizer (D : Set X), a * c = c * a) :
    ∀ x ∈ P, a * x = x * a := by
  let φ : X →* MulAut ↥P := MulAut.conjNormal
  have hφ : ∀ (g : X) (w : ↥P), ((φ g w : ↥P) : X) = g * (w : X) * g⁻¹ := fun g w => rfl
  have hDp : IsPGroup p (D.map φ) := hD.map φ
  have hb : φ a = 1 := by
    refine CFSG.GroupTheory.eq_one_of_forall_fixed_of_coprime (p := p) hP hDp
      (ha.coprime_dvd_left (orderOf_map_dvd φ a)) ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact mem_centralizer_iff.mp haD d hd
    · intro w hw
      have hwc : (w : X) ∈ centralizer (D : Set X) := by
        refine mem_centralizer_iff.mpr fun d hd => ?_
        have h1 := congrArg Subtype.val (hw (φ d) ⟨d, hd, rfl⟩)
        rw [hφ] at h1
        exact mul_inv_eq_iff_eq_mul.mp h1
      refine Subtype.ext ?_
      rw [hφ]
      exact mul_inv_eq_iff_eq_mul.mpr (hfix w ⟨w.2, hwc⟩)
  intro x hx
  have h1 := congrArg (fun f : MulAut ↥P => ((f ⟨x, hx⟩ : ↥P) : X)) hb
  simp only [hφ, MulAut.one_apply] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem le_centralizer_of_hyperplanes {p : ℕ} [Fact p.Prime] {E S P : Subgroup X} [P.Normal]
    (hE : CFSG.Open.IsElemAbelian p E) [Nontrivial E] (hS : ¬ p ∣ Nat.card S)
    (hES : E ≤ normalizer (S : Set X)) (hP : IsPGroup p P)
    (h : ∀ D : Subgroup X, D ≤ E → (D.subgroupOf E).index = p →
      ∀ a ∈ S ⊓ centralizer (D : Set X), ∀ c ∈ P ⊓ centralizer (D : Set X), a * c = c * a) :
    S ≤ centralizer (P : Set X) := by
  classical
  letI : MulDistribMulAction E S := Subgroup.conjMulDistribMulActionOfLeNormalizer E S hES
  haveI : IsElementaryAbelian p E := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := E) (H := S) hS
  have hle : (⊤ : Subgroup S).map S.subtype ≤ centralizer (P : Set X) := by
    rw [← hgen]
    simp only [Subgroup.map_iSup]
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨s, hs, rfl⟩
    set D : Subgroup X := B.map E.subtype with hDdef
    have hDE : D ≤ E := Subgroup.map_subtype_le B
    have hDidx : (D.subgroupOf E).index = p := by
      rw [hDdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
      exact hB
    have hDp : IsPGroup p D := (hE.mono hDE).isPGroup
    have hsD : (s : X) ∈ centralizer (D : Set X) := by
      refine mem_centralizer_iff.mpr fun d hd => ?_
      obtain ⟨e, heB, rfl⟩ := Subgroup.mem_map.mp hd
      have h1 : (⟨e, heB⟩ : B) • s = s := hs ⟨e, heB⟩
      have h2 := congrArg Subtype.val h1
      have h3 : (((⟨e, heB⟩ : B) • s : S) : X) = (e : X) * (s : X) * (e : X)⁻¹ :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit E S hES e s
      rw [h3] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
    have hcop : Nat.Coprime (orderOf (s : X)) p := by
      have h1 : orderOf (s : X) ∣ Nat.card S := by
        rw [Subgroup.orderOf_coe s]
        exact orderOf_dvd_natCard s
      exact (Nat.Coprime.coprime_dvd_left h1
        (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hS).symm))
    have hcomm := centralizes_of_hyperplane hP hDp hcop hsD
      (fun c hc => h D hDE hDidx (s : X) ⟨s.2, hsD⟩ c hc)
    refine mem_centralizer_iff.mpr fun x hx => ?_
    exact (hcomm x hx).symm
  intro s hs
  exact hle ⟨⟨s, hs⟩, trivial, rfl⟩

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace NineCore

theorem normalizer_le_of_hyperplane (h : NineCore G M p Q H E k) {D : Subgroup G} (hDE : D ≤ E)
    (hcard : Nat.card E = p * Nat.card D) : normalizer (D : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨hk, hEQ, hE, hEc, hΓ⟩ := h.stdE
  have hk2 := h.k_two_le
  have hDc : Nat.card D = p ^ (k - 1) := by
    have h1 : p * Nat.card D = p * p ^ (k - 1) := by
      rw [← hcard, hEc, ← pow_succ']
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left h.prime.pos h1
  have hrk : k - 1 ≤ CFSG.Open.pRank p D :=
    CFSG.SectionRank.le_pRank h.prime.one_lt le_rfl (hE.mono hDE) hDc
  exact (gamma_le_iff (k - 1) p E M).mp hΓ D hDE hrk

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple (relPPrimeCore_eq_map)
open CFSG.AGLEmbedding (card_map_mk_of_isPGroup inf_eq_bot_of_isPGroup map_comap_inf_eq)
open CFSG.AGLEmbeddingD2 (normalizer_map_mk_le_map_inf)
open scoped commutatorElement

theorem starImg_le_centralizer_pCore (h : NineCore G M p Q H E k) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSY : S ≤ H ⊓ M)
    (hSn : ∀ y ∈ H ⊓ M, ∀ s ∈ S, y * s * y⁻¹ ∈ S) :
    starImg p H S ≤ Subgroup.centralizer
      ((CFSG.pCore p (↥H ⧸ primeComplementCore (G := ↥H) p) :
        Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) : Set (↥H ⧸ primeComplementCore
          (G := ↥H) p)) := by
  classical
  haveI hpf : Fact p.Prime := ⟨h.prime⟩
  have hp := h.prime
  set O : Subgroup ↥H := primeComplementCore (G := ↥H) p with hOdef
  haveI hOn : O.Normal := primeComplementCore_normal p
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπdef
  set Y' : Subgroup ↥H := (H ⊓ M).subgroupOf H with hY'
  have hEH : E ≤ H := h.stdE.2.1.trans h.Q_le_H
  have hEM : E ≤ M := h.stdE.2.1.trans h.Q_le_M
  have hk2 := h.k_two_le
  have hOM : O ≤ Y' := by
    intro n hn
    have h1 : (n : G) ∈ relPPrimeCore p H := by
      rw [relPPrimeCore_eq_map hp H]
      exact ⟨n, hn, rfl⟩
    exact mem_subgroupOf.mpr ⟨n.2, h.relPPrimeCore_le h1⟩
  set Ss : Subgroup (↥H ⧸ O) := starImg p H S with hSs
  set Ys : Subgroup (↥H ⧸ O) := Y'.map π with hYs
  have hYsN : Ys ≤ normalizer (Ss : Set (↥H ⧸ O)) := by
    have hfwd : ∀ y ∈ Y', ∀ s ∈ Ss, π y * s * (π y)⁻¹ ∈ Ss := by
      intro y hy s hs
      obtain ⟨t, ht, rfl⟩ := hs
      refine ⟨y * t * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have ht' : (t : G) ∈ S := ht
      have hy' : (y : G) ∈ H ⊓ M := hy
      exact hSn _ hy' _ ht'
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hfwd y hy s hs, fun hs => ?_⟩
    have := hfwd y⁻¹ (Y'.inv_mem hy) _ hs
    simpa [map_inv, mul_assoc] using this
  have hS_cop : ¬ p ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    rw [hn]
    intro hdvd
    exact h.ne_two ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hSs_cop : ¬ p ∣ Nat.card Ss := by
    intro hdvd
    apply hS_cop
    refine hdvd.trans ?_
    calc Nat.card Ss ∣ Nat.card (S.subgroupOf H) := Subgroup.card_map_dvd _ _
      _ = Nat.card S := Nat.card_congr (subgroupOfEquivOfLe (hSY.trans inf_le_left)).toEquiv
  set Eh : Subgroup ↥H := E.subgroupOf H with hEh
  set Es : Subgroup (↥H ⧸ O) := Eh.map π with hEs
  have hEhc : Nat.card Eh = Nat.card E := Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv
  have hEhp : IsPGroup p Eh := IsPGroup.of_card (n := k) (by rw [hEhc]; exact h.stdE.2.2.2.1)
  have hEsc : Nat.card Es = Nat.card E := by
    rw [hEs, card_map_mk_of_isPGroup hp O hO hEhp, hEhc]
  have hEel : IsElemAbelian p Es := (h.stdE.2.2.1.subgroupOf H).map π
  haveI : Nontrivial Es := by
    rw [← Finite.one_lt_card_iff_nontrivial, hEsc, h.stdE.2.2.2.1]
    exact one_lt_pow' hp.one_lt (by omega)
  have hEsY : Es ≤ Ys := by
    refine Subgroup.map_mono fun e he => ?_
    rw [mem_subgroupOf] at he ⊢
    exact ⟨e.2, hEM he⟩
  have hEsN : Es ≤ normalizer (Ss : Set (↥H ⧸ O)) := hEsY.trans hYsN
  have hCY : ∀ D : Subgroup (↥H ⧸ O), D ≤ Es → (D.subgroupOf Es).index = p →
      Subgroup.centralizer (D : Set (↥H ⧸ O)) ≤ Ys := by
    intro D hDE hDidx
    set Dh : Subgroup ↥H := D.comap π ⊓ Eh with hDh
    have hDmap : Dh.map π = D := map_comap_inf_eq π hDE
    have hDhEh : Dh ≤ Eh := inf_le_right
    have hDhp : IsPGroup p Dh := hEhp.to_le hDhEh
    have hcardD : Nat.card D = Nat.card Dh := by
      rw [← hDmap]
      exact card_map_mk_of_isPGroup hp O hO hDhp
    set DG : Subgroup G := Dh.map H.subtype with hDG
    have hDGE : DG ≤ E := by
      rintro _ ⟨d, hd, rfl⟩
      exact mem_subgroupOf.mp (hDhEh hd)
    have hcardDG : Nat.card DG = Nat.card Dh :=
      Subgroup.card_map_of_injective H.subtype_injective
    have hEDG : Nat.card E = p * Nat.card DG := by
      have h1 := Subgroup.card_mul_index (D.subgroupOf Es)
      have h2 : Nat.card (D.subgroupOf Es) = Nat.card D :=
        Nat.card_congr (subgroupOfEquivOfLe hDE).toEquiv
      rw [hDidx, h2, hEsc, hcardD] at h1
      rw [hcardDG, ← h1, mul_comm]
    have hnorm := normalizer_map_mk_le_map_inf hp O hO hOM hDhp
      (h.normalizer_le_of_hyperplane hDGE hEDG)
    rw [hDmap] at hnorm
    exact (Subgroup.centralizer_le_normalizer _).trans hnorm
  refine le_centralizer_of_hyperplanes (E := Es) (S := Ss) hEel hSs_cop hEsN
    CFSG.pCore_isPGroup ?_
  intro D hDE hDidx a ha c hc
  have hcY : c ∈ Ys := hCY D hDE hDidx hc.2
  have h1 : c * a⁻¹ * c⁻¹ ∈ Ss := (mem_normalizer_iff.mp (hYsN hcY) a⁻¹).mp (Ss.inv_mem ha.1)
  have hP1 : a * c * a⁻¹ * c⁻¹ ∈ CFSG.pCore p (↥H ⧸ O) :=
    (CFSG.pCore p (↥H ⧸ O)).mul_mem
      ((CFSG.pCore_normal (p := p)).conj_mem c hc.1 a) ((CFSG.pCore p (↥H ⧸ O)).inv_mem hc.1)
  have hS1 : a * c * a⁻¹ * c⁻¹ ∈ Ss := by
    have := Ss.mul_mem ha.1 h1
    simpa only [mul_assoc] using this
  have hbot := inf_eq_bot_of_isPGroup hp (CFSG.pCore_isPGroup (G := ↥H ⧸ O) (p := p))
    ((hp.coprime_iff_not_dvd).mpr hSs_cop)
  have h2 : a * c * a⁻¹ * c⁻¹ ∈ CFSG.pCore p (↥H ⧸ O) ⊓ Ss := ⟨hP1, hS1⟩
  rw [hbot, Subgroup.mem_bot] at h2
  exact (commutatorElement_eq_one_iff_mul_comm (g₁ := a) (g₂ := c)).mp h2

end NineCore

namespace NineSettingGen

theorem starImg_le_centralizer_pCore (h : NineSettingGen G M p Q H E k) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSY : S ≤ H ⊓ M)
    (hSn : ∀ y ∈ H ⊓ M, ∀ s ∈ S, y * s * y⁻¹ ∈ S) :
    starImg p H S ≤ Subgroup.centralizer
      ((CFSG.pCore p (↥H ⧸ primeComplementCore (G := ↥H) p) :
        Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) : Set (↥H ⧸ primeComplementCore
          (G := ↥H) p)) :=
  h.toCore.starImg_le_centralizer_pCore hS2 hSY hSn

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
