module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDefs
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.SteinbergCBFTHall
import CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial
import CFSG.Open.StatedAPI
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
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
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

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Subgroup

theorem oPPrimeHull_oPPrimeHull (p : ℕ) {G : Type*} [Group G] (A : Subgroup G) :
    oPPrimeHull p (oPPrimeHull p A) = oPPrimeHull p A := by
  refine le_antisymm (closure_le _ |>.mpr fun x hx => hx.1) (closure_le _ |>.mpr fun x hx => ?_)
  exact subset_closure ⟨subset_closure hx, hx.2⟩

theorem exists_pow_mem_zpowers_of_orderOf_eq {p : ℕ} [hp : Fact p.Prime] {G G' : Type*} [Group G]
    [Finite G] [Group G'] (f : G →* G') (a : G) {k : ℕ} (hk : orderOf (f a) = p ^ k) :
    ∃ b ∈ zpowers a, (∃ j : ℕ, orderOf b = p ^ j) ∧ f b = f a := by
  obtain ⟨e, m, hm, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a).ne' p hp.out.ne_one
  have hcop : Nat.Coprime m (p ^ k) := (Nat.Coprime.pow_right k
    ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm).symm)
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime (hk ▸ hcop : Nat.Coprime m (orderOf (f a)))
  refine ⟨(a ^ m) ^ c, pow_mem (pow_mem (mem_zpowers a) m) c, ?_, ?_⟩
  · have h1 : (a ^ m) ^ p ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
    have hdvd : orderOf ((a ^ m) ^ c) ∣ p ^ e := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    exact ⟨j, hj⟩
  · rw [map_pow, map_pow, hc]

theorem map_oPPrimeHull {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G] [Finite G] [Group G']
    (f : G →* G') (A : Subgroup G) : (oPPrimeHull p A).map f = oPPrimeHull p (A.map f) := by
  rw [oPPrimeHull, MonoidHom.map_closure, oPPrimeHull]
  refine le_antisymm (closure_mono ?_) (closure_le _ |>.mpr ?_)
  · rintro _ ⟨x, ⟨hxA, k, hk⟩, rfl⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (hk ▸ orderOf_map_dvd f x)
    exact ⟨mem_map_of_mem f hxA, j, hj⟩
  · rintro _ ⟨⟨a, haA, rfl⟩, k, hk⟩
    obtain ⟨b, hb, hbp, hfb⟩ := exists_pow_mem_zpowers_of_orderOf_eq f a hk
    have hbA : b ∈ A := (zpowers_le.mpr haA) hb
    exact subset_closure ⟨b, ⟨hbA, hbp⟩, hfb⟩

theorem nonempty_quot_pCore_mulEquiv_of_surjective {p : ℕ} [Fact p.Prime] {A B : Type*} [Group A]
    [Group B] [Finite A] (f : A →* B) (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    Nonempty (A ⧸ CFSG.pCore p A ≃* B ⧸ CFSG.pCore p B) := by
  haveI : Finite B := Finite.of_surjective f hf
  have hmap : (CFSG.pCore p A).map f = CFSG.pCore p B :=
    CFSG.GroupTheory.FT63ChII.pCore_map_of_surjective hf hker
  have hkle : f.ker ≤ CFSG.pCore p A := le_sSup ⟨f.normal_ker, hker⟩
  have hNM : CFSG.pCore p A ≤ (CFSG.pCore p B).comap f := by
    rw [← hmap]
    exact le_comap_map f _
  refine ⟨MulEquiv.ofBijective (QuotientGroup.map _ _ f hNM) ⟨fun x y hxy => ?_, fun y => ?_⟩⟩
  · induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.eq, ← map_inv, ← map_mul,
      ← hmap] at hxy
    obtain ⟨n, hn, hfn⟩ := hxy
    rw [QuotientGroup.eq]
    have hk : a⁻¹ * b * n⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv f n, hfn, mul_inv_cancel]
    simpa using (CFSG.pCore p A).mul_mem (hkle hk) hn
  · induction y using QuotientGroup.induction_on with | H b => ?_
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨a, rfl⟩

theorem oPPrimeHull_map_eq {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G] [Finite G] [Group G']
    (f : G →* G') {H : Subgroup G} (hH : oPPrimeHull p H = H) :
    oPPrimeHull p (H.map f) = H.map f := by
  rw [← map_oPPrimeHull, hH]

theorem oPPrimeHull_top_of_eq {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : oPPrimeHull p H = H) : oPPrimeHull p (⊤ : Subgroup ↥H) = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [map_oPPrimeHull, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact hH

theorem nonempty_quot_pCore_mulEquiv_of_mulEquiv {p : ℕ} [Fact p.Prime] {A B : Type*} [Group A]
    [Group B] [Finite A] (e : A ≃* B) : Nonempty (A ⧸ CFSG.pCore p A ≃* B ⧸ CFSG.pCore p B) :=
  nonempty_quot_pCore_mulEquiv_of_surjective e.toMonoidHom e.surjective <| by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    exact IsPGroup.of_bot

theorem nonempty_quot_pCore_map_of_injective {p : ℕ} [Fact p.Prime] {G G' : Type*} [Group G]
    [Finite G] [Group G'] (f : G →* G') (hf : Function.Injective f) (H : Subgroup G) :
    Nonempty (↥H ⧸ CFSG.pCore p ↥H ≃* ↥(H.map f) ⧸ CFSG.pCore p ↥(H.map f)) :=
  nonempty_quot_pCore_mulEquiv_of_mulEquiv (H.equivMapOfInjective f hf)

theorem pCore_eq_bot_of_isIrreducibleMatrixRep {p n : ℕ} [Fact p.Prime]
    {H : Subgroup (GL (Fin n) (ZMod p))}
    (hH : CFSG.RepresentationTheory.IsIrreducibleMatrixRep H.subtype) : CFSG.pCore p ↥H = ⊥ := by
  let ρ : ↥H →* ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp H.subtype)
  refine @CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial.pCore_eq_bot p _
    ↥H (Fin n → ZMod p) _ _ (Pi.module _ _ _) _ _ ρ
    (fun a b hab => Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).injective hab)))
    fun W hW => hH W fun g w hw => hW g w hw

theorem dvd_card_of_oPPrimeHull_of_ne_bot {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {H : Subgroup G} (hH : oPPrimeHull p H = H) (hne : H ≠ ⊥) :
    p ∣ Nat.card H := by
  by_contra hp
  apply hne
  rw [← hH, oPPrimeHull]
  refine le_antisymm (Subgroup.closure_le _ |>.mpr ?_) bot_le
  rintro x ⟨hxH, k, hk⟩
  change x = 1
  have hdvd : orderOf x ∣ Nat.card ↥H := Subgroup.orderOf_dvd_natCard H hxH
  rw [hk] at hdvd
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exact absurd (dvd_trans (⟨p ^ k, by rw [pow_succ, mul_comm]⟩ : p ∣ p ^ (k + 1)) hdvd) hp

theorem det_eq_one_of_orderOf_eq_prime_pow {p n : ℕ} [Fact p.Prime]
    {g : GL (Fin n) (ZMod p)} {k : ℕ} (hg : orderOf g = p ^ k) :
    (g : Matrix (Fin n) (Fin n) (ZMod p)).det = 1 := by
  have hpow : (g : Matrix (Fin n) (Fin n) (ZMod p)) ^ p ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  have hdet : (g : Matrix (Fin n) (Fin n) (ZMod p)).det ^ p ^ k = 1 := by
    rw [← Matrix.det_pow, hpow, Matrix.det_one]
  have hfix : (g : Matrix (Fin n) (Fin n) (ZMod p)).det ^ p ^ k =
      (g : Matrix (Fin n) (Fin n) (ZMod p)).det := ZMod.pow_card_pow (n := k) _
  rwa [hfix] at hdet

theorem le_statedSL_of_oPPrimeHull {p n : ℕ} [Fact p.Prime]
    {H : Subgroup (GL (Fin n) (ZMod p))} (hH : oPPrimeHull p H = H) :
    H ≤ CFSG.Open.StatedSL n (ZMod p) := by
  rw [← hH]
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro x ⟨-, k, hk⟩
  exact CFSG.Open.StatedAPI.mem_statedSL_iff.mpr (det_eq_one_of_orderOf_eq_prime_pow hk)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
