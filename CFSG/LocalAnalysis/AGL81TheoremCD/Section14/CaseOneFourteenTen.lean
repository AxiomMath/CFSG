module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneThreeStarImg
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.ThreePrimeJCentral
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTransfer
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Target
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactAutAlt
import CFSG.Quasithin.SteinbergCGPlanePairTransport
import CFSG.RankThree.PartOne.S9.Sylow.GlobalLemmas
import CFSG.GroupTheory.WielandtProductAux
import CFSG.GroupTheory.Commutator.SubgroupOf

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.Quasithin
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (gnV gnC gnImg)


variable {G : Type} [Group G] [Finite G]

theorem isThreeOnePlusFour_of_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour R) :
    CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour R' := by
  obtain ⟨hcard, hpow, hcenter, hcomm⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv, hcard]
  · intro x
    have := congrArg e (hpow (e.symm x))
    simpa using this
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hcenter]
  · intro x hx
    have hxmap : x ∈ (commutator R).map e.toMonoidHom := by
      rw [show commutator R = ⁅(⊤ : Subgroup R), ⊤⁆ from rfl, Subgroup.map_commutator]
      simp only [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
      rw [show ⁅(⊤ : Subgroup R'), ⊤⁆ = commutator R' from rfl]
      exact hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxmap
    exact (Subgroup.centerCongr e ⟨y, hcomm hy⟩).2

namespace CaseOneCtx

variable {M H E Q J R T : Subgroup G}

theorem isThreeOnePlusFour_threeStarImg (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) (hQD : Q ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M = ⊥) :
    CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥(threeStarImg M Q) := by
  have hQM : Q ≤ M := c.choice.Q_le_M c.nine
  let e := threeStarImgMulEquiv M Q hQM hQD
  have hQ142 : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥Q := by
    obtain ⟨⟨hcard, hpow, hcomm, hcenter⟩, -⟩ := h142 H E Q J c.choice c.typeA
    refine ⟨hcard, ?_, ?_, ?_⟩
    · intro x
      apply Subtype.ext
      simpa using hpow x.1 x.2
    · rw [Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center ↥Q) Q.subtype
        Q.subtype_injective).toEquiv, hcenter]
    · intro x hx
      have hxQ : (x : G) ∈ ⁅Q, Q⁆ := by
        have hmap : (commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
          rw [show commutator ↥Q = ⁅(⊤ : Subgroup ↥Q), ⊤⁆ from rfl, Subgroup.map_commutator]
          rw [show (⊤ : Subgroup ↥Q).map Q.subtype = Q from by
            ext y
            constructor
            · rintro ⟨z, -, rfl⟩; exact z.2
            · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩]
        rw [← hmap]
        exact Subgroup.mem_map_of_mem Q.subtype hx
      rw [hcomm] at hxQ
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxQ
      have hxy : y = x := Subtype.ext hyx
      rwa [hxy] at hy
  exact isThreeOnePlusFour_of_mulEquiv e hQ142

private theorem alternating_le_eleven {M L : Subgroup G} (h8 : FourteenEightData M L)
    {m : ℕ} (eA : threeStar L ≃* alternatingGroup (Fin m))
    (h3M : CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) ≤ 3) : m ≤ 11 := by
  by_contra hm
  have hm12 : 12 ≤ m := by omega
  obtain ⟨eL⟩ := h8.img_equiv
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar L)) :=
    CFSG.AGLEmbedding.le_pRank_of_mulEquiv_alternatingGroup eA (k := 4) (by omega)
  have h4bar : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(threeStarImg M L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eL]
    exact h4
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(threeStarImg M L)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (threeStarImg M L)]
    exact CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  omega

private theorem three_pow_five_dvd_mulAut_threeStarImg (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) {L : Subgroup G} (h8 : FourteenEightData M L)
    (hQD : Q ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M = ⊥) :
    3 ^ 5 ∣ Nat.card (MulAut ↥(threeStarImg M L)) := by
  have hQM : Q ≤ M := c.choice.Q_le_M c.nine
  have hQbar_card : Nat.card ↥(threeStarImg M Q) = 3 ^ 5 := by
    obtain ⟨⟨hcard, -⟩, -⟩ := h142 H E Q J c.choice c.typeA
    rw [← Nat.card_congr (threeStarImgMulEquiv M Q hQM hQD).toEquiv, hcard]
  have hLbar_normal : (threeStarImg M L).Normal := by
    rw [threeStarImg]
    exact h8.L_normal.map _ (QuotientGroup.mk'_surjective _)
  haveI : (threeStarImg M L).Normal := hLbar_normal
  let φ : threeStar M →* MulAut ↥(threeStarImg M L) := MulAut.conjNormal
  have hker_eq : φ.ker = Subgroup.centralizer (threeStarImg M L : Set (threeStar M)) :=
    CFSG.ProperTwoGeneratedCore.normal_conjugation_kernel_eq_centralizer (threeStarImg M L)
  have hφker : φ.ker = ⊥ := by
    rw [hker_eq, h8.centralizer_img]
  let ψ : ↥(threeStarImg M Q) →* MulAut ↥(threeStarImg M L) :=
    φ.comp (threeStarImg M Q).subtype
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : (a : threeStar M) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact ha
    rw [hφker, Subgroup.mem_bot] at hmem
    exact Subtype.val_injective hmem
  have hdvd : Nat.card ↥(threeStarImg M Q) ∣ Nat.card (MulAut ↥(threeStarImg M L)) :=
    Subgroup.card_dvd_of_injective ψ hψinj
  rwa [hQbar_card] at hdvd

private theorem three_pow_five_not_dvd_mulAut_alternating {m : ℕ} (hm5 : 5 ≤ m)
    (hm11 : m ≤ 11) :
    ¬ 3 ^ 5 ∣ Nat.card (MulAut ↥(alternatingGroup (Fin m))) := by
  intro hdvd
  by_cases h6 : m = 6
  · subst h6
    have hdiv :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_mulAut_alternatingGroup_six_dvd_two_mul
    have hle := hdvd.trans hdiv
    norm_num at hle
  · rw [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_mulAut_alternatingGroup_eq_factorial
      m hm5 h6] at hdvd
    interval_cases m <;> norm_num [Nat.factorial] at hdvd

theorem not_alternating (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) {L : Subgroup G} (h8 : FourteenEightData M L)
    (hQD : Q ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M = ⊥)
    (h3M : CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) ≤ 3) :
    ¬ ∃ m : ℕ, 5 ≤ m ∧ Nonempty (threeStar L ≃* alternatingGroup (Fin m)) := by
  rintro ⟨m, hm5, ⟨eA⟩⟩
  have hm11 := alternating_le_eleven h8 eA h3M
  have hdvd := three_pow_five_dvd_mulAut_threeStarImg c h142 h8 hQD
  obtain ⟨eL⟩ := h8.img_equiv
  have hcardMul : Nat.card (MulAut ↥(threeStarImg M L)) =
      Nat.card (MulAut ↥(alternatingGroup (Fin m))) :=
    Nat.card_congr (MulAut.congr (eL.trans eA)).toEquiv
  rw [hcardMul] at hdvd
  exact three_pow_five_not_dvd_mulAut_alternating hm5 hm11 hdvd
end CaseOneCtx

@[expose] def KFact1410a : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple L →
    Subgroup.center ↥L = ⊥ → Subgroup.centralizer (L : Set X) = ⊥ →
    CFSG.AGLEmbedding.IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
    ∀ R : Subgroup X, CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R →
      3 ≤ CFSG.Open.pRank 3 L

@[expose] def K4143NoExtraspecial : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple L →
    Subgroup.center ↥L = ⊥ → CFSG.AGLEmbedding.IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
    CFSG.Open.pRank 3 L = 3 → CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 →
      ∀ R : Subgroup X, ¬ CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R

namespace CaseOneCtx

variable {M H E Q J R T : Subgroup G}

theorem not_isClassicalTwoOrG2 (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) {L : Subgroup G} (h8 : FourteenEightData M L)
    (hQD : Q ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M = ⊥)
    (h3M : CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) ≤ 3)
    (h1410 : KFact1410a) (h4143 : K4143NoExtraspecial) :
    ¬ CFSG.AGLEmbedding.IsClassicalTwoOrG2 (threeStar L) := by
  intro hcl
  obtain ⟨eL⟩ := h8.img_equiv
  have hLbar_normal : (threeStarImg M L).Normal := by
    rw [threeStarImg]
    exact h8.L_normal.map _ (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (threeStar L) := h8.simple
  have hqStar : CFSG.IsQuasisimple (threeStar L) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h8.nonabelian).1
  have hqLbar : CFSG.IsQuasisimple ↥(threeStarImg M L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hqStar
  have hqOpen : CFSG.Open.IsQuasisimple ↥(threeStarImg M L) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hqLbar)
  have hcenterStar : Subgroup.center (threeStar L) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h8.nonabelian).2
  have hcenterL : Subgroup.center ↥(threeStarImg M L) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (Subgroup.centerCongr eL).toEquiv, hcenterStar]
    simp
  have hclass : CFSG.AGLEmbedding.IsClassicalTwoOrG2
      (↥(threeStarImg M L) ⧸ Subgroup.center ↥(threeStarImg M L)) := by
    have e1 : (↥(threeStarImg M L) ⧸ Subgroup.center ↥(threeStarImg M L)) ≃* threeStar L :=
      ((QuotientGroup.quotientMulEquivOfEq hcenterL).trans QuotientGroup.quotientBot).trans eL
    exact CFSG.HardMathSupport.Cooperstein.Proving.isClassicalTwoOrG2_of_mulEquiv e1.symm hcl
  have hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥(threeStarImg M Q) :=
    c.isThreeOnePlusFour_threeStarImg h142 hQD
  have h3Lbar : 3 ≤ CFSG.Open.pRank 3 (threeStarImg M L) :=
    h1410 (threeStar M) (threeStarImg M L) hLbar_normal hqOpen hcenterL
      h8.centralizer_img hclass (threeStarImg M Q) hR
  have hmono : CFSG.Open.pRank 3 (threeStarImg M L) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  have hrankL : CFSG.Open.pRank 3 (threeStarImg M L) = 3 := by omega
  have hrankTop : CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) = 3 := by omega
  exact h4143 (threeStar M) (threeStarImg M L) hLbar_normal hqOpen hcenterL hclass
    hrankL hrankTop (threeStarImg M Q) hR

theorem isKGroup_lHatQuot (c : CaseOneCtx G M H E Q J R T) {L : Subgroup G}
    (hLM : L ≤ M) :
    CFSG.Open.IsKGroup (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))) := by
  have hTM : T ≤ M := c.T_sylow.le.trans inf_le_right
  have hXM : L ⊔ T ≤ M := sup_le hLM hTM
  haveI : IsSimpleGroup G := c.choice.cstar.simple
  have hMtop : M ≠ ⊤ := CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top
    c.choice.cstar.nonab M c.choice.maxLocal.1
  have hXtop : L ⊔ T ≠ ⊤ := by
    intro h
    exact hMtop (top_le_iff.mp (h ▸ hXM))
  exact (c.choice.cstar.kProper.isKGroup (L ⊔ T) hXtop).quotient _

end CaseOneCtx

section Certs44

theorem commutator_gnImg_thompsonJ_eq_bot (X : Type) [Group X] [Finite X] (T : Subgroup X)
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X))
    (hQT : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ T) (hK : CFSG.Open.IsKGroup (X ⧸ gnC T))
    (hO2 : CFSG.pCore 2 (X ⧸ gnC T) = ⊥) (N : Subgroup (X ⧸ gnC T)) [N.Normal]
    (h3 : ¬ 3 ∣ Nat.card N) : ⁅N, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = ⊥ := by
  have hV : IsElemAbelian 2 (gnV T) :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.isElemAbelian_gnV_of_le hC hQT
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hinj := gnRep_injective hV
  have hJle : gnImg T (CFSG.Quasithin.thompsonJ T) ≤
      Subgroup.centralizer (N : Set (X ⧸ gnC T)) := by
    unfold gnImg CFSG.Quasithin.thompsonJ
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    have hcomm :=
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.commutator_eq_bot_of_normal_of_not_three_dvd
        (X ⧸ gnC T) (Additive (IntMod (gnV T) hV)) (gnRep hV) hinj hK hO2
        (A.map (QuotientGroup.mk' (gnC T))) (isElementaryAbelian_map_mk hA)
        (CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.isBestOffender_gnRep_of_le hV
          (CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.gnV_le_of_le hC hQT) hA) N h3
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJle

private theorem lHat_perfect {M L : Subgroup G} (h8 : FourteenEightData M L) :
    Group.IsPerfect ↥L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (threeStar L) := h8.simple
  let O : Subgroup ↥L := CFSG.pPrimeCore 3 ↥L
  let π : ↥L →* threeStar L := QuotientGroup.mk' O
  have hperfQ : Group.IsPerfect (threeStar L) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h8.nonabelian).1.1
  have hmap : (commutator ↥L).map π = ⊤ := by
    rw [show commutator ↥L = ⁅(⊤ : Subgroup ↥L), ⊤⁆ from rfl, Subgroup.map_commutator]
    simp only [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O)]
    rw [show ⁅(⊤ : Subgroup (threeStar L)), ⊤⁆ = commutator (threeStar L) from rfl,
      hperfQ.commutator_eq_top]
  have hsup : commutator ↥L ⊔ O = ⊤ := by
    have h := Subgroup.comap_map_eq π (commutator ↥L)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hcop : Nat.Coprime 3 (commutator ↥L).index :=
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥L)).of_dvd_right
      (CFSG.GroupTheory.WielandtProduct.index_dvd_card_of_sup_eq_top hsup)
  have hle : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥L ≤
      commutator ↥L :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index
      3 (commutator ↥L) hcop
  have htop : (⊤ : Subgroup ↥L) ≤ commutator ↥L := by
    rwa [← h8.residual]
  rw [Group.isPerfect_def]
  exact top_le_iff.mp htop

private theorem lHat_commutator {M L T : Subgroup G} (h9 : FourteenNineData M L T) :
    ⁅gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T)),
        gnImg (T.subgroupOf (L ⊔ T)) (CFSG.Quasithin.thompsonJ (T.subgroupOf (L ⊔ T)))⁆ =
      gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T)) := by
  let X : Subgroup G := L ⊔ T
  have hthompX : ⁅(CFSG.Quasithin.thompsonJ T).subgroupOf X, L.subgroupOf X⁆ =
      L.subgroupOf X := by
    have hA : CFSG.Quasithin.thompsonJ T ≤ X :=
      (CFSG.Quasithin.C1GN.thompsonJ_le T).trans le_sup_right
    rw [CFSG.GroupTheory.commutator_subgroupOf_eq hA le_sup_left, h9.thompson]
  have hJX : CFSG.Quasithin.thompsonJ (T.subgroupOf X) =
      (CFSG.Quasithin.thompsonJ T).subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [CFSG.Quasithin.SteinbergCG.thompsonJ_subgroupOf_map le_sup_right]
    rw [Subgroup.map_subgroupOf_eq_of_le
      ((CFSG.Quasithin.C1GN.thompsonJ_le T).trans le_sup_right)]
  have hmap : ⁅(CFSG.Quasithin.thompsonJ (T.subgroupOf X)).map
        (QuotientGroup.mk' (gnC (T.subgroupOf X))),
      (L.subgroupOf X).map (QuotientGroup.mk' (gnC (T.subgroupOf X)))⁆ =
      (L.subgroupOf X).map (QuotientGroup.mk' (gnC (T.subgroupOf X))) := by
    rw [← Subgroup.map_commutator, hJX, hthompX]
  simpa [gnImg, X, Subgroup.commutator_comm] using hmap

private theorem lHat_ker_le_core {M L T : Subgroup G} (h8 : FourteenEightData M L)
    (h9 : FourteenNineData M L T) :
    ((QuotientGroup.mk' (gnC (T.subgroupOf (L ⊔ T)))).comp
        (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ T))).ker ≤
      CFSG.pPrimeCore 3 ↥L := by
  intro l hl
  rw [MonoidHom.mem_ker] at hl
  have hC : Subgroup.inclusion (le_sup_left : L ≤ L ⊔ T) l ∈
      gnC (T.subgroupOf (L ⊔ T)) := by
    have hmem : Subgroup.inclusion (le_sup_left : L ≤ L ⊔ T) l ∈
        (QuotientGroup.mk' (gnC (T.subgroupOf (L ⊔ T)))).ker := by
      rw [MonoidHom.mem_ker]
      simpa using hl
    rwa [QuotientGroup.ker_mk'] at hmem
  have hD : (l : G) ∈ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
    have h := h9.gnC_le (Subgroup.mem_map.mpr ⟨Subgroup.inclusion le_sup_left l, hC, rfl⟩)
    simpa using h
  have hLD : (l : G) ∈ L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := ⟨l.2, hD⟩
  rw [← h8.core_eq] at hLD
  obtain ⟨o, ho, hlo⟩ := Subgroup.mem_map.mp hLD
  have hoi : o = l := Subtype.ext hlo
  rwa [hoi] at ho


private theorem lHat_Nhat_normal_not_three {M L T : Subgroup G} (h8 : FourteenEightData M L)
    (h9 : FourteenNineData M L T) (hTM : T ≤ M) :
    (gnImg (T.subgroupOf (L ⊔ T))
        ((L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M).subgroupOf (L ⊔ T))).Normal ∧
      ¬ 3 ∣ Nat.card ↥(gnImg (T.subgroupOf (L ⊔ T))
        ((L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M).subgroupOf (L ⊔ T))) := by
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let T' : Subgroup ↥X := T.subgroupOf X
  let N : Subgroup ↥X := (L ⊓ D).subgroupOf X
  let π : ↥X →* ↥X ⧸ gnC T' := QuotientGroup.mk' (gnC T')
  let Nhat : Subgroup (↥X ⧸ gnC T') := N.map π
  have hXM : X ≤ M := sup_le h8.L_le hTM
  have hDleM : D ≤ M := show D ≤ M from Subgroup.map_subtype_le _
  have hDnormM : (D.subgroupOf M).Normal := by
    have hDeq : D.subgroupOf M = CFSG.pPrimeCore 3 ↥M := by
      change Subgroup.comap M.subtype ((CFSG.pPrimeCore 3 ↥M).map M.subtype) =
        CFSG.pPrimeCore 3 ↥M
      exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [hDeq]
    exact CFSG.pPrimeCore_normal
  have hLN : X ≤ Subgroup.normalizer (L : Set G) :=
    hXM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h8.L_le).mp h8.L_normal)
  have hDN : X ≤ Subgroup.normalizer (D : Set G) :=
    hXM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hDleM).mp hDnormM)
  have hNnorm : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show L ⊓ D ≤ X from inf_le_left.trans le_sup_left)).mpr
      ((le_inf hLN hDN).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have h3Nhat : ¬ 3 ∣ Nat.card ↥Nhat := by
    have hDcop : Nat.Coprime 3 (Nat.card ↥D) :=
      CFSG.RankThree.PartOne.Sec9B.coprime_card_inSubgroup_pPrimeCore (r := 3) M
    have hLDcop : Nat.Coprime 3 (Nat.card ↥(L ⊓ D)) :=
      hDcop.of_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
    have hNcop : Nat.Coprime 3 (Nat.card ↥N) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show L ⊓ D ≤ X from inf_le_left.trans le_sup_left)).toEquiv]
      exact hLDcop
    exact (Nat.prime_three.coprime_iff_not_dvd).mp
      (hNcop.of_dvd_right (Subgroup.card_map_dvd N π))
  exact ⟨hNnorm.map π (QuotientGroup.mk'_surjective _), h3Nhat⟩

private theorem lHat_Nhat_le_center {M L T : Subgroup G} (h8 : FourteenEightData M L)
    (h9 : FourteenNineData M L T) (hTM : T ≤ M)
    (hK : CFSG.Open.IsKGroup (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))))
    (hLcomm : ⁅gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T)),
        gnImg (T.subgroupOf (L ⊔ T)) (CFSG.Quasithin.thompsonJ (T.subgroupOf (L ⊔ T)))⁆ =
      gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) :
    (gnImg (T.subgroupOf (L ⊔ T))
        ((L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M).subgroupOf (L ⊔ T))).subgroupOf
        (gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) ≤
      Subgroup.center ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) := by
  let X : Subgroup G := L ⊔ T
  let T' : Subgroup ↥X := T.subgroupOf X
  let Lhat : Subgroup (↥X ⧸ gnC T') := gnImg T' (L.subgroupOf X)
  let Jhat : Subgroup (↥X ⧸ gnC T') := gnImg T' (CFSG.Quasithin.thompsonJ T')
  let Nhat : Subgroup (↥X ⧸ gnC T') :=
    gnImg T' ((L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M).subgroupOf X)
  obtain ⟨hNhat_normal, h3Nhat⟩ := lHat_Nhat_normal_not_three h8 h9 hTM
  haveI : Nhat.Normal := hNhat_normal
  have hcomm := commutator_gnImg_thompsonJ_eq_bot X T' h9.charTwo h9.core_le hK
    h9.pCore_two Nhat h3Nhat
  rw [Subgroup.commutator_comm] at hcomm
  have hJcenter : Jhat ≤ Subgroup.centralizer (Nhat : Set (↥X ⧸ gnC T')) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hJL : ⁅Jhat, Lhat⁆ ≤ Subgroup.centralizer (Nhat : Set (↥X ⧸ gnC T')) :=
    (Subgroup.commutator_mono hJcenter le_rfl).trans (Subgroup.commutator_le_left _ _)
  have hLcomp : Lhat ≤ Subgroup.centralizer (Nhat : Set (↥X ⧸ gnC T')) := by
    have hLcomm' : ⁅Jhat, Lhat⁆ = Lhat := by
      rw [Subgroup.commutator_comm]; exact hLcomm
    rw [← hLcomm']
    exact hJL
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro l
  apply Subtype.ext
  simpa using (Subgroup.mem_centralizer_iff.mp (hLcomp l.2) (n : ↥X ⧸ gnC T')
    (Subgroup.mem_subgroupOf.mp hn)).symm

private theorem lHat_psi_of_quotient {L T : Subgroup G}
    (f : ↥L →* ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))))
    (hfsurj : Function.Surjective f)
    (hker : f.ker ≤ CFSG.pPrimeCore 3 ↥L) :
    ∃ ψ : ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) →* threeStar L,
      Function.Surjective ψ ∧
        (∀ l, ψ (f l) = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥L) l) := by
  let X : Subgroup G := L ⊔ T
  let T' : Subgroup ↥X := T.subgroupOf X
  let Lhat : Subgroup (↥X ⧸ gnC T') := gnImg T' (L.subgroupOf X)
  let O : Subgroup ↥L := CFSG.pPrimeCore 3 ↥L
  let K : Subgroup ↥L := f.ker
  have hKker : K ≤ (QuotientGroup.mk' O).ker := by
    rw [QuotientGroup.ker_mk']
    exact hker
  let ψ0 : (↥L ⧸ K) →* threeStar L :=
    QuotientGroup.lift K (QuotientGroup.mk' O) hKker
  let e : (↥L ⧸ K) ≃* ↥Lhat :=
    MulEquiv.ofBijective (QuotientGroup.kerLift f) (by
      refine ⟨QuotientGroup.kerLift_injective f, ?_⟩
      intro y
      obtain ⟨l, rfl⟩ := hfsurj y
      exact ⟨QuotientGroup.mk' K l, QuotientGroup.kerLift_mk f l⟩)
  let ψ : ↥Lhat →* threeStar L := ψ0.comp e.symm.toMonoidHom
  have hψ_apply : ∀ l, ψ (f l) = QuotientGroup.mk' O l := by
    intro l
    have hes : e.symm (f l) = QuotientGroup.mk' K l := by
      rw [← show e (QuotientGroup.mk' K l) = f l from rfl, MulEquiv.symm_apply_apply]
    calc ψ (f l) = ψ0 (e.symm (f l)) := rfl
      _ = ψ0 (QuotientGroup.mk' K l) := by rw [hes]
      _ = QuotientGroup.mk' O l :=
        QuotientGroup.lift_mk K (φ := QuotientGroup.mk' O) hKker l
  have hψsurj : Function.Surjective ψ := by
    have h0 : Function.Surjective ψ0 :=
      QuotientGroup.lift_surjective_of_surjective K (QuotientGroup.mk' O)
        (QuotientGroup.mk'_surjective O) hKker
    intro y
    obtain ⟨x, rfl⟩ := h0 y
    exact ⟨e x, by simp [ψ]⟩
  exact ⟨ψ, hψsurj, hψ_apply⟩

private theorem lHat_map_to_star {M L T : Subgroup G} (h8 : FourteenEightData M L)
    (h9 : FourteenNineData M L T) :
    ∃ (f : ↥L →* ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))))
      (ψ : ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) →* threeStar L),
      Function.Surjective f ∧ Function.Surjective ψ ∧
        (∀ l, ψ (f l) = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥L) l) ∧
        (∀ l, (f l : ↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))) =
          (QuotientGroup.mk' (gnC (T.subgroupOf (L ⊔ T))))
            (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ T) l)) := by
  let X : Subgroup G := L ⊔ T
  let T' : Subgroup ↥X := T.subgroupOf X
  let π : ↥X →* ↥X ⧸ gnC T' := QuotientGroup.mk' (gnC T')
  let Lhat : Subgroup (↥X ⧸ gnC T') := gnImg T' (L.subgroupOf X)
  let fL : ↥L →* ↥X ⧸ gnC T' := π.comp (Subgroup.inclusion le_sup_left)
  have hrange : fL.range = Lhat := by
    change fL.range = gnImg T' (L.subgroupOf X)
    rw [gnImg, MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr q.2
    · intro hx
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  let fL' : ↥L →* ↥Lhat := fL.codRestrict Lhat fun l => by
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨l, rfl⟩
  have hsurj : Function.Surjective fL' := by
    intro y
    have hy : (y : ↥X ⧸ gnC T') ∈ fL.range := by rw [hrange]; exact y.2
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hy
    exact ⟨l, Subtype.ext hl⟩
  have hker : fL'.ker ≤ CFSG.pPrimeCore 3 ↥L := by
    have hK_eq : fL'.ker = fL.ker := by
      ext l
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro h
        have := congrArg Subtype.val h
        simpa [fL'] using this
      · intro h
        apply Subtype.ext
        simpa [fL'] using h
    rw [hK_eq]
    exact lHat_ker_le_core h8 h9
  have hfl : ∀ l, (fL' l : ↥X ⧸ gnC T') = π (Subgroup.inclusion le_sup_left l) :=
    fun l => rfl
  obtain ⟨ψ, hψsurj, hψ_apply⟩ := lHat_psi_of_quotient fL' hsurj hker
  exact ⟨fL', ψ, hsurj, hψsurj, hψ_apply, hfl⟩

private theorem lHat_psi_ker_le_N {M L T : Subgroup G} (h8 : FourteenEightData M L)
    (f : ↥L →* ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))))
    (ψ : ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) →* threeStar L)
    (hfsurj : Function.Surjective f)
    (hψ_apply : ∀ l, ψ (f l) = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥L) l)
    (hfl : ∀ l, (f l : ↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))) =
      (QuotientGroup.mk' (gnC (T.subgroupOf (L ⊔ T))))
        (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ T) l)) :
    ψ.ker ≤ (gnImg (T.subgroupOf (L ⊔ T))
        ((L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M).subgroupOf (L ⊔ T))).subgroupOf
        (gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) := by
  let X : Subgroup G := L ⊔ T
  let O : Subgroup ↥L := CFSG.pPrimeCore 3 ↥L
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  obtain ⟨l, rfl⟩ := hfsurj y
  have hyl : QuotientGroup.mk' O l = 1 := by
    have h := hψ_apply l
    rw [hy] at h
    exact h.symm
  have hyl' : l ∈ O := (QuotientGroup.eq_one_iff (N := O) l).mp hyl
  have hD : (l : G) ∈ L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
    rw [← h8.core_eq]
    exact Subgroup.mem_map.mpr ⟨l, hyl', rfl⟩
  have hsub : Subgroup.inclusion (le_sup_left : L ≤ L ⊔ T) l ∈
      (L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M).subgroupOf X := by
    rw [Subgroup.mem_subgroupOf]
    exact hD
  have hmem : (f l : ↥X ⧸ gnC (T.subgroupOf X)) ∈
      gnImg (T.subgroupOf X) ((L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M).subgroupOf X) := by
    rw [hfl l, gnImg]
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion le_sup_left l, hsub, rfl⟩
  rw [Subgroup.mem_subgroupOf]
  exact hmem

private theorem lHat_psi_center {M L T : Subgroup G} (h8 : FourteenEightData M L)
    (h9 : FourteenNineData M L T) (hTM : T ≤ M)
    (hK : CFSG.Open.IsKGroup (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))))
    (hLcomm : ⁅gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T)),
        gnImg (T.subgroupOf (L ⊔ T)) (CFSG.Quasithin.thompsonJ (T.subgroupOf (L ⊔ T)))⁆ =
      gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) :
    ∃ ψ : ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) →* threeStar L,
      Function.Surjective ψ ∧ Group.IsPerfect ↥(gnImg (T.subgroupOf (L ⊔ T))
        (L.subgroupOf (L ⊔ T))) ∧
      Subgroup.center ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) = ψ.ker := by
  obtain ⟨f, ψ, hfsurj, hψsurj, hψ_apply, hfl⟩ := lHat_map_to_star h8 h9
  have hperfLhat : Group.IsPerfect ↥(gnImg (T.subgroupOf (L ⊔ T))
      (L.subgroupOf (L ⊔ T))) := by
    haveI : Group.IsPerfect ↥L := lHat_perfect h8
    exact Group.IsPerfect.ofSurjective (f := f) hfsurj
  have hψker_le_N := lHat_psi_ker_le_N h8 f ψ hfsurj hψ_apply hfl
  have hNcenter := lHat_Nhat_le_center h8 h9 hTM hK hLcomm
  have hψker_center : ψ.ker ≤ Subgroup.center ↥(gnImg (T.subgroupOf (L ⊔ T))
      (L.subgroupOf (L ⊔ T))) := hψker_le_N.trans hNcenter
  haveI : IsSimpleGroup (threeStar L) := h8.simple
  have hcenterStar : Subgroup.center (threeStar L) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h8.nonabelian).2
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hperfLhat ψ hψsurj hψker_center
  have hcenter_eq : Subgroup.center ↥(gnImg (T.subgroupOf (L ⊔ T))
      (L.subgroupOf (L ⊔ T))) = ψ.ker := by
    rw [← hcomap, hcenterStar]
    simp
  exact ⟨ψ, hψsurj, hperfLhat, hcenter_eq⟩

namespace CaseOneCtx

variable {M H E Q J R T : Subgroup G}

theorem lHat_component (c : CaseOneCtx G M H E Q J R T) {L : Subgroup G}
    (h8 : FourteenEightData M L) (h9 : FourteenNineData M L T) :
    CFSG.Open.IsComponentOf (gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) ⊤ ∧
    ⁅gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T)),
        gnImg (T.subgroupOf (L ⊔ T)) (CFSG.Quasithin.thompsonJ (T.subgroupOf (L ⊔ T)))⁆ =
      gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T)) ∧
    Nonempty (↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) ⧸
        Subgroup.center ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) ≃* threeStar L) := by
  have hTM : T ≤ M := c.T_sylow.le.trans inf_le_right
  have hK : CFSG.Open.IsKGroup (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))) :=
    c.isKGroup_lHatQuot h8.L_le
  have hLcomm := lHat_commutator (T := T) h9
  obtain ⟨ψ, hψsurj, hperf, hcenter⟩ := lHat_psi_center h8 h9 hTM hK hLcomm
  haveI : IsSimpleGroup (threeStar L) := h8.simple
  have hqStar : CFSG.IsQuasisimple (threeStar L) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h8.nonabelian).1
  have hqNative : CFSG.IsQuasisimple ↥(gnImg (T.subgroupOf (L ⊔ T))
      (L.subgroupOf (L ⊔ T))) :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf ψ hψsurj hcenter.symm.le).mpr hqStar
  have hqOpen : CFSG.Open.IsQuasisimple ↥(gnImg (T.subgroupOf (L ⊔ T))
      (L.subgroupOf (L ⊔ T))) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hqNative)
  let X : Subgroup G := L ⊔ T
  have hL'normal : (L.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (show L ≤ X from le_sup_left)]
    exact (sup_le h8.L_le hTM).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h8.L_le).mp h8.L_normal)
  have hLhat_normal : (gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf X)).Normal := by
    rw [gnImg]
    exact hL'normal.map _ (QuotientGroup.mk'_surjective _)
  have hLhat_top : ((gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf X)).subgroupOf ⊤).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
    rw [Subgroup.normalizer_eq_top_iff.mpr hLhat_normal]
  have hsub : CFSG.Open.IsSubnormal (gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf X)) ⊤ :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_top hLhat_top
  refine ⟨⟨le_top, hsub, hqOpen⟩, hLcomm, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)⟩

theorem ffConclusion_threeStar (c : CaseOneCtx G M H E Q J R T) {L : Subgroup G}
    (h8 : FourteenEightData M L) (h9 : FourteenNineData M L T)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.FFConclusion (threeStar L) := by
  obtain ⟨hLcomp, hLJ, hIso⟩ := c.lHat_component h8 h9
  obtain ⟨W, hWadd, hWmod, hWfin, ρ, hρ, A, hAel, hAbest, hAnorm, hLA⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.exists_rep_offender_of_le
      ↥(L ⊔ T) (T.subgroupOf (L ⊔ T)) h9.charTwo h9.core_le
      (gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) hLcomp hLJ
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  have hLhatne : gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T)) ≠ ⊥ := by
    intro hbot
    apply h9.not_le_gnC
    rw [gnImg] at hbot
    have hle := (Subgroup.map_eq_bot_iff (L.subgroupOf (L ⊔ T))).mp hbot
    rwa [QuotientGroup.ker_mk'] at hle
  have hKA : ⁅gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T)), A⁆ ≠ ⊥ := by
    rw [hLA]
    exact hLhatne
  have hFFc : CFSG.HardMathSupport.Cooperstein.Coordinator.FFConclusion
      (↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) ⧸
        Subgroup.center ↥(gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T)))) :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffConclusion_of_component hFF
      (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))) W ρ hρ
      (c.isKGroup_lHatQuot h8.L_le) h9.pCore_two A hAel hAbest
      (gnImg (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))) hLcomp hKA
  obtain ⟨e⟩ := hIso
  exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffConclusion_of_mulEquiv e hFFc

end CaseOneCtx

theorem caseOne_false_of_data {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    {L : Subgroup G} (h8 : FourteenEightData M L) (h9 : FourteenNineData M L T)
    (hQD : Q ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M = ⊥)
    (h3M : CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) ≤ 3)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (h1410 : KFact1410a) (h4143 : K4143NoExtraspecial) : False :=
  (c.ffConclusion_threeStar h8 h9 hFF).elim
    (c.not_isClassicalTwoOrG2 h142 h8 hQD h3M h1410 h4143)
    (c.not_alternating h142 h8 hQD h3M)

end Certs44

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
