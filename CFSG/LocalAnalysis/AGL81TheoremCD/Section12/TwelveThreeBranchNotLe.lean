module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineApply
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeOrders
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTenBranches
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.LThreeParabolic
public import CFSG.RankThree.PartOne.KP.Fi22SectionLocalThreeRank
import CFSG.GroupTheory.IsCyclicOfPRankLeOne
import CFSG.Holt.Induced
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OmegaPlusEightThreeRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.LThreeInnerP
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenAtQuotKer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenFinal
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.EvenBN.Tits.I21Filter
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rx
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FAt
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6SigOdd

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]
variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

@[expose] def KFactFi22SectionThreeRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (K : Subgroup ↥H) [K.Normal],
    Nonempty ((↥H ⧸ K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .Fi22) →
      4 ≤ CFSG.Open.twoLocalPrimeRank 3 G

theorem kFactFi22SectionThreeRank_holds :
    KFactFi22SectionThreeRank :=
  fun _ _ _ H K _ ⟨e⟩ =>
    CFSG.RankThree.PartOne.four_le_twoLocalPrimeRank_three_of_section_fi22 H K e

private theorem false_of_card_eq_tits_of_kStarType {K : Type} [Group K]
    (hcard : Nat.card K = 17971200)
    (htype : IsPSLType 2 (GaloisField 2 3) K ∨
      IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
        (fun B _ => Nat.card B = 3) K ∨ IsSLType 3 (GaloisField 2 2) K) : False := by
  rcases htype with hL2 | hExt | hSL
  · obtain ⟨e⟩ := hL2
    have hc : Nat.card K = 504 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.EvenBN.Tits.I21.Filter.card_psl_two_even _ (by norm_num)
          (GaloisField.card 2 3 (by norm_num)),
        GaloisField.card 2 3 (by norm_num)]
      norm_num
    omega
  · obtain ⟨N, hNnormal, hN3, hAN, -⟩ := hExt
    have : N.Normal := hNnormal
    obtain ⟨e⟩ := hAN
    have hc : Nat.card K = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N,
        Nat.card_congr e.toEquiv, nat_card_alternatingGroup, hN3]
      norm_num
    omega
  · obtain ⟨e⟩ := hSL
    have hc : Nat.card K = 60480 := by
      let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
      rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field 3]
      have hq : Fintype.card (GaloisField 2 2) = 4 := by
        rw [← Nat.card_eq_fintype_card]
        exact GaloisField.card 2 2 (by norm_num)
      simp [Fin.prod_univ_three, hq]
    omega

private theorem false_of_branchA_three (hord : TwelveThreeOrderFacts) {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) {K : Type} [Group K] {W : Type} [Group W]
    (htuple : ThreeNineTuple 3 d K W)
    (htype : IsPSLType 2 (GaloisField 2 3) K ∨
      IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
        (fun B _ => Nat.card B = 3) K ∨ IsSLType 3 (GaloisField 2 2) K) : False := by
  rcases htuple with ⟨-, hd13, htits, -⟩ | ⟨h35, -⟩ | ⟨h35, -⟩ | ⟨h35, -⟩ |
    ⟨h37, -⟩ | ⟨h37, -⟩ | ⟨hdvd, -, -⟩
  · have hcard : Nat.card K = 17971200 := by
      have hsimple := hord.1 K htits
      rw [isSimpleOfOrder_iff] at hsimple
      exact hsimple.2.2
    exact false_of_card_eq_tits_of_kStarType hcard htype
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h4 : d ∣ 2 ^ 2 := by simpa using hdvd
    have hdvd2 : d ∣ 2 := hd.dvd_of_dvd_pow h4
    exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp hdvd2)

theorem xSub_le_M_and_kSub_normal_of_branchA (h10 : NineTenGen) (h39 : ThreeNine)
    (hI : NineNineOneInput) (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hord : TwelveThreeOrderFacts) (h : TwelveCtx G M p Q H) (hns : ¬ Group.IsSolvable ↥M)
    {d : ℕ} (hd : d ∈ sigmaSet G M) (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G))
    (hdH : d ∣ Nat.card (H ⊓ M : Subgroup G)) (hA : ¬ pLayerIn p H ≤ M) :
    xSub p M H ≤ M ∧ ((kSub p M H).subgroupOf H).Normal := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  rcases nineTen_branchA_of_twelveCtx h10 h hEQ hE hEc hΓ hA with
    ⟨hX, -, hKn⟩ | ⟨hp3, htype, -, -, -⟩
  · exact ⟨hX, hKn⟩
  · exfalso
    rw [hp3] at htype
    have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
    have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
    have : Fact d.Prime := ⟨hdp⟩
    obtain ⟨D, hD⟩ := CFSG.ABGLocalTools.exists_isSylowOf d (H ⊓ M)
    have hk0 : 0 < (Nat.card (H ⊓ M : Subgroup G)).factorization d :=
      hdp.factorization_pos_of_dvd Nat.card_pos.ne' hdH
    have hD1 : D ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card D = 1 := by rw [hbot, Subgroup.card_bot]
      rw [hD.card_eq] at hcard
      exact (Nat.one_lt_pow hk0.ne' hdp.one_lt).ne' hcard
    obtain ⟨-, -, htuple⟩ :=
      threeNine_kStar_of_twelveCtx h39 hI hbridge h hns hd hXM hA hD hD1
    rw [hp3] at htuple
    exact false_of_branchA_three hord hdp hd2 htuple htype

private theorem exists_noncyclic_isPGroup_map_le {A B : Type*} [Group A] [Finite A] [Group B]
    {q : ℕ} (hq : q.Prime) (f : A →* B) {E : Subgroup B} (hE : E ≤ f.range)
    (hEq : IsPGroup q E) (hEnc : ¬ IsCyclic ↥E) :
    ∃ S : Subgroup A, IsPGroup q S ∧ ¬ IsCyclic ↥S ∧ S.map f = E := by
  have : Fact q.Prime := ⟨hq⟩
  have hE' : E ≤ (⊤ : Subgroup A).map f := by
    rwa [Subgroup.map_top]
  obtain ⟨S, -, -, hSq, hSmap⟩ :=
    CFSG.Holt.exists_isPGroup_map_eq_of_map_le (H := ⊤) f hEq hE'
      (IsPGroup.of_bot : IsPGroup q (⊥ : Subgroup A)) bot_le (by simp)
  let g : ↥S →* ↥E := (f.comp S.subtype).codRestrict E fun s =>
    (hSmap ▸ Subgroup.mem_map_of_mem f s.2 : f (s : A) ∈ E)
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp (show y.1 ∈ S.map f by rw [hSmap]; exact y.2)
    exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
  refine ⟨S, hSq, fun hc => hEnc (isCyclic_of_surjective g hgsurj), hSmap⟩

private theorem three_mem_sigmaA_of_fi22_kStar (hFi : KFactFi22SectionThreeRank)
    (hK : CFSG.Blueprint.NativeSporadic.IsSporadic ↥(kStar p M H) .Fi22) :
    3 ∈ rankThreeSigmaA G := by
  let K : Subgroup G := kSub p M H
  have hKH : K ≤ H := RankThreeUC.AGL81C.kSub_le p M H
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  let φ : ↥K →* ↥(kStar p M H) :=
    { toFun := fun k =>
        ⟨π ⟨k.1, hKH k.2⟩, Subgroup.mem_map.mpr
          ⟨⟨k.1, hKH k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; exact map_one π
      map_mul' := fun x y => by
        apply Subtype.ext
        exact map_mul π ⟨x.1, hKH x.2⟩ ⟨y.1, hKH y.2⟩ }
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext ?_⟩
    simpa [φ, π] using hxy
  let N : Subgroup ↥K := φ.ker
  have : N.Normal := MonoidHom.normal_ker φ
  obtain ⟨eK⟩ := hK
  have h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G :=
    hFi G K N ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans eK⟩
  exact mem_sigmaA_of_four_le_localRank Nat.prime_three (by norm_num)
    (by simpa [CFSG.Open.rankThreeLocalRank] using h4)

private theorem exists_noncyclic_three_subgroup_of_pOmegaPlus {X₁ : Subgroup (StarGroup p H)}
    {d : ℕ} (hW : CFSG.Open.StatedClassicalModel (oPrimeModPrimeComplement d X₁)
      .POmegaPlus 4 2 1) :
    ∃ S' : Subgroup (StarGroup p H), S' ≤ X₁ ∧ IsPGroup 3 S' ∧ ¬ IsCyclic ↥S' := by
  obtain ⟨E, hE3, hEnc⟩ :=
    exists_not_isCyclic_of_statedClassicalModel_pOmegaPlus_four_two hW
  let Q₁ := modPrimeComplement d X₁
  let W : Subgroup Q₁ := oPPrimeHull d (⊤ : Subgroup Q₁)
  let E' : Subgroup Q₁ := E.map W.subtype
  have hE'3 : IsPGroup 3 E' := hE3.map W.subtype
  have hE'nc : ¬ IsCyclic ↥E' := fun hc => hEnc
    ((MulEquiv.isCyclic (Subgroup.equivMapOfInjective E W.subtype
      W.subtype_injective)).mpr hc)
  let O₁ : Subgroup ↥X₁ :=
    CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥X₁) d
  let π₁ : ↥X₁ →* Q₁ := QuotientGroup.mk' O₁
  have hE'range : E' ≤ π₁.range := by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective O₁)]
    exact le_top
  obtain ⟨S, hS3, hSnc, hSmap⟩ :=
    exists_noncyclic_isPGroup_map_le Nat.prime_three π₁ hE'range hE'3 hE'nc
  refine ⟨S.map X₁.subtype, Subgroup.map_subtype_le S, hS3.map X₁.subtype, ?_⟩
  intro hc
  exact hSnc ((MulEquiv.isCyclic (Subgroup.equivMapOfInjective S X₁.subtype
    X₁.subtype_injective)).mpr hc)

private theorem exists_noncyclic_three_subgroup_inf (h : TwelveCtx G M p Q H)
    {S' : Subgroup (StarGroup p H)} (hS'le : S' ≤ starImg p H M)
    (hS'3 : IsPGroup 3 S') (hS'nc : ¬ IsCyclic ↥S') :
    ∃ R : Subgroup G, R ≤ H ⊓ M ∧ IsPGroup 3 R ∧ ¬ IsCyclic ↥R := by
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have hS'range : S' ≤ π.range := by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective O)]
    exact le_top
  obtain ⟨P, hP3, hPnc, hPmap⟩ :=
    exists_noncyclic_isPGroup_map_le Nat.prime_three π hS'range hS'3 hS'nc
  have hOle : O ≤ (M ⊓ H).subgroupOf H := primeComplementCore_le_subgroupOf_of_twelveCtx h
  have hMeq : M.subgroupOf H = (M ⊓ H).subgroupOf H := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hPle : P ≤ (M ⊓ H).subgroupOf H := by
    have hsub : P ≤ (((M ⊓ H).subgroupOf H).map π).comap π := by
      refine Subgroup.map_le_iff_le_comap.mp ?_
      rw [hPmap, ← hMeq]
      exact hS'le
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hOle] at hsub
  refine ⟨P.map H.subtype, ?_, hP3.map H.subtype, ?_⟩
  · have h := Subgroup.map_mono (f := H.subtype) hPle
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h
    exact le_inf (h.trans inf_le_right) (h.trans inf_le_left)
  · intro hc
    exact hPnc ((MulEquiv.isCyclic (Subgroup.equivMapOfInjective P H.subtype
      H.subtype_injective)).mpr hc)

private theorem two_le_pRank_three_of_not_isCyclic {R : Subgroup G}
    (hR3 : IsPGroup 3 R) (hRnc : ¬ IsCyclic ↥R) :
    2 ≤ CFSG.Open.pRank 3 R := by
  rcases Nat.lt_or_ge (CFSG.Open.pRank 3 R) 2 with hlt | hge
  · refine absurd (isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) hR3 ?_) hRnc
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    omega
  · exact hge

theorem false_of_fi22_kStar (hFi : KFactFi22SectionThreeRank) (h : TwelveCtx G M p Q H)
    {X₁ : Subgroup (StarGroup p H)} (hX₁ : X₁ ≤ starImg p H M) {d : ℕ}
    (hK : CFSG.Blueprint.NativeSporadic.IsSporadic ↥(kStar p M H) .Fi22)
    (hW : CFSG.Open.StatedClassicalModel (oPrimeModPrimeComplement d X₁) .POmegaPlus 4 2 1) :
    False := by
  have h3 := three_mem_sigmaA_of_fi22_kStar hFi hK
  obtain ⟨S', hS'X₁, hS'3, hS'nc⟩ := exists_noncyclic_three_subgroup_of_pOmegaPlus hW
  obtain ⟨R, hRM, hR3, hRnc⟩ :=
    exists_noncyclic_three_subgroup_inf h (hS'X₁.trans hX₁) hS'3 hS'nc
  have hRH : R ≤ H := hRM.trans (inf_le_left : H ⊓ M ≤ H)
  have hRMs : R ≤ M := hRM.trans (inf_le_right : H ⊓ M ≤ M)
  have hrank : 2 ≤ CFSG.Open.pRank 3 R := two_le_pRank_three_of_not_isCyclic hR3 hRnc
  exact h.not_H_le_M (h.cstar.embed 3 h3 M h.maxLocal R hRMs hR3 hrank H h.H_twoLocal hRH)

private theorem starImg_inf_eq_of_primeComplementCore_le (h : TwelveCtx G M p Q H) :
    kStar p M H ⊓ starImg p H M = starImg p H (M ⊓ kSub p M H) := by
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  have hOle : O ≤ (M ⊓ H).subgroupOf H := primeComplementCore_le_subgroupOf_of_twelveCtx h
  have hOle' : O ≤ M.subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp (hOle hx)).1
  rw [inf_comm]
  rw [kStar, starImg, starImg,
    ← CFSG.LocalAnalysis.GLTheoremA.I141F.map_inf_of_le_ker (N := O)
      (A := M.subgroupOf H) (B := (kSub p M H).subgroupOf H) hOle']
  congr 1

private theorem starImg_inf_ne_kStar_of_not_kSub_le_M (hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) :
    starImg p H (M ⊓ kSub p M H) ≠ kStar p M H := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  intro heq
  apply not_kSub_le_M_of_nineNineOne h hI
  let K : Subgroup G := kSub p M H
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have hOle : O ≤ (M ⊓ H).subgroupOf H := primeComplementCore_le_subgroupOf_of_twelveCtx h
  have hle_map : starImg p H K ≤ starImg p H (M ⊓ K) := by
    rw [show starImg p H K = kStar p M H from rfl, heq]
  have hle : K.subgroupOf H ≤ (((M ⊓ K).subgroupOf H).map π).comap π := by
    refine Subgroup.map_le_iff_le_comap.mp ?_
    rw [show (K.subgroupOf H).map π = starImg p H K from rfl]
    exact hle_map
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hle
  have hleG : K ≤ (M ⊓ K) ⊔ O.map H.subtype := by
    have h := Subgroup.map_mono (f := H.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le (RankThreeUC.AGL81C.kSub_le p M H),
      Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le ((inf_le_right : M ⊓ K ≤ K).trans
        (RankThreeUC.AGL81C.kSub_le p M H))] at h
    exact h
  have hOM : O.map H.subtype ≤ M := by
    have h := Subgroup.map_mono (f := H.subtype) hOle
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h
    exact h.trans inf_le_left
  exact hleG.trans (sup_le inf_le_left hOM)

omit [Finite G] in
private theorem center_kStar_eq_bot_of_isPSLType_three (hp : p.Prime)
    (hK : IsPSLType 3 (ZMod p) ↥(kStar p M H)) :
    Subgroup.center ↥(kStar p M H) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hK
  have h := Subgroup.map_center_eq e
  rw [CFSG.Quasithin.F420.center_projectiveSpecialLinearGroup_eq_bot (n := 3)
    (by norm_num)] at h
  exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center ↥(kStar p M H))
    (f := e.toMonoidHom) e.injective).mp h

omit [Finite G] in
private theorem inf_centralizer_kStar_eq_bot_of_isPSLType_three (hp : p.Prime)
    (hK : IsPSLType 3 (ZMod p) ↥(kStar p M H)) :
    kStar p M H ⊓ Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) = ⊥ := by
  have hcenter := center_kStar_eq_bot_of_isPSLType_three hp hK
  rw [eq_bot_iff]
  intro x hx
  have hxcenter : (⟨x, hx.1⟩ : ↥(kStar p M H)) ∈ Subgroup.center ↥(kStar p M H) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hx.2 y.1 y.2)
  rw [hcenter] at hxcenter
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxcenter)

private theorem exists_sylow_normalizer_le_M_of_twelveCtx (hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p R H ∧
      Subgroup.normalizer (R : Set G) ≤ M := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hEH : E ≤ H := hEQ.trans h.Q_le_H
  let E' : Subgroup ↥H := E.subgroupOf H
  have hE'p : IsPGroup p E' := hE.isPGroup.comap_subtype (K := H)
  obtain ⟨R, hE'R⟩ := hE'p.exists_le_sylow
  let Rsub : Subgroup G := (R : Subgroup ↥H).map H.subtype
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf p Rsub H := ⟨R, rfl⟩
  have hERsub : E ≤ Rsub := by
    rw [← (show E'.map H.subtype = E by
      dsimp only [E']
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEH])]
    exact Subgroup.map_mono hE'R
  obtain ⟨-, hNRM⟩ :=
    le_M_and_normalizer_le_of_le hI h hEQ hE hEc hΓ hRsyl.isPGroup hERsub
  exact ⟨Rsub, hRsyl, hNRM⟩

private theorem pStar_eq_sup_of_le_sup_centralizer (hp : p.Prime)
    {Pstar : Subgroup (StarGroup p H)}
    (hPstarSylow : CFSG.ABGLocalTools.IsSylowOf p Pstar ⊤)
    (hK : IsPSLType 3 (ZMod p) ↥(kStar p M H))
    (hPstar_le : Pstar ≤ kStar p M H ⊔
      Subgroup.centralizer (kStar p M H : Set (StarGroup p H))) :
    Pstar = (Pstar ⊓ kStar p M H) ⊔
      (Pstar ⊓ Subgroup.centralizer (kStar p M H : Set (StarGroup p H))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdisj := inf_centralizer_kStar_eq_bot_of_isPSLType_three hp hK
  have hcomm : ∀ a ∈ kStar p M H,
      ∀ b ∈ Subgroup.centralizer (kStar p M H : Set (StarGroup p H)), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha
  have hSylowSup : CFSG.ABGLocalTools.IsSylowOf p Pstar
      (kStar p M H ⊔ Subgroup.centralizer (kStar p M H : Set (StarGroup p H))) :=
    hPstarSylow.of_le hPstar_le le_top
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_sylow_eq_sup hcomm hdisj hSylowSup

private theorem normalizer_inf_le_starImg_inf (h : TwelveCtx G M p Q H)
    {Pstar U V : Subgroup (StarGroup p H)} {Rsub : Subgroup G}
    (hV : V = Pstar ⊓ Subgroup.centralizer (kStar p M H : Set (StarGroup p H)))
    (hPstar_eq : Pstar = U ⊔ V)
    (hPstarNorm : Subgroup.normalizer (Pstar : Set (StarGroup p H)) =
      starImg p H (Subgroup.normalizer (Rsub : Set G) ⊓ H))
    (hNRM : Subgroup.normalizer (Rsub : Set G) ≤ M) :
    kStar p M H ⊓ Subgroup.normalizer (U : Set (StarGroup p H)) ≤
      starImg p H (M ⊓ kSub p M H) := by
  have hVle : V ≤ Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
    rw [hV]; exact inf_le_right
  have hKcV : kStar p M H ≤ Subgroup.centralizer (V : Set (StarGroup p H)) :=
    Subgroup.le_centralizer_iff.mpr hVle
  have hNle : kStar p M H ⊓ Subgroup.normalizer (U : Set (StarGroup p H)) ≤
      Subgroup.normalizer (Pstar : Set (StarGroup p H)) := by
    intro x hx
    obtain ⟨hxK, hxN⟩ := hx
    change x ∈ Subgroup.normalizer (U : Set (StarGroup p H)) at hxN
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hxN ⊢
    rw [hPstar_eq, Subgroup.map_sup, hxN,
      show Subgroup.map (↑(MulAut.conj x)) V = V.map (MulAut.conj x).toMonoidHom from rfl,
      CFSG.OddStandard.Solomon75.Sec6SigOdd.map_conj_eq_of_mem_centralizer (hKcV hxK)]
  rw [← starImg_inf_eq_of_primeComplementCore_le h]
  refine le_inf inf_le_left ?_
  intro x hx
  have hx' := hNle hx
  rw [hPstarNorm] at hx'
  exact starImg_mono (inf_le_left.trans hNRM) hx'

theorem isMaxParabolicP_kStar_of_isPSLType_three (hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1)
    (hKn : ((kSub p M H).subgroupOf H).Normal) {D : Subgroup G} (hDM : D ≤ H ⊓ M)
    (hdD : d ∣ Nat.card ↥(starImg p H D)) (hDK : starImg p H D ≤ kStar p M H)
    (hK : IsPSLType 3 (ZMod p) ↥(kStar p M H)) :
    CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p (kStar p M H)
      (starImg p H (M ⊓ kSub p M H)) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hp5 : 5 ≤ p := five_le_of_odd_prime_dvd_add_one h.p_prime h.p_odd hd hd2 hdp
  have hKtype : IsPSLType 3 (ZMod p) ↥(kStar p M H) := hK
  obtain ⟨e⟩ := hK
  have hKstarNormal : (kStar p M H).Normal := Section15.starImg_normal hKn
  have hY := starImg_inf_eq_of_primeComplementCore_le h
  have hYK : starImg p H (M ⊓ kSub p M H) ≤ kStar p M H := starImg_mono inf_le_right
  have hne := starImg_inf_ne_kStar_of_not_kSub_le_M hI h
  have hDY : starImg p H D ≤ starImg p H (M ⊓ kSub p M H) := by
    rw [← hY]
    exact le_inf hDK (starImg_mono (hDM.trans inf_le_right))
  have hdY : d ∣ Nat.card ↥(starImg p H (M ⊓ kSub p M H)) :=
    hdD.trans (Subgroup.card_dvd_of_le hDY)
  obtain ⟨Rsub, hRsyl, hNRM⟩ := exists_sylow_normalizer_le_M_of_twelveCtx hI h
  let Pstar : Subgroup (StarGroup p H) := starImg p H Rsub
  have hPstarSylow : CFSG.ABGLocalTools.IsSylowOf p Pstar ⊤ :=
    Section15.isSylowOf_starImg_top h.p_prime hRsyl
  have hPstarNorm : Subgroup.normalizer (Pstar : Set (StarGroup p H)) =
      starImg p H (Subgroup.normalizer (Rsub : Set G) ⊓ H) :=
    Section15.starImg_normalizer_eq h.p_prime hRsyl.le hRsyl.isPGroup
  have hRK : Pstar ≤ Subgroup.normalizer (kStar p M H : Set (StarGroup p H)) :=
    Subgroup.le_normalizer_of_normal
  have hPstar_le : Pstar ≤ kStar p M H ⊔
      Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) :=
    le_sup_centralizer_of_isPGroup_of_isPSLType_three hp5 hKtype hPstarSylow.isPGroup hRK
  let U : Subgroup (StarGroup p H) := Pstar ⊓ kStar p M H
  let V : Subgroup (StarGroup p H) := Pstar ⊓
    Subgroup.centralizer (kStar p M H : Set (StarGroup p H))
  have hU_sylow : CFSG.ABGLocalTools.IsSylowOf p U (kStar p M H) :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPstarSylow le_top
      (Subgroup.le_normalizer_of_normal)
  have hPstar_eq : Pstar = U ⊔ V :=
    pStar_eq_sup_of_le_sup_centralizer h.p_prime hPstarSylow hKtype hPstar_le
  have hN : kStar p M H ⊓ Subgroup.normalizer (U : Set (StarGroup p H)) ≤
      starImg p H (M ⊓ kSub p M H) :=
    normalizer_inf_le_starImg_inf h rfl hPstar_eq hPstarNorm hNRM
  exact isMaxParabolicP_of_isPSLType_three (A := StarGroup p H) hd hd2 hdp e hYK hne
    hU_sylow hN hdY

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
