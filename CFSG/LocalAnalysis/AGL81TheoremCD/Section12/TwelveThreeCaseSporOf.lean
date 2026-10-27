module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineApply
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineSocle
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicTable
public import CFSG.Sporadic.Schreier.TitsAutD
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeYTransport
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeOrders
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.DResidualSimple
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.HypC
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
import CFSG.LocalAnalysis.RankThreeUC.AGL81CKStarComponent
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoONan
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Induction
public import CFSG.RankThree.PartOne.Mult.Sec68
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.OrderCheckF
public import CFSG.Sporadic.Fi24
public import CFSG.Sporadic.Recognition.HNMultiplier
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelYAut
public import CFSG.Sporadic.Recognition.LyonsFinalDist2
public import CFSG.Sporadic.Suz
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenConstrained

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer congr_mem_inner_iff)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem threeNineSocleCase_congr {X X' : Type} [Group X] [Finite X] [Group X']
    [Finite X'] {K X₁ : Subgroup X} {K' X₁' : Subgroup X'} {p d : ℕ} (eK : ↥K ≃* ↥K')
    (eX : ↥X₁ ≃* ↥X₁') (h : ThreeNineSocleCase K X₁ p d) : ThreeNineSocleCase K' X₁' p d := by
  obtain ⟨eW⟩ := CFSG.LocalAnalysis.AGL81I.Section3.oPrimeModPrimeComplement_congr d eX
  rcases h with ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩ |
    ⟨hp, hd, hK, hW⟩
  · exact Or.inl ⟨hp, hd, CFSG.SectionRank.reeTitsModel_of_mulEquiv eK.symm hK,
      Nonempty.map (fun e => eW.symm.trans e) hW⟩
  · exact Or.inr (Or.inl ⟨hp, hd, Nonempty.map (fun e => eK.symm.trans e) hK,
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eW hW⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hp, hd, Nonempty.map (fun e => eK.symm.trans e) hK,
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eW.symm hW⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hd, Nonempty.map (fun e => eK.symm.trans e) hK,
      Nonempty.map (fun e => eW.symm.trans e) hW⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, hd, Nonempty.map (fun e => eK.symm.trans e) hK,
      Nonempty.map (fun e => eW.symm.trans e) hW⟩)))

omit [Finite G] in
private theorem coe_mem_xSub_iff (z : ↥H) :
    (z : G) ∈ xSub p M H ↔ QuotientGroup.mk' (primeComplementCore (G := ↥H) p) z ∈
      Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
  refine ⟨fun hz => ?_, fun hz => ⟨z, hz, rfl⟩⟩
  obtain ⟨w, hw, hwz⟩ := hz
  rw [← Subtype.ext hwz]
  exact hw

private theorem map_eq_bot_of_range_eq_oPPrimeHull {A B : Type*} [Group A] [Finite A] [Group B]
    [Finite B] {d : ℕ} (hd : d.Prime) (f : A →* B) {T : Subgroup B}
    (hT : f.range = oPPrimeHull d T) (hs : IsSimpleGroup ↥(oPPrimeHull d T)) {P : Subgroup A}
    (hP : P.Normal) (hPd : ¬ d ∣ Nat.card P) : P.map f = ⊥ := by
  have : IsSimpleGroup ↥f.range := by rw [hT]; exact hs
  have : (P.map f.rangeRestrict).Normal := hP.map _ f.rangeRestrict_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map f.rangeRestrict) with hb | ht
  · rw [Subgroup.map_eq_bot_iff] at hb ⊢
    rwa [MonoidHom.ker_rangeRestrict] at hb
  · have hdvd : Nat.card f.range ∣ Nat.card P := by
      rw [← Subgroup.card_top (G := ↥f.range), ← ht]
      exact Subgroup.card_map_dvd _ _
    have hbot := map_oPPrimeHull_eq_bot_of_not_dvd_card hd (A := T) (MonoidHom.id B)
      (by rw [Subgroup.map_id, ← hT]; exact fun h => hPd (h.trans hdvd))
    rw [Subgroup.map_id] at hbot
    exact absurd hbot ((Subgroup.nontrivial_iff_ne_bot _).mp hs.toNontrivial)

private theorem mem_inner_of_card_outer_le_two_of_odd {T : Type} [Group T] [Finite T] {n : ℕ}
    (hn : Odd n) (hT : Nat.card (Outer T) ≤ 2) {α : MulAut T} (hα : α ^ n = 1) :
    α ∈ inner T := by
  have : Nonempty (Outer T) := ⟨1⟩
  have : Finite (Outer T) := inferInstance
  let β : Outer T := QuotientGroup.mk' (inner T) α
  have hβ : orderOf β ∣ n := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hα, map_one])
  have hle : orderOf β ≤ 2 := (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard β)).trans hT
  obtain ⟨k, hk⟩ := hn.of_dvd_nat hβ
  have h1 : orderOf β = 1 := by omega
  exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp h1)

private theorem mem_inner_of_mulEquiv_of_odd {K T : Type} [Group K] [Group T] [Finite T]
    (e : K ≃* T) (hT : Nat.card (Outer T) ≤ 2) {n : ℕ} (hn : Odd n) {α : MulAut K}
    (hα : α ^ n = 1) : α ∈ inner K :=
  (congr_mem_inner_iff e α).mp
    (mem_inner_of_card_outer_le_two_of_odd hn hT (by rw [← map_pow, hα, map_one]))

private theorem socle_of_threeNineSocleCase (hI : NineNineOneInput)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (hsoc : KFactThreeNineSocle)
    (h : TwelveCtx G M p Q H) (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥)
    (hDK : starImg p H D ≤ kStar p M H)
    (hcase : ThreeNineSocleCase (kStar p M H) (starImg p H M ⊓ kStar p M H) p d)
    (hK : CFSG.IsComponent (kStar p M H)) (hKM : ¬ kStar p M H ≤ starImg p H M) :
    IsSimpleGroup ↥(oPPrimeHull d (starImg p H M ⊓ kStar p M H)) ∧
      ∀ k ∈ kStar p M H, (∀ y ∈ oPPrimeHull d (starImg p H M ⊓ kStar p M H), y * k = k * y) →
        k = 1 := by
  have : Fact d.Prime := ⟨sigmaA_prime d hd.1⟩
  have hKN : kStar p M H ≤ Subgroup.normalizer (kStar p M H : Set (StarGroup p H)) :=
    Subgroup.le_normalizer
  have hXN := (inf_le_right : starImg p H M ⊓ kStar p M H ≤ kStar p M H).trans hKN
  obtain ⟨E, hE⟩ := threeNineHyp_of_twelveCtx hI hbridge h hns hd hXM hD hD1 hK hKM
  rw [sup_eq_left.mpr hDK] at hE
  obtain ⟨hs, hc⟩ := hsoc _ _ _ _ _ p d hE
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hDK (Subgroup.mem_subgroupOf.mp hx)))
    (threeNineSocleCase_congr (Subgroup.subgroupOfEquivOfLe hKN).symm
      (Subgroup.subgroupOfEquivOfLe hXN).symm hcase)
  rw [← oPPrimeHull_subgroupOf_of_le hXN] at hs hc
  have := hs
  refine ⟨MulEquiv.isSimpleGroup
    (Subgroup.subgroupOfEquivOfLe ((oPPrimeHull_le d _).trans hXN)).symm, fun k hk hck => ?_⟩
  have hmem := (Subgroup.eq_bot_iff_forall _).mp hc ⟨k, hKN hk⟩
    ⟨Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subtype.ext (hck y (Subgroup.mem_subgroupOf.mp hy)), hk⟩
  exact congrArg Subtype.val hmem

private theorem range_eq_oPPrimeHull (h : TwelveCtx G M p Q H) {d : ℕ} [Fact d.Prime]
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hDK : starImg p H D ≤ kStar p M H) :
    ((QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp
      (Subgroup.inclusion ((oPPrimeHull_le d (H ⊓ M)).trans inf_le_left))).range =
      oPPrimeHull d (starImg p H M ⊓ kStar p M H) := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range,
    oPPrimeHull_inf_eq_of_isSylowOf_starImg Fact.out
      (not_dvd_card_primeComplementCore_of_twelveCtx h hXM) hD hDK
      (starImg_le_normalizer_kStar p M H),
    oPPrimeHull_subgroupOf_of_le (inf_le_left : H ⊓ M ≤ H), S631.map_oPPrimeHull,
    Subgroup.inf_subgroupOf_left]
  rfl

private theorem primeComplementCore_map_le_xSub (h : TwelveCtx G M p Q H) {d : ℕ}
    [Fact d.Prime] (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hDK : starImg p H D ≤ kStar p M H)
    (hs : IsSimpleGroup ↥(oPPrimeHull d (starImg p H M ⊓ kStar p M H))) :
    (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore
        (G := ↥(oPPrimeHull d (H ⊓ M))) d).map (oPPrimeHull d (H ⊓ M)).subtype ≤
      xSub p M H := by
  have hYH : oPPrimeHull d (H ⊓ M) ≤ H := (oPPrimeHull_le d (H ⊓ M)).trans inf_le_left
  have hP := CFSG.RankThreeEvenClassification.Helpers.primeComplementCore_properties
    ↥(oPPrimeHull d (H ⊓ M)) d Fact.out
  have hbot := map_eq_bot_of_range_eq_oPPrimeHull Fact.out _ (range_eq_oPPrimeHull h hXM hD hDK)
    hs hP.1 hP.2
  rintro _ ⟨y, hy, rfl⟩
  have h1 : QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨(y : G), hYH y.2⟩ = 1 :=
    MonoidHom.mem_ker.mp ((Subgroup.map_eq_bot_iff _).mp hbot hy)
  refine (coe_mem_xSub_iff ⟨(y : G), hYH y.2⟩).mpr ?_
  rw [h1]
  exact Subgroup.one_mem _

private theorem mem_xSub_of_commutator_mem {d : ℕ} {Y₁ : Subgroup (StarGroup p H)}
    (hY₁ : Y₁ ≤ kStar p M H) (hcent : ∀ k ∈ kStar p M H, (∀ y ∈ Y₁, y * k = k * y) → k = 1)
    (hY : ∀ y ∈ Y₁, ∃ y₀ : ↥H, (y₀ : G) ∈ oPPrimeHull d (H ⊓ M) ∧
      QuotientGroup.mk' (primeComplementCore (G := ↥H) p) y₀ = y)
    {x : G} (hx : x ∈ kSub p M H ⊔ xSub p M H)
    (hc : ∀ y ∈ oPPrimeHull d (H ⊓ M), x * y * x⁻¹ * y⁻¹ ∈ xSub p M H) : x ∈ xSub p M H := by
  have hle : kSub p M H ⊔ xSub p M H ≤ ((kStar p M H ⊔ Subgroup.centralizer
      (kStar p M H : Set (StarGroup p H))).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))).map H.subtype :=
    sup_le (fun k hk => ⟨⟨k, Section14.kSub_le p M H hk⟩, Subgroup.mem_sup_left
        ⟨⟨k, Section14.kSub_le p M H hk⟩, hk, rfl⟩, rfl⟩)
      fun _ ⟨w, hw, hwx⟩ => ⟨w, Subgroup.mem_sup_right hw, hwx⟩
  obtain ⟨z, hz, rfl⟩ := hle hx
  have hz' : QuotientGroup.mk' (primeComplementCore (G := ↥H) p) z ∈
      ((kStar p M H ⊔ Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) :
        Subgroup (StarGroup p H)) : Set (StarGroup p H)) := hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (Subgroup.centralizer_le_normalizer _)] at hz'
  obtain ⟨k, hk, c, hcC, hkc⟩ := Set.mem_mul.mp hz'
  have hk1 : k = 1 := hcent k hk fun y hy => by
    obtain ⟨y₀, hy₀, rfl⟩ := hY y hy
    have h1 := (coe_mem_xSub_iff (z * y₀ * z⁻¹ * y₀⁻¹)).mp (by simpa using hc _ hy₀)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hkc] at h1
    have hcy : c * QuotientGroup.mk' (primeComplementCore (G := ↥H) p) y₀ * c⁻¹ =
        QuotientGroup.mk' (primeComplementCore (G := ↥H) p) y₀ := by
      rw [← Subgroup.mem_centralizer_iff.mp hcC _ (hY₁ hy), mul_inv_cancel_right]
    have hw : k * QuotientGroup.mk' (primeComplementCore (G := ↥H) p) y₀ * k⁻¹ *
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) y₀)⁻¹ ∈
        Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
      convert h1 using 1
      calc _ = k * (c * QuotientGroup.mk' (primeComplementCore (G := ↥H) p) y₀ * c⁻¹) * k⁻¹ *
            (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) y₀)⁻¹ := by rw [hcy]
        _ = _ := by group
    have hw1 := hcent _ (mul_mem (mul_mem (mul_mem hk (hY₁ hy)) (inv_mem hk)) (inv_mem (hY₁ hy)))
      fun y' hy' => Subgroup.mem_centralizer_iff.mp hw y' (hY₁ hy')
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hw1
    exact hw1.symm
  rw [hk1, one_mul] at hkc
  exact (coe_mem_xSub_iff z).mpr (hkc ▸ hcC)

omit [Finite G] in
private theorem mem_kSub_sup_xSub_of_odd (hKn : ((kSub p M H).subgroupOf H).Normal)
    (hinn : ∀ n : ℕ, Odd n → ∀ α : MulAut ↥(kStar p M H), α ^ n = 1 →
      α ∈ inner ↥(kStar p M H))
    {g : G} (hg : g ∈ H) (hodd : Odd (orderOf g)) : g ∈ kSub p M H ⊔ xSub p M H := by
  have : (kStar p M H).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  let g' : ↥H := ⟨g, hg⟩
  have hg1 : g' ^ orderOf g = 1 := Subtype.ext (by simp [g', pow_orderOf_eq_one])
  obtain ⟨k, hk⟩ := hinn _ hodd
    (MulAut.conjNormal (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) g'))
    (by rw [← map_pow, ← map_pow, hg1, map_one, map_one])
  have hc : (k : StarGroup p H)⁻¹ * QuotientGroup.mk' (primeComplementCore (G := ↥H) p) g' ∈
      Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hkx := congrArg
      (fun φ : MulAut ↥(kStar p M H) => ((φ ⟨x, hx⟩ : ↥(kStar p M H)) : StarGroup p H)) hk
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at hkx
    calc x * ((k : StarGroup p H)⁻¹ * QuotientGroup.mk' (primeComplementCore (G := ↥H) p) g')
        = (k : StarGroup p H)⁻¹ * ((k : StarGroup p H) * x * (k : StarGroup p H)⁻¹) *
          QuotientGroup.mk' (primeComplementCore (G := ↥H) p) g' := by group
      _ = _ := by rw [hkx]; group
  obtain ⟨k₀, hk₀, hk₀k⟩ := k.2
  have hx : ((k₀⁻¹ * g' : ↥H) : G) ∈ xSub p M H :=
    (coe_mem_xSub_iff _).mpr (by rwa [map_mul, map_inv, hk₀k])
  have hgk : g = (k₀ : G) * ((k₀⁻¹ * g' : ↥H) : G) := by simp [g']
  rw [hgk]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk₀))
    (Subgroup.mem_sup_right hx)

private theorem twelveThreeCaseSpor_of_inputs (hI : NineNineOneInput)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (hsoc : KFactThreeNineSocle)
    (h : TwelveCtx G M p Q H) (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) (hA : ¬ pLayerIn p H ≤ M)
    (hKn : ((kSub p M H).subgroupOf H).Normal) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥)
    (hDK : starImg p H D ≤ kStar p M H)
    (hcase : ThreeNineSocleCase (kStar p M H) (starImg p H M ⊓ kStar p M H) p d)
    (hAlt : TwelveThreeAltThree M p H d ∨ TwelveThreeAltFour M p H d ∨
      TwelveThreeAltFive M p H d)
    (hsim : IsSimpleGroup ↥(kStar p M H) ∧ ¬ Group.IsSolvable ↥(kStar p M H))
    (hout : ∃ (T : Type) (_ : Group T), Nonempty (↥(kStar p M H) ≃* T) ∧
      Nat.card (Outer T) ≤ 2) :
    TwelveThreeCaseSpor M p H d := by
  have : Fact d.Prime := ⟨sigmaA_prime d hd.1⟩
  obtain ⟨E₀, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have := hsim.1
  have hq : CFSG.IsQuasisimple ↥(kStar p M H) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (by
      by_contra hc
      exact hsim.2 (isSolvable_of_comm fun a b => not_not.mp fun hab => hc ⟨a, b, hab⟩))).1
  obtain ⟨hK, hKM⟩ := (nineSettingGen h hEQ hE hEc hΓ).isComponent_kStar_of_isQuasisimple hA hq
  obtain ⟨hs, hcent⟩ :=
    socle_of_threeNineSocleCase hI hbridge hsoc h hns hd hXM hD hD1 hDK hcase hK hKM
  obtain ⟨T, _, ⟨e⟩, hT⟩ := hout
  have : Finite T := Finite.of_equiv _ e.toEquiv
  refine ⟨hA, hKn, hAlt, primeComplementCore_map_le_xSub h hXM hD hDK hs,
    fun x hx hc => mem_xSub_of_commutator_mem ((oPPrimeHull_le d _).trans inf_le_right) hcent
      (fun y hy => ?_) hx.2 hc,
    fun g hg hodd => mem_kSub_sup_xSub_of_odd hKn
      (fun _ hn _ hα => mem_inner_of_mulEquiv_of_odd e hT hn hα) hg hodd⟩
  rw [← range_eq_oPPrimeHull h hXM hD hDK] at hy
  obtain ⟨y₀, rfl⟩ := hy
  exact ⟨Subgroup.inclusion _ y₀, y₀.2, rfl⟩

section Holds


theorem twelveThreeCaseSpor_of_threeNineSocleCase (hI : NineNineOneInput)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (hsoc : KFactThreeNineSocle)
    (h : TwelveCtx G M p Q H) (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) (hA : ¬ pLayerIn p H ≤ M)
    (hKn : ((kSub p M H).subgroupOf H).Normal) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥)
    (hDK : starImg p H D ≤ kStar p M H)
    (hcase : ThreeNineSocleCase (kStar p M H) (starImg p H M ⊓ kStar p M H) p d)
    (hAlt : TwelveThreeAltThree M p H d ∨ TwelveThreeAltFour M p H d ∨
      TwelveThreeAltFive M p H d) :
    TwelveThreeCaseSpor M p H d := by
  have key : ∀ n, IsSimpleOfOrder n ↥(kStar p M H) →
      IsSimpleGroup ↥(kStar p M H) ∧ ¬ Group.IsSolvable ↥(kStar p M H) := fun _ hn =>
    ⟨(isSimpleOfOrder_iff.mp hn).1, (isSimpleOfOrder_iff.mp hn).2.1⟩
  have hsim : IsSimpleGroup ↥(kStar p M H) ∧ ¬ Group.IsSolvable ↥(kStar p M H) := by
    rcases hcase with ⟨-, -, hK, -⟩ | ⟨-, -, hK, -⟩ | ⟨-, -, hK, -⟩ | ⟨-, -, hK, -⟩ |
      ⟨-, -, hK, -⟩
    · exact key _ (isSimpleOfOrder_of_reeTitsModel_tits hK)
    · exact key _ (isSimpleOfOrder_of_isSporadic_HS hK)
    · exact key _ (isSimpleOfOrder_of_isSporadic_Ly hK)
    · exact key _ (isSimpleOfOrder_of_isSporadic_ONan hK)
    · exact key _ (isSimpleOfOrder_of_isSporadic_Fi24Prime hK)
  have hout : ∃ (T : Type) (_ : Group T), Nonempty (↥(kStar p M H) ≃* T) ∧
      Nat.card (Outer T) ≤ 2 := by
    rcases hcase with ⟨-, -, hK, -⟩ | ⟨-, -, hK, -⟩ | ⟨-, -, hK, -⟩ | ⟨-, -, hK, -⟩ |
      ⟨-, -, hK, -⟩
    · exact ⟨_, _, CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hK,
        CFSG.Sporadic.Schreier.Tits.card_outer_titsD.le⟩
    · exact ⟨_, _, hK, CFSG.AGLEmbeddingD2.card_outer_carrier_le_two_of_ne_M .HS (by decide)⟩
    · exact ⟨_, _, hK, CFSG.AGLEmbeddingD2.card_outer_carrier_le_two_of_ne_M .Ly (by decide)⟩
    · exact ⟨_, _, hK, CFSG.AGLEmbeddingD2.card_outer_carrier_le_two_of_ne_M .ONan (by decide)⟩
    · exact ⟨_, _, hK,
        CFSG.AGLEmbeddingD2.card_outer_carrier_le_two_of_ne_M .Fi24Prime (by decide)⟩
  exact twelveThreeCaseSpor_of_inputs hI hbridge hsoc h hns hd hXM hA hKn hD hD1 hDK hcase hAlt
    hsim hout

end Holds

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
