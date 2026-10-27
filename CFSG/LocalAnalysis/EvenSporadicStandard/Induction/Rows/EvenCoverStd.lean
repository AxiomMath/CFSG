module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SolStdSubgroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.EvenCoverOutHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.LitX
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24OneOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.StdBareStandard

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

theorem standardComponentIsStandard_of_solStd {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (h : SolStd L) (hq : CFSG.IsQuasisimple ↥L) : CFSG.Open.standardComponentIsStandard L := by
  obtain ⟨hstd, t, ht2, hcomp⟩ := h
  exact standardComponentIsStandard_of_stdBare'
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥L).2.2.1.1 hq)
    (even_card_centralizer_of_le_centralizer ht2 hcomp.le) hstd

theorem oddLieType_top {G : Type} [Group G] (h : OddLieType G) :
    OddLieType ↥(⊤ : Subgroup G) := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := h
  exact ⟨t, n, p, f, hp, hp2, hadm,
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv Subgroup.topEquiv.symm hm⟩

theorem pRank_centralizer_le_one_of_cover (inp : Hyp.Thm24ThreeSimpleInputs)
    {s : TauCeti.SporadicName} (hpin : s ∈ Hyp.pinnedNames) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {L : Subgroup G} (hL : SolStd L)
    (hs : IsSporadic (↥L ⧸ center ↥L) s) :
    CFSG.pRank 2 ↥(centralizer (L : Set G)) ≤ 1 := by
  by_contra hr
  exact Hyp.thm24ThreeCover_simple inp hpin G hnonab hkp L hL hs (by omega)

theorem isCyclic_sylow_of_cover (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hord : ¬ Nat.card ↥(⊤ : Subgroup G) ∣ 95040) {L : Subgroup G} (hL : SolStd L)
    {s : TauCeti.SporadicName}
    (hs : IsSporadic (↥L ⧸ center ↥L) s) (hr : CFSG.pRank 2 ↥(centralizer (L : Set G)) ≤ 1)
    (S : Sylow 2 ↥(centralizer (L : Set G))) :
    IsCyclic ↥(S : Subgroup ↥(centralizer (L : Set G))) := by
  have hrS : CFSG.pRank 2 ↥(S : Subgroup ↥(centralizer (L : Set G))) ≤ 1 :=
    (Hyp.pRank_two_le_of_injective (S : Subgroup ↥(centralizer (L : Set G))).subtype
      (S : Subgroup ↥(centralizer (L : Set G))).subtype_injective).trans hr
  rcases Hyp.isCyclic_or_genQuaternion_of_pRank_le_one S.isPGroup' hrS with hc | hq
  · exact hc
  · exfalso
    have hfs := fStarSimple_top G hnonab
    have hodd := thm24_1 G ⊤ hfs hord L hL ⟨S, hq⟩
    obtain ⟨t, ht2, hcomp⟩ := hL.exists_involution
    exact hlie G ⊤ hfs hodd t ht2 L hcomp s hs

theorem balance_of_even_cover_at (hlie : Hyp.OddLieCompNotSporadic) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hU : Balance.UGTAt G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {L : Subgroup G} (hL : SolStd L)
    {s : TauCeti.SporadicName} (hs : IsSporadic (↥L ⧸ center ↥L) s)
    (hev : ¬ Odd (Nat.card ↥(center ↥L))) :
    ∀ z : G, orderOf z = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({z} : Set G)) = ⊥ := by
  intro z hz
  by_contra hne
  have hfs := fStarSimple_top G hnonab
  obtain ⟨t, ht2, hcomp⟩ := hL.exists_involution
  rcases hU hnonab hkp z hz hne with hodd | ⟨n, h7, -, ⟨e⟩⟩
  · exact hlie G ⊤ hfs (oddLieType_top hodd) t ht2 L hcomp s hs
  · obtain ⟨F, _, _, hF5, ⟨ψ⟩⟩ := Balance.exists_alternating_of_component hfs (Or.inr h7)
      (Subgroup.topEquiv.trans e) ht2 hcomp
    have h4 : 4 ≤ Nat.card F := by omega
    have hZ1 : Nat.card (center ↥L) = 1 := by
      rw [card_center_of_mulEquiv' ψ, alternatingGroup.center_eq_bot h4, Subgroup.card_bot]
    exact hev (by rw [hZ1]; exact odd_one)

theorem isPGroup_center_of_balance {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hL : SolStd L) (ht2 : orderOf t = 2) (hcomp : IsCompIn L (centralizer ({t} : Set G)))
    (hbal : CFSG.Open.standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) :
    IsPGroup 2 ↥(center ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLC : L ≤ centralizer ({t} : Set G) := hcomp.le
  have htL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.2 fun x hx =>
    mem_centralizer_singleton_iff.1 (hLC hx)
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), ∀ l ∈ L, c * l * c⁻¹ ∈ L := fun c hc l hl =>
    (mem_normalizer_iff.1 (hL.centralizer_le_normalizer htL ht2 hc) l).1 hl
  have hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(center ↥L) → q = 2 := by
    intro q hqp hqd
    by_contra hq2
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥L)) q hqd
    have hz' : orderOf ((z : ↥L) : G) = q := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hz
    have hzq : ((z : ↥L) : G) ^ q = 1 := by
      rw [← hz']
      exact pow_orderOf_eq_one _
    have hzc : ∀ l ∈ L, l * ((z : ↥L) : G) = ((z : ↥L) : G) * l := fun l hl =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨l, hl⟩)
    let W : Subgroup ↥(centralizer ({t} : Set G)) :=
      { carrier := {c | (c : G) ∈ L ∧ (∀ l ∈ L, l * (c : G) = (c : G) * l) ∧ (c : G) ^ q = 1}
        mul_mem' := by
          rintro a b ⟨haL, ha, haq⟩ ⟨hbL, hb, hbq⟩
          refine ⟨L.mul_mem haL hbL, fun l hl => ?_, ?_⟩
          · show l * ((a : G) * (b : G)) = ((a : G) * (b : G)) * l
            rw [← mul_assoc, ha l hl, mul_assoc, hb l hl, ← mul_assoc]
          · show ((a : G) * (b : G)) ^ q = 1
            have hab : Commute (a : G) (b : G) := (ha _ hbL).symm
            rw [hab.mul_pow, haq, hbq, one_mul]
        one_mem' := ⟨L.one_mem, fun l _ => by simp, by simp⟩
        inv_mem' := by
          rintro a ⟨haL, ha, haq⟩
          refine ⟨L.inv_mem haL, fun l hl => ?_, ?_⟩
          · show l * (a : G)⁻¹ = (a : G)⁻¹ * l
            exact Commute.inv_right (show Commute l (a : G) from ha l hl)
          · show ((a : G)⁻¹) ^ q = 1
            rw [inv_pow, haq, inv_one] }
    have hWn : W.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨hnL, hnc, hnq⟩ := hn
      have hgC : (g : G) ∈ centralizer ({t} : Set G) := g.2
      have hg'C : (g : G)⁻¹ ∈ centralizer ({t} : Set G) := (g⁻¹).2
      refine ⟨?_, fun l hl => ?_, ?_⟩
      · show (g : G) * (n : G) * (g : G)⁻¹ ∈ L
        exact hnorm g hgC n hnL
      · show l * ((g : G) * (n : G) * (g : G)⁻¹) = ((g : G) * (n : G) * (g : G)⁻¹) * l
        have hm : (g : G)⁻¹ * l * (g : G) ∈ L := by
          have := hnorm _ hg'C l hl
          rwa [inv_inv] at this
        have h1 := hnc _ hm
        calc l * ((g : G) * (n : G) * (g : G)⁻¹)
            = (g : G) * (((g : G)⁻¹ * l * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
          _ = (g : G) * ((n : G) * ((g : G)⁻¹ * l * (g : G))) * (g : G)⁻¹ := by rw [h1]
          _ = ((g : G) * (n : G) * (g : G)⁻¹) * l := by group
      · show ((g : G) * (n : G) * (g : G)⁻¹) ^ q = 1
        rw [conj_pow, hnq, mul_one, mul_inv_cancel]
    have hWodd : Odd (Nat.card W) := by
      by_contra hne
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 2
        (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne))
      have hw2 : orderOf (((w : ↥(centralizer ({t} : Set G))) : G)) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hw
      have hdvd : 2 ∣ q := hw2 ▸ orderOf_dvd_of_pow_eq_one w.2.2.2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).1 hdvd).symm
    have hWle : W ≤ CFSG.Open.standardComponentOddCore ↥(centralizer ({t} : Set G)) :=
      le_sSup ⟨hWn, hWodd⟩
    rw [hbal, le_bot_iff] at hWle
    have hzW : (⟨((z : ↥L) : G), hLC (z : ↥L).2⟩ : ↥(centralizer ({t} : Set G))) ∈ W :=
      ⟨(z : ↥L).2, hzc, hzq⟩
    rw [hWle, Subgroup.mem_bot] at hzW
    have hz1' : ((z : ↥L) : G) = 1 := congrArg Subtype.val hzW
    have hz1 : z = 1 := Subtype.ext (Subtype.ext hz1')
    rw [hz1, orderOf_one] at hz
    exact hqp.one_lt.ne hz
  have hcard : Nat.card ↥(center ↥L) = 2 ^ (Nat.card ↥(center ↥L)).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdd => hprime d hd hdd
  exact IsPGroup.of_card hcard

theorem stdHyp_of_balanced_cover (thm24_1 : Sol78Thm24_1Use) (inp : Hyp.Thm24ThreeSimpleInputs)
    (hlie : Hyp.OddLieCompNotSporadic) {s : TauCeti.SporadicName} (hpin : s ∈ Hyp.pinnedNames)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hbal : ∀ z : G, orderOf z = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({z} : Set G)) = ⊥)
    {L : Subgroup G} (hL : SolStd L) (hq : CFSG.IsQuasisimple ↥L)
    (hZ : Nat.card ↥(center ↥L) = 2) (hs : IsSporadic (↥L ⧸ center ↥L) s) : StdHyp G L := by
  have hr := pRank_centralizer_le_one_of_cover inp hpin hnonab hkp hL hs
  have hord : ¬ Nat.card ↥(⊤ : Subgroup G) ∣ 95040 :=
    Hyp.not_card_dvd_95040_of_cover inp hpin (le_top : L ≤ ⊤) hq hs
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer (L : Set G))) := inferInstance
  exact ⟨inferInstance, hnonab, hkp, standardComponentIsStandard_of_solStd hL hq, hbal,
    ⟨S, isCyclic_sylow_of_cover thm24_1 hlie hnonab hord hL hs hr S⟩,
    IsPGroup.of_card (n := 1) (by rw [hZ]; norm_num)⟩

structure CoverReductionH : Prop where
  thm24_1 : Sol78Thm24_1Use
  thm24_3 : Hyp.Thm24ThreeSimpleInputs
  lie : Hyp.OddLieCompNotSporadic
  central : CentralTwoBound

theorem stdHyp_of_even_cover_at (R : CoverReductionH) {s : TauCeti.SporadicName}
    (hpin : s ∈ Hyp.pinnedNames) (h2 : twoPartBound s ∣ 2) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hU : Balance.UGTAt G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {L : Subgroup G} (hL : SolStd L)
    (hq : CFSG.IsQuasisimple ↥L) (hs : IsSporadic (↥L ⧸ center ↥L) s)
    (hev : ¬ Odd (Nat.card ↥(center ↥L))) : StdHyp G L ∧ Nat.card ↥(center ↥L) = 2 := by
  have hbal := balance_of_even_cover_at R.lie hU hnonab hkp hL hs hev
  obtain ⟨t, ht2, hcomp⟩ := hL.exists_involution
  have hZ2 : IsPGroup 2 ↥(center ↥L) := isPGroup_center_of_balance hL ht2 hcomp (hbal t ht2)
  obtain ⟨hdvd, -⟩ := R.central ↥L
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥L).2.2.1.1 hq) hZ2 s hs
  have hZ : Nat.card ↥(center ↥L) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (hdvd.trans h2) with h | h
    · exact absurd (by rw [h]; exact odd_one) hev
    · exact h
  exact ⟨stdHyp_of_balanced_cover R.thm24_1 R.thm24_3 R.lie hpin hnonab hkp hbal hL hq hZ hs, hZ⟩

theorem exists_cover_in_fStar {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2) {L : Subgroup Y} (hL : SolStd L)
    (hq : CFSG.IsQuasisimple ↥L) (hev : ¬ Odd (Nat.card ↥(center ↥L)))
    {s : TauCeti.SporadicName} (hs : IsSporadic (↥L ⧸ center ↥L) s) :
    ∃ L' : Subgroup ↥N', SolStd L' ∧ CFSG.IsQuasisimple ↥L' ∧
      Nat.card ↥(center ↥L') = Nat.card ↥(center ↥L) ∧
      IsSporadic (↥L' ⧸ center ↥L') s := by
  have hNn : N'.Normal := hN.normal
  have hLN : L ≤ N' := Hyp.le_of_perfect_of_index_le_two hidx hq.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥L)) 2
    (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev))
  have hr2 : orderOf ((r : ↥L) : Y) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hr
  have hrC : ((r : ↥L) : Y) ∈ centralizer (L : Set Y) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 r.2 ⟨y, hy⟩)
  let φ : ↥(L.subgroupOf N') ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLN
  refine ⟨L.subgroupOf N', solStd_subgroupOf hLN (hLN (r : ↥L).2) hr2 hrC hL,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hq, card_center_of_mulEquiv' φ, ?_⟩
  obtain ⟨e⟩ := hs
  exact ⟨(quotientCenterEquiv' φ).trans e⟩

theorem exists_stdHyp_of_even_cover_at (R : CoverReductionH) {s : TauCeti.SporadicName}
    (hpin : s ∈ Hyp.pinnedNames) (h2 : twoPartBound s ∣ 2) {Y : Type} [Group Y] [Finite Y]
    (hY : Balance.UHered Y) {N' : Subgroup Y} (hN : FStarSimple N') (hidx : N'.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {L : Subgroup Y} (hL : SolStd L)
    (hq : CFSG.IsQuasisimple ↥L) (hs : IsSporadic (↥L ⧸ center ↥L) s)
    (hev : ¬ Odd (Nat.card ↥(center ↥L))) :
    ∃ L' : Subgroup ↥N', StdHyp ↥N' L' ∧ Nat.card ↥(center ↥L') = 2 ∧
      IsSporadic (↥L' ⧸ center ↥L') s := by
  obtain ⟨L', hL', hq', hc, hs'⟩ := exists_cover_in_fStar hN hidx hL hq hev hs
  have := hN.isSimpleGroup
  have hkp' : CFSG.Assembly.KProper CFSG.Blueprint.Catalog ↥N' :=
    Hyp.kProper_of_section hkp N' (MonoidHom.id ↥N') Function.surjective_id
  obtain ⟨hStd, hZ⟩ := stdHyp_of_even_cover_at R hpin h2
    (hY ↥N' (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup N'))
    hN.nonabelian hkp' hL' hq' hs' (by rw [hc]; exact hev)
  exact ⟨L', hStd, hZ, hs'⟩

theorem evenCoverOutHered_of_child (R : CoverReductionH) {s : TauCeti.SporadicName}
    (hpin : s ∈ Hyp.pinnedNames) (h2 : twoPartBound s ∣ 2) {Up : List TauCeti.SporadicName}
    (hchild : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
      Nat.card ↥(center ↥L) = 2 → IsSporadic (↥L ⧸ center ↥L) s → ∃ s'' ∈ Up, IsSporadic G s'') :
    EvenCoverOutHered Up s := by
  intro Y _ _ hY N' hN hidx hkp L hsol hq hcq hodd
  obtain ⟨L', hStd, hZ, hs'⟩ :=
    exists_stdHyp_of_even_cover_at R hpin h2 hY hN hidx hkp hsol hq hcq hodd
  have := hN.isSimpleGroup
  exact hchild ↥N' L' hStd hZ hs'

theorem evenCoverExclHered_of_noStd (R : CoverReductionH) {s : TauCeti.SporadicName}
    (hpin : s ∈ Hyp.pinnedNames) (h2 : twoPartBound s ∣ 2)
    (hno : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
      Nat.card ↥(center ↥L) = 2 → ¬ IsSporadic (↥L ⧸ center ↥L) s) : EvenCoverExclHered s :=
  evenCoverOutHered_of_child R hpin h2 fun G _ _ L h hZ hs => absurd hs (hno G L h hZ)

end CFSG.EvenSporadicStandard.Induction
