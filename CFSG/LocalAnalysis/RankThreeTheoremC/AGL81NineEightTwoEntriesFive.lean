module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntries
import CFSG.GroupTheory.ElemAbelianPlaneAction
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoCriteria
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesThree
import CFSG.RankThree.PartOne.KS.HSMcL
import CFSG.RankThree.PartOne.KS.Ru
import CFSG.Sporadic.Bridge.HSSurj
import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.RankThree.Native.HSMcLFiveData
public import CFSG.RankThree.PartOne.KS.RuFiveData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open Subgroup

section Model

variable {G : Type} [Group G] [Finite G]

private theorem commutator_mem_of_card {p : ℕ} [Fact p.Prime] {A Z : Subgroup G}
    (hA : Nat.card A = p ^ 3) (hZ : Nat.card Z = p) (hZA : Z ≤ A)
    (hZc : ∀ a ∈ A, ∀ c ∈ Z, a * c = c * a) {w b : G} (hw : w ∈ A) (hb : b ∈ A) :
    w * b * w⁻¹ * b⁻¹ ∈ Z := by
  set N : Subgroup A := Z.subgroupOf A with hNdef
  haveI : N.Normal := ⟨fun n hn g => by
    rw [hNdef, mem_subgroupOf] at hn ⊢
    have e : ((g * n * g⁻¹ : A) : G) = n := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hZc g g.2 n hn,
        mul_inv_cancel_right]
    rw [e]
    exact hn⟩
  have hN : Nat.card N = p := by
    rw [hNdef, Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv, hZ]
  have hQ : Nat.card (↥A ⧸ N) = p ^ 2 := by
    have h := N.card_eq_card_quotient_mul_card_subgroup
    rw [hA, hN, show p ^ 3 = p ^ 2 * p by ring] at h
    exact (Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h).symm
  have hc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ).is_comm.comm
    (QuotientGroup.mk (⟨w, hw⟩ : A) : ↥A ⧸ N) (QuotientGroup.mk (⟨b, hb⟩ : A))
  have h1 : ((⟨w, hw⟩ * ⟨b, hb⟩ * (⟨w, hw⟩ : A)⁻¹ * (⟨b, hb⟩ : A)⁻¹ : A) : ↥A ⧸ N) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc, mul_inv_cancel_right,
      mul_inv_cancel]
  rw [QuotientGroup.eq_one_iff, hNdef, mem_subgroupOf] at h1
  exact h1

theorem kFactNineThreeNoTwoAt_of_autModel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P R C A : Subgroup G} (h : CFSG.Sporadic.SmallOddCore.AutModel P R) {x : G} (hxR : x ∈ R)
    (hC : C = centralizer {x} ⊓ R) (hAC : A ≤ C) (hAn : (A.subgroupOf C).Normal)
    (hAP : A ≤ P) (hA : Nat.card A = p ^ 3) (hAexp : Monoid.exponent A = p)
    (hZ : Nat.card (centralizer (A : Set G) ⊓ C : Subgroup G) = p)
    (hZA : centralizer (A : Set G) ⊓ C ≤ A)
    (hP2 : ¬ 2 ^ (p * orderOf (2 : ZMod p)) ∣ Nat.card P) {i : TauCeti.CFSGIndex}
    (hM : Nonempty (P ≃* i.Group)) : KFactNineThreeNoTwoAt p i := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup G := centralizer (A : Set G) ⊓ C
  have hCx : ∀ g ∈ C, g * x = x * g := fun g hg => by
    rw [hC] at hg
    exact mem_centralizer_singleton_iff.mp hg.1
  have hxC : x ∈ C := by
    rw [hC]
    exact ⟨mem_centralizer_singleton_iff.mpr rfl, hxR⟩
  have hxZ : x ∈ Z := ⟨mem_centralizer_iff.mpr fun a ha => hCx a (hAC ha), hxC⟩
  have hxA : x ∈ A := hZA hxZ
  have hxP : x ∈ P := hAP hxA
  have hZc : ∀ a ∈ A, ∀ c ∈ Z, a * c = c * a := fun a ha c hc =>
    mem_centralizer_iff.mp hc.1 a ha
  have hApow : ∀ a ∈ A, a ^ p = 1 := fun a ha => by
    have e := Monoid.pow_exponent_eq_one (⟨a, ha⟩ : A)
    rw [hAexp] at e
    simpa using congrArg Subtype.val e
  have hcen : center P = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [mem_bot]
    refine Subtype.ext (h.inj g (h.le g.2) fun q hq => ?_)
    exact (congrArg Subtype.val (mem_center_iff.mp hg ⟨q, hq⟩)).symm
  have hhom : ∀ q : P, h.hom (MulAut.conj q) = q := fun q =>
    (h.hom_apply _).trans (h.elt_eq (h.le q.2) fun r => by simp [MulAut.conj_apply])
  set T : Subgroup P := A.subgroupOf P with hTdef
  have hT : IsPGroup p T :=
    IsPGroup.of_card (n := 3) (by rw [hTdef, Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv, hA])
  have hzT : (⟨x, hxP⟩ : P) ∈ T := mem_subgroupOf.mpr hxA
  have hTz : T ≤ centralizer ({⟨x, hxP⟩} : Set P) := fun t ht =>
    mem_centralizer_singleton_iff.mpr (Subtype.ext (hCx t (hAC (mem_subgroupOf.mp ht))))
  have hCN : C ≤ normalizer (A : Set G) := le_normalizer_of_normal_subgroupOf (hK := hAn) hAC
  have hzQ : centralizer ({⟨x, hxP⟩} : Set P) ≤ normalizer (T : Set P) := by
    intro k hk
    have hkC : (k : G) ∈ C := by
      rw [hC]
      exact ⟨mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hk)), h.le k.2⟩
    rw [mem_normalizer_iff]
    intro q
    rw [hTdef, mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp (hCN hkC) q
  have hCQ : centralizer ({MulAut.conj (⟨x, hxP⟩ : P)} : Set (MulAut P)) ⊓
      centralizer ((T.map (MulAut.conj : P →* MulAut P) : Subgroup (MulAut P)) :
        Set (MulAut P)) ≤ T.map (MulAut.conj : P →* MulAut P) := by
    rintro α ⟨hαx, hαT⟩
    have hyx : h.hom α * x = x * h.hom α := by
      have e := congrArg h.hom (mem_centralizer_singleton_iff.mp hαx)
      rwa [map_mul, map_mul, hhom] at e
    have hyA : h.hom α ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have e := congrArg h.hom (mem_centralizer_iff.mp hαT (MulAut.conj ⟨a, hAP ha⟩)
        ⟨⟨a, hAP ha⟩, mem_subgroupOf.mpr ha, rfl⟩)
      rwa [map_mul, map_mul, hhom] at e
    have hyC : h.hom α ∈ C := by
      rw [hC]
      exact ⟨mem_centralizer_singleton_iff.mpr hyx, h.elt_mem α⟩
    have hyA' : h.hom α ∈ A := hZA ⟨hyA, hyC⟩
    refine ⟨⟨h.hom α, hAP hyA'⟩, mem_subgroupOf.mpr hyA', h.hom_injective ?_⟩
    rw [hhom]
  have h1 := mulAut_forall_eq_bot_of_selfCentralizing hcen hp Nat.prime_two hp2 hT le_rfl hzQ hCQ
  obtain ⟨w, hw, b, hb, hwb⟩ : ∃ w ∈ A, ∃ b ∈ A, w * b ≠ b * w := by
    by_contra hcon
    push Not at hcon
    have hAZ : A ≤ Z := fun a ha => ⟨mem_centralizer_iff.mpr fun c hc => hcon c hc a ha, hAC ha⟩
    have hle := Subgroup.card_le_of_le hAZ
    rw [hA, hZ] at hle
    have h3 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = w * b * w⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ Z := hcdef ▸ commutator_mem_of_card hA hZ hZA hZc hw hb
  have hcA : c ∈ A := hZA hcZ
  have hc1 : c ≠ 1 := fun h1 => hwb (by
    rw [hcdef, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1)
  have hwbc : w * b * w⁻¹ = b * c := by
    rw [hZc b hb c hcZ, hcdef]
    group
  have hcZeq : zpowers c = Z :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hcZ)
      (by rw [Nat.card_zpowers, orderOf_eq_prime (hApow c hcA) hc1, hZ])
  have hcx : ∀ g : G, g * c = c * g → g * x = x * g := fun g hg => by
    have hxc : x ∈ zpowers c := by
      rw [hcZeq]
      exact hxZ
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxc
    rw [← hk]
    exact (Commute.zpow_right hg k).eq
  have h2 : ∀ E : Subgroup P, IsElemAbelian 2 E → T ≤ normalizer (E : Set P) →
      E ⊓ centralizer ({⟨x, hxP⟩} : Set P) = ⊥ → E = ⊥ := by
    intro E hE hTE hEx
    by_contra hne
    have hmem : ∀ {g : G} (hg : g ∈ A), (⟨g, hAP hg⟩ : P) ∈ normalizer (E : Set P) :=
      fun hg => hTE (mem_subgroupOf.mpr hg)
    have hfix : E ⊓ centralizer ({⟨c, hAP hcA⟩} : Set P) = ⊥ := by
      rw [eq_bot_iff, ← hEx]
      refine fun e he => ⟨he.1, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩
      exact hcx e (congrArg Subtype.val (mem_centralizer_singleton_iff.mp he.2))
    have hle := CFSG.GroupTheory.PlaneAction.two_pow_le_card_of_fpf hp hp2 hE (hmem hb)
      (hmem hcA) (hmem hw) (Subtype.ext (hZc b hb c hcZ)) (Subtype.ext (hApow b hb))
      (Subtype.ext (hApow c hcA)) (Subtype.ext hwbc) (Subtype.ext (hZc w hw c hcZ)) hfix hne
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (show IsPGroup 2 E from
      fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩)
    rw [hk] at hle
    have hdvd : 2 ^ (p * orderOf (2 : ZMod p)) ∣ Nat.card E :=
      hk ▸ pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hle)
    exact hP2 (hdvd.trans (Subgroup.card_subgroup_dvd_card E))
  refine kFactNineThreeNoTwoAt_of_model hp hM hT fun V hV hN => ?_
  exact mulAut_eq_bot_of_central hcen Nat.prime_two hzT hTz h1 h2 V hV
    fun t ht => hN ⟨t, ht, rfl⟩

end Model

open CFSG.RankThree.Native CFSG.RankThree.PartOne in
theorem kFactNineThreeNoTwoAt_hs :
    KFactNineThreeNoTwoAt 5 (.sporadic .HS) := by
  obtain ⟨⟨hQP, -, -, -⟩, ⟨hlines, -⟩, -, -, -, -, -, ⟨hC, -⟩, -,
    ⟨hAC, hAn, hAP, hA, hAexp, hZ, hZA⟩, -⟩ := R3E_HS_full_five_centralizer_structures
  have hxQ : hs100FiveLine 23 ∈ hs100FiveQ := by
    have hmem : zpowers (hs100FiveLine 23) ∈
        {H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨23, rfl⟩
    exact hmem.1 (mem_zpowers _)
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  refine kFactNineThreeNoTwoAt_of_autModel Nat.prime_five (by norm_num) hs_autModel
    (hs_autModel.le (hQP hxQ)) hC hAC hAn hAP (by rw [hA]; norm_num) hAexp hZ hZA ?_
    ⟨hs100Equiv.symm.trans e⟩
  rw [CFSG.GroupTheory.PlaneAction.orderOf_two_zmod_five, card_hs100P]
  norm_num

open CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier in
theorem kFactNineThreeNoTwoAt_ru :
    KFactNineThreeNoTwoAt 5 (.sporadic .Ru) := by
  obtain ⟨⟨hQP, -, -, -⟩, ⟨hlines, -⟩, -, -, -, ⟨hC, -⟩, -,
    ⟨hAC, hAn, hAP, hA, hAexp, hZ, hZA⟩, -⟩ := R3E_Ru_full_five_centralizer_structures
  have hxQ : ruFiveLine 0 ∈ ruFiveQ := by
    have hmem : zpowers (ruFiveLine 0) ∈
        {H : Subgroup (Equiv.Perm (Fin 4060)) | H ≤ ruFiveQ ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨0, rfl⟩
    exact hmem.1 (mem_zpowers _)
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  refine kFactNineThreeNoTwoAt_of_autModel Nat.prime_five (by norm_num) ru_autModel (hQP hxQ) hC
    hAC hAn hAP (by rw [hA]; norm_num) hAexp hZ hZA ?_ ⟨ruEquivP.symm.trans e⟩
  rw [CFSG.GroupTheory.PlaneAction.orderOf_two_zmod_five, card_ruP_five]
  norm_num

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
