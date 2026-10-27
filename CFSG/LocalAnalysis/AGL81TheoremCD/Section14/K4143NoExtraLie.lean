module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K4143Reduce
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2Reduction
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K1410aOut
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Lin
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6aHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Small
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTen

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.Blueprint (LieModel)

private def quotientCenterMulEquiv {X : Type} [Group X] (L : Subgroup X)
    (hZ : Subgroup.center ↥L = ⊥) : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq (G := ↥L) hZ).trans
    (QuotientGroup.quotientBot (G := ↥L))

theorem pElementSubgroup_le_of_k2 {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (hZ : Subgroup.center ↥L = ⊥) (h3L : CFSG.Open.pRank 3 L = 3)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (H : ∀ R : Subgroup (MulAut ↥L), IsPGroup 3 R →
      CFSG.ABGLocalTools.IsSylowOf 3
        (R ⊓ (MulAut.conj : ↥L →* MulAut ↥L).range)
        (MulAut.conj : ↥L →* MulAut ↥L).range →
      ¬ R ≤ (MulAut.conj : ↥L →* MulAut ↥L).range → 4 ≤ CFSG.Open.pRank 3 R) :
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup 3
      (⊤ : Subgroup X) ≤ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (Subgroup.closure_le L).2 ?_
  rintro x ⟨-, k, hk⟩
  have hxk : x ^ 3 ^ k = 1 := hk ▸ pow_orderOf_eq_one x
  by_contra hxL
  obtain ⟨P, hxP⟩ : ∃ P : Sylow 3 X, x ∈ (P : Subgroup X) := by
    have hp : IsPGroup 3 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, hP (Subgroup.mem_zpowers x)⟩
  set c : X →* MulAut ↥L := MulAut.conjNormal (H := L)
  have hinj : ∀ z ∈ (P : Subgroup X), c z = 1 → z = 1 := by
    intro z hz hz1
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨z, hz⟩
    have hzj : z ^ 3 ^ j = 1 := congrArg Subtype.val hj
    exact eq_one_of_mem_centralizer_of_pow_three_pow hZ h3L.ge h3X.le
      ((conjNormal_eq_one_iff_mem_centralizer L).1 hz1) hzj
  have hnle : ¬ (P : Subgroup X).map c ≤ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    intro hle
    obtain ⟨l, hl⟩ := hle ⟨x, hxP, rfl⟩
    have hcen := inv_mul_mem_centralizer_of_conj_eq hl
    have hxeq : x = (l : X) * ((l : X)⁻¹ * x) := by group
    refine hxL (mem_of_mem_sup_centralizer hZ h3L.ge h3X.le ?_ hxk)
    rw [hxeq]
    exact Subgroup.mul_mem_sup l.2 hcen
  have h4 := H ((P : Subgroup X).map c) ((P.isPGroup').map c)
    (isSylowOf_inf_inner L P) hnle
  rw [pRank_map_of_injOn (by norm_num) c (P : Subgroup X) hinj] at h4
  have h5 : CFSG.Open.pRank 3 (P : Subgroup X) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono (by norm_num) le_top
  omega

theorem le_of_isLie811 {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
    (hZ : Subgroup.center ↥L = ⊥) (h3L : CFSG.Open.pRank 3 L = 3)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) {fam : LieFam811} {r f : ℕ}
    (hLie : IsLie811 ↥L fam r f) {R : Subgroup X} (hexp : ∀ x ∈ R, x ^ 3 = 1) : R ≤ L := by
  have h3Ltop : CFSG.pRank 3 (⊤ : Subgroup ↥L) = 3 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank (p := 3) (H := (⊤ : Subgroup ↥L))]
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact h3L
  have hple := pElementSubgroup_le_of_k2 L hZ h3L h3X
    (fun R hR hSyl hnle => by
      have h := k2Lie_holds ↥L fam r f hLie h3Ltop R hR hSyl hnle
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h)
  intro x hx
  refine hple (Subgroup.subset_closure ⟨Subgroup.mem_top x, ?_⟩)
  have hdvd : orderOf x ∣ 3 ^ 1 := by
    simpa using orderOf_dvd_of_pow_eq_one (hexp x hx)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  exact ⟨k, hk⟩

private theorem uniqueElemSylow_coe_of_isLie811 {L : Type} [Group L] [Finite L]
    {fam : LieFam811} {r f : ℕ} (h : IsLie811 L fam r f)
    (hZ : Subgroup.center L = ⊥) : CFSG.GroupTheory.UniqueElemSylow 3 3 L := by
  have hX : CFSG.GroupTheory.UniqueElemSylow 3 3 (L ⧸ Subgroup.center L) := by
    by_cases hfam : fam = .l4
    · subst hfam
      exact uniqueElemSylow_of_lieModel_l4 h.2.2
    · exact uniqueElemSylow_of_isLieFam811 h.2.2 hfam
  exact CFSG.GroupTheory.UniqueElemSylow.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq (G := L) hZ).trans
      (QuotientGroup.quotientBot (G := L))) hX

theorem not_isThreeOnePlusFour_of_isLie811 {X : Type} [Group X] [Finite X]
    {L : Subgroup X} [L.Normal] (hZ : Subgroup.center ↥L = ⊥)
    (h3L : CFSG.Open.pRank 3 L = 3) (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    {fam : LieFam811} {r f : ℕ} (hLie : IsLie811 ↥L fam r f) (R : Subgroup X) :
    ¬ CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R := by
  rintro ⟨hcard, hexp, hZR, hcomm⟩
  have hexpR : ∀ x ∈ R, x ^ 3 = 1 := by
    intro x hx
    simpa using congrArg Subtype.val (hexp ⟨x, hx⟩)
  have hRle : R ≤ L := le_of_isLie811 hZ h3L h3X hLie hexpR
  have hU : CFSG.GroupTheory.UniqueElemSylow 3 3 ↥L :=
    uniqueElemSylow_coe_of_isLie811 hLie hZ
  have hR' : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥(R.subgroupOf L) :=
    isThreeOnePlusFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRle).symm
      ⟨hcard, hexp, hZR, hcomm⟩
  obtain ⟨hcard', hexp', hZ', hcomm'⟩ := hR'
  exact CFSG.GroupTheory.ExtraspecialThreeFive.false_of_uniqueElemSylow hU
    hcard' hexp' hZ' hcomm'

theorem not_isThreeOnePlusFour_of_psp43 {X : Type} [Group X] [Finite X]
    {L : Subgroup X} [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZ : Subgroup.center ↥L = ⊥) (h3L : CFSG.Open.pRank 3 L = 3)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hm : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 3 1)
    (R : Subgroup X) : ¬ CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R := by
  rintro ⟨hcard, hexp, -, -⟩
  have hexpR : ∀ x ∈ R, x ^ 3 = 1 := by
    intro x hx
    simpa using congrArg Subtype.val (hexp ⟨x, hx⟩)
  have h3L' : 3 ≤ CFSG.Open.pRank 3 L := h3L.ge
  have h3X' : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 := h3X.le
  set c : X →* MulAut ↥L := MulAut.conjNormal (H := L)
  have hinj : ∀ x ∈ R, c x = 1 → x = 1 := by
    intro x hx hx1
    exact eq_one_of_mem_centralizer_of_pow_three_pow hZ h3L' h3X'
      ((conjNormal_eq_one_iff_mem_centralizer L).1 hx1) (k := 1)
      (by simpa using hexpR x hx)
  have hR3 : IsPGroup 3 R := IsPGroup.of_card (p := 3) (n := 5) hcard
  have hmap3 : IsPGroup 3 (R.map c) := hR3.map c
  haveI : Group.IsPerfect ↥L := (Group.isPerfect_def).2 hq.1
  have hInner : R.map c ≤ innAut ↥L :=
    le_innAut_of_card_outer_le_two (card_outer_le_two_of_psp43 hm) hmap3
  have hsup : ∀ x ∈ R, x ∈ L ⊔ Subgroup.centralizer (L : Set X) → x ∈ L := by
    intro x hx hxsup
    exact mem_of_mem_sup_centralizer hZ h3L' h3X' hxsup (k := 1)
      (by simpa using hexpR x hx)
  have hRle : R ≤ L := le_of_map_conjNormal_le_innAut hInner hsup
  have hdvd : 3 ^ 5 ∣ Nat.card ↥L := by
    have h := Subgroup.card_dvd_of_le hRle
    rwa [show Nat.card ↥R = 3 ^ 5 from hcard] at h
  have hcardL : Nat.card ↥L = 25920 := by
    obtain ⟨eP⟩ := psp43_equiv_of_lieModel hm
    calc Nat.card ↥L = Nat.card (↥L ⧸ Subgroup.center ↥L) :=
          (Nat.card_congr (quotientCenterMulEquiv L hZ).toEquiv).symm
      _ = Nat.card CFSG.GH74.Exceptional.PSp43 := Nat.card_congr eP.toEquiv
      _ = 25920 := card_PSp43
  rw [hcardL] at hdvd
  exact (by norm_num : ¬ 3 ^ 5 ∣ 25920) hdvd

private theorem openPRank_top_centerQuotient {X : Type} [Group X] [Finite X]
    (L : Subgroup X) (hZ : Subgroup.center ↥L = ⊥)
    (h3L : CFSG.Open.pRank 3 L = 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) = 3 := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
    (quotientCenterMulEquiv L hZ)]
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact h3L

private theorem classicalTags_and_characteristic_of_isClassicalOrG2Index
    {d : TauCeti.LieTypeIndex} (hd : CFSG.AGLEmbedding.IsClassicalOrG2Index d)
    (hG2 : ∀ q, d ≠ .G2 q) :
    d.characteristic ≠ 3 ∧
      ((∃ r q, d = .A r q) ∨ (∃ r q, d = .twistedA r q) ∨
        (∃ r q, d = .B r q) ∨ (∃ r q, d = .C r q) ∨
        (∃ r q, d = .D r q) ∨ (∃ r q, d = .twistedD r q)) := by
  cases d with
  | A r q =>
    have hq2 : q.p = 2 := by
      simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index] using hd
    have hch : (TauCeti.LieTypeIndex.A r q).characteristic ≠ 3 := by
      rw [TauCeti.LieTypeIndex.characteristic_A, hq2]
      norm_num
    exact ⟨hch, Or.inl ⟨r, q, rfl⟩⟩
  | twistedA r q =>
    have hq2 : q.p = 2 := by
      simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index] using hd
    have hch : (TauCeti.LieTypeIndex.twistedA r q).characteristic ≠ 3 := by
      rw [TauCeti.LieTypeIndex.characteristic_twistedA, hq2]
      norm_num
    exact ⟨hch, Or.inr (Or.inl ⟨r, q, rfl⟩)⟩
  | B r q =>
    have hq2 : q.p = 2 := by
      simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index] using hd
    have hch : (TauCeti.LieTypeIndex.B r q).characteristic ≠ 3 := by
      rw [TauCeti.LieTypeIndex.characteristic_B, hq2]
      norm_num
    exact ⟨hch, Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩))⟩
  | C r q => exact hd.elim
  | D r q =>
    have hq2 : q.p = 2 := by
      simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index] using hd
    have hch : (TauCeti.LieTypeIndex.D r q).characteristic ≠ 3 := by
      rw [TauCeti.LieTypeIndex.characteristic_D, hq2]
      norm_num
    exact ⟨hch, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩))))⟩
  | twistedD r q =>
    have hq2 : q.p = 2 := by
      simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index] using hd
    have hch : (TauCeti.LieTypeIndex.twistedD r q).characteristic ≠ 3 := by
      rw [TauCeti.LieTypeIndex.characteristic_twistedD, hq2]
      norm_num
    exact ⟨hch, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, q, rfl⟩))))⟩
  | G2 q => exact (hG2 q rfl).elim
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki k => exact hd.elim
  | reeG2 k => exact hd.elim
  | reeF4 k => exact hd.elim
  | tits => exact hd.elim

theorem not_isThreeOnePlusFour_of_classical {X : Type} [Group X] [Finite X]
    (L : Subgroup X) [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZ : Subgroup.center ↥L = ⊥) (h3L : CFSG.Open.pRank 3 L = 3)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (d : TauCeti.ValidLieTypeIndex) (hd : CFSG.AGLEmbedding.IsClassicalOrG2Index d.1)
    (hG2 : ∀ q, d.1 ≠ .G2 q)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (R : Subgroup X) : ¬ CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R := by
  obtain ⟨hch, hcl⟩ :=
    classicalTags_and_characteristic_of_isClassicalOrG2Index hd hG2
  have h3Q : CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) = 3 :=
    openPRank_top_centerQuotient L hZ h3L
  rcases k34odd_lie_classical_crossChar (↥L ⧸ Subgroup.center ↥L) d e h3Q hch hcl with
    hm | hclause
  · exact not_isThreeOnePlusFour_of_psp43 hq hZ h3L h3X hm R
  · have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
      rw [hZ, Subgroup.card_bot]
      exact odd_one
    have hqn : CFSG.IsQuasisimple ↥L :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥L).1 hq
    obtain ⟨fam, r, f, hLie⟩ := exists_isLie811_of_clause4 hqn hZodd hclause
    exact not_isThreeOnePlusFour_of_isLie811 hZ h3L h3X hLie R

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
