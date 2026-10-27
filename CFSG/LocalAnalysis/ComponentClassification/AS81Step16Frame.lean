module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Points
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalQuot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Conj

variable {A : Subgroup G}

omit [Finite G] in
theorem rightConjugate_rightConjugate_inv_eq (A : Subgroup G) (x : G) :
    rightConjugate (rightConjugate A x) x⁻¹ = A := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem rankTwoHypNF_rightConjugate (hH : RankTwoHypNF G A) (x : G) :
    RankTwoHypNF G (rightConjugate A x) where
  standard := RankTwoClassical.standardComponentIsStandard_map_equiv (MulAut.conj x⁻¹) hH.standard
  not_normal := by
    intro h
    apply hH.not_normal
    have hn : x⁻¹ ∈ normalizer ((rightConjugate A x : Subgroup G) : Set G) := by
      rw [normalizer_eq_top_iff.mpr h]
      exact mem_top _
    have heq := (rightConjugate_eq_self_iff _ _).mpr hn
    rw [rightConjugate_rightConjugate_inv_eq] at heq
    rw [heq]
    exact h
  rank := by
    obtain ⟨U, hUK, hUe, hU4⟩ := RankTwoSporadic.exists_four_le_of_two_le_pRank hH.rank
    refine CFSG.SectionRank.le_pRank one_lt_two (E := rightConjugate U x) ?_
      (AS76b.isElemAbelian_rightConjugate hUe x) (by rw [rightConjugate_card, hU4]; norm_num)
    rw [← AschbacherTheorem3.rightConjugate_centralizer]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hUK x

theorem rankTwoHyp_rightConjugate (hH : RankTwoHyp G A) (x : G) :
    RankTwoHyp G (rightConjugate A x) where
  kProper := hH.kProper
  standard := (rankTwoHypNF_rightConjugate hH.toNF x).standard
  not_normal := (rankTwoHypNF_rightConjugate hH.toNF x).not_normal
  rank := (rankTwoHypNF_rightConjugate hH.toNF x).rank

omit [Finite G] in
theorem hypII_rightConjugate (h : AS76b.HypII ↥A) (x : G) :
    AS76b.HypII ↥(rightConjugate A x) := by
  intro H _ _ B T ⟨e⟩
  exact h H B T ⟨e.trans (rightConjugateEquiv x)⟩

theorem base_rightConjugate (hB : Base G A) (hL : TypeL34 (rankTwoQuot A)) (x : G) :
    Base G (rightConjugate A x) where
  hyp := rankTwoHypNF_rightConjugate hB.hyp x
  oddCore := hB.oddCore
  hypII := hypII_rightConjugate hB.hypII x
  type := Or.inl (typeL34_rightConjugate x hL)

end Conj

theorem le_sup_rightConjugate {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) {A R : Subgroup G} (hB : Base G A)
    (hL : TypeL34 (rankTwoQuot A)) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4) {D : Subgroup G} (hD : IsElemAbelian 2 D)
    (hD64 : Nat.card D = 64) {x : G} (hxD : rightConjugate R x ≤ D) :
    D ≤ rightConjugate A x ⊔ rightConjugate R x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hB.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hKx : rightConjugate (centralizer (A : Set G)) x =
      centralizer (rightConjugate A x : Set G) := AschbacherTheorem3.rightConjugate_centralizer A x
  have hRx : IsSylowOf 2 (rightConjugate R x) (centralizer (rightConjugate A x : Set G)) :=
    hKx ▸ AschbacherTheorem3.isSylowOf_rightConjugate hR x
  have hRxe : IsElemAbelian 2 (rightConjugate R x) := AS76b.isElemAbelian_rightConjugate hRe x
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hR hKte.1
  have hRx1 : rightConjugate R x ≠ ⊥ := by
    intro h
    apply hR1
    rw [← Subgroup.card_eq_one, ← rightConjugate_card R x, h, Subgroup.card_bot]
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hRx1
  have hKxte : TightlyEmbedded (centralizer (rightConjugate A x : Set G)) :=
    hKx ▸ RankTwoSporadic.tightlyEmbedded_rightConjugate' hKte x
  have hNKx : normalizer (centralizer (rightConjugate A x : Set G) : Set G) =
      normalizer (rightConjugate A x : Set G) := by
    rw [← hKx, ← AschbacherTheorem3.rightConjugate_normalizer, hNK,
      AschbacherTheorem3.rightConjugate_normalizer]
  have hDN : D ≤ normalizer (rightConjugate A x : Set G) := by
    intro d hd
    rw [← hNKx]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKxte (hRx.le y.2)
      (fun h => hy1 (Subtype.ext h)) (hRxe.2 _ y.2) (hcomm d hd _ (hxD y.2))
  have hAxperf : commutator ↥(rightConjugate A x) = ⊤ :=
    (isQuasisimple_rightConjugate x hstd.1).1
  obtain ⟨e₀⟩ := PSL3Four.nonempty_equiv_of_stated (↥A ⧸ center ↥A) hL
  have hle := le_sup_centralizer_of_sixteen_le hE16 hAxperf
    ((rightConjugateQuotEquiv x).trans e₀) hRx hDN hD
    (by rw [rightConjugate_card, hR4, hD64])
  exact le_sup_of_le_sup_normalizer hRx (isPGroup_two_of_isElemAbelian hD)
    (fun d hd => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      hcomm r (hxD hr) d hd)) hle

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem rightConjugate_eq_of_mem_normalizer (hF : Frame G A A R g E F) {x : G}
    (hxE : rightConjugate R x ≤ E) (hx : x ∈ normalizer (A : Set G)) :
    rightConjugate R x = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hNK := AS76b.normalizer_centralizer_eq hstd
  set K := centralizer (A : Set G)
  have hxK : x ∈ normalizer (K : Set G) := hNK ▸ hx
  have hKx : rightConjugate K x = K := (rightConjugate_eq_self_iff K x).mpr hxK
  have hRx : IsSylowOf 2 (rightConjugate R x) K :=
    hKx ▸ AschbacherTheorem3.isSylowOf_rightConjugate hF.sylowR x
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hN : rightConjugate R x ≤ normalizer (R : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
      hcomm z (hF.R_le_E hz) y (hxE hy))
  have h2 := hF.sylowR.isPGroup.to_sup_of_normal_left' hRx.isPGroup hN
  have h1 := hF.sylowR.eq_of_le le_sup_left (sup_le hF.sylowR.le hRx.le) h2
  have h3 := hRx.eq_of_le le_sup_right (sup_le hF.sylowR.le hRx.le) h2
  rw [← h3, h1]

theorem card_inf_of_frame (hF : Frame G A A R g E F) : Nat.card ↥(E ⊓ F) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := hNK ▸ hF.not_mem
  have hRRg : R ⊓ rightConjugate R g = ⊥ := by
    have h := two_subgroup_inf_conjugate_eq_bot _ (R ⊓ rightConjugate R g) hKte
      (hF.sylowR.isPGroup.to_le inf_le_left) g hgK
      (inf_le_right.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate hF.sylowR.le g))
    rwa [inf_eq_left.mpr (inf_le_left.trans hF.sylowR.le)] at h
  have hN : rightConjugate R g ≤ normalizer (R : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (hF.comm hy)
  have h := card_sup_mul_card_inf hN
  rw [hRRg, Subgroup.card_bot, mul_one, rightConjugate_card, hF.cardR] at h
  rw [hF.inf_eq, h]

theorem frame_at_point {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) {x : G} (hxV : rightConjugate R x ≤ E ⊓ F)
    (hne : rightConjugate R x ≠ R) :
    Frame G (rightConjugate A x) (rightConjugate A x) (rightConjugate R x) x⁻¹ E F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hxE : rightConjugate R x ≤ E := hxV.trans inf_le_left
  have hxF : rightConjugate R x ≤ F := hxV.trans inf_le_right
  have hxA : x ∉ normalizer (A : Set G) := fun hx =>
    hne (rightConjugate_eq_of_mem_normalizer hF hxE hx)
  have hKx : rightConjugate (centralizer (A : Set G)) x =
      centralizer (rightConjugate A x : Set G) := AschbacherTheorem3.rightConjugate_centralizer A x
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEle := le_sup_rightConjugate hE16 hF.base hL hF.sylowR hF.elemR hF.cardR hF.elemE
    hF.cardE hxE
  have hFle := le_sup_rightConjugate hE16 hF.base hL hF.sylowR hF.elemR hF.cardR hF.elemF
    hF.cardF hxF
  have hRR := rightConjugate_rightConjugate_inv_eq R x
  have hRV : R ≤ E ⊓ F := le_inf hF.R_le_E hF.R_le_F
  have hRRx : R ⊓ rightConjugate R x = ⊥ :=
    inf_eq_bot_of_mem_pointsIn hKte hF.sylowR hcommE (self_mem_pointsIn hF.R_le_E)
      ⟨hxE, x, rfl⟩ hne.symm
  have hNx : R ≤ normalizer (rightConjugate R x : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
      hcommE z (hxE hz) y (hF.R_le_E hy))
  have hcardQR : Nat.card ↥(rightConjugate R x ⊔ R) = 16 := by
    have h := card_sup_mul_card_inf hNx
    rw [inf_comm, hRRx, Subgroup.card_bot, mul_one, rightConjugate_card, hF.cardR] at h
    exact h
  have hinf : E ⊓ F = rightConjugate R x ⊔ R := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hxV hRV) ?_).symm
    rw [card_inf_of_frame hF, hcardQR]
  refine
    { base := base_rightConjugate hF.base hL x
      le := le_rfl
      quasisimple := isQuasisimple_rightConjugate x hF.quasisimple
      typeA₁ := typeL34_rightConjugate x hL
      sylowR := hKx ▸ AschbacherTheorem3.isSylowOf_rightConjugate hF.sylowR x
      elemR := AS76b.isElemAbelian_rightConjugate hF.elemR x
      cardR := by rw [rightConjugate_card, hF.cardR]
      not_mem := ?_
      comm := ?_
      conj_le := by rw [hRR]; exact hF.R_le_E.trans hEle
      E_le := hEle
      F_le := hFle
      R_le_E := hxE
      R_le_F := hxF
      elemE := hF.elemE
      elemF := hF.elemF
      cardE := hF.cardE
      cardF := hF.cardF
      ne := hF.ne
      inf_eq := by rw [hRR]; exact hinf
      inf_eq_center := hF.inf_eq_center
      sylow := ?_ }
  ·
    intro h
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff] at h
    apply hxA
    simpa using inv_mem h
  ·
    rw [hRR]
    exact fun y hy => mem_centralizer_iff.mpr fun z hz => hcommE z (hxE hz) y (hF.R_le_E hy)
  ·
    have hcard := hF.sylow.card_eq
    refine isSylowOf_of_card (sup_le hEle hFle) ?_
    have hsup : rightConjugate A x ⊔ rightConjugate R x = rightConjugate (A ⊔ R) x :=
      (Subgroup.map_sup A R (MulAut.conj x⁻¹).toMonoidHom).symm
    have hc : Nat.card ↥(rightConjugate A x ⊔ rightConjugate R x) = Nat.card ↥(A ⊔ R) := by
      rw [hsup, rightConjugate_card]
    rw [hc]
    exact hcard

end Frame

end CFSG.ComponentClassification.AS81
