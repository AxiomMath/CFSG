module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQNineSeventeen
public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6NineSeventeen

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111 CFSG.AGLEmbeddingD2 CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem card_le_sq_of_le_sup_cyclic [hp : Fact p.Prime] {Y E F : Subgroup G} (hYc : IsCyclic Y)
    (hEN : E ≤ Subgroup.normalizer (Y : Set G)) (hE : Nat.card E = p ^ 2) (hEY : E ⊓ Y ≠ ⊥)
    (hF : IsElemAbelian p F) (hFA : F ≤ Y ⊔ E) : Nat.card F ≤ p ^ 2 := by
  have hFY : Nat.card (Y ⊓ F : Subgroup G) ≤ p := by
    have hle : (Y ⊓ F : Subgroup G) ≤ Y := inf_le_left
    haveI : IsCyclic (Y ⊓ F : Subgroup G) := Subgroup.isCyclic_of_le hle
    have hexp : Monoid.exponent (Y ⊓ F : Subgroup G) ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hF.2 g ((inf_le_right : Y ⊓ F ≤ F) g.2))
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.out.pos hexp
  set A := Y ⊔ E
  have hYA : Y ≤ A := le_sup_left
  have hEA : E ≤ A := le_sup_right
  set Y' := Y.subgroupOf A
  set E' := E.subgroupOf A
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hEN
  haveI hY'n : Y'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYA).mpr hAN
  have htop : E' ⊔ Y' = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEA,
      Subgroup.map_subgroupOf_eq_of_le hYA, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      sup_comm]
  have hidxA : Y.relIndex A = Y.relIndex E := by
    show Y'.index = _
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right,
      Subgroup.relIndex_subgroupOf hEA]
  have hEYc : p ≤ Nat.card (Y ⊓ E : Subgroup G) := by
    have hdvd : Nat.card (Y ⊓ E : Subgroup G) ∣ p ^ 2 := by
      rw [← hE]; exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    have hne : (Y ⊓ E : Subgroup G) ≠ ⊥ := by rwa [inf_comm]
    rcases k with _ | k
    · exact absurd ((Subgroup.card_eq_one).mp (by simpa using hkc)) hne
    · rw [hkc]
      exact (pow_one p).symm.le.trans (Nat.pow_le_pow_right hp.out.pos (by omega))
  have hrE : Y.relIndex E ≤ p := by
    have h := Subgroup.relIndex_mul_card (H := Y) (K := E)
    rw [hE] at h
    by_contra hlt
    push Not at hlt
    have : p * p < Y.relIndex E * Nat.card (Y ⊓ E : Subgroup G) :=
      Nat.mul_lt_mul_of_lt_of_le hlt hEYc Nat.card_pos
    rw [h] at this
    nlinarith
  haveI : Y.IsFiniteRelIndex A := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrF : Y.relIndex F ≤ p :=
    (Subgroup.relIndex_le_of_le_right hFA (Subgroup.relIndex_ne_zero)).trans (hidxA ▸ hrE)
  have h := Subgroup.relIndex_mul_card (H := Y) (K := F)
  rw [← h, sq]
  exact Nat.mul_le_mul hrF hFY

variable {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} {z : H}
  {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {E : Subgroup G}

theorem InnerNotQConfig.pRank_baseA_le_two (hOut : KFactOutCyclic)
    (hC : InnerNotQConfig p P M H R Rbar z L E) :
    Open.pRank p (innerNotQBaseA p H R L E) ≤ 2 := by
  have hp := hC.cfg.ext.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hLn : L.Normal := (hC.nineThree hOut).normal
  have he := hC.cfg.ext.toD1Escape
  have hRH : R ≤ H := he.le_H
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  unfold innerNotQBaseA
  rw [hC.innerNotQJ_eq hOut]
  set Y := d1LiftX p H R L with hYdef
  have hYH : Y ≤ H := d1LiftX_le_H p H R L
  have hYp : IsPGroup p Y := hC.cfg.ext.isPGroup.to_le (d1LiftX_le p H R L)
  have hYc : IsCyclic Y := by
    have hSp : IsPGroup p (Y.subgroupOf H) := hYp.comap_subtype
    have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp
      (primeComplementCore (G := H) p)
      (hp.coprime_iff_not_dvd.mp (primeComplementCore_coprime p)) _ hSp
    let e := MulEquiv.ofBijective _ ⟨hinj, π.subgroupMap_surjective (Y.subgroupOf H)⟩
    have himg : (Y.subgroupOf H).map π ≤
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L := by
      rw [map_d1LiftX, hC.cfg.rbar]
    haveI := hC.cyclic L hC.isComponent
    haveI : IsCyclic ((Y.subgroupOf H).map π) := Subgroup.isCyclic_of_le himg
    haveI : IsCyclic (Y.subgroupOf H) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hYH).toMonoidHom
      (MulEquiv.surjective _)
  have hconj : ∀ g ∈ R, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    rintro g hg _ ⟨x, ⟨hxR, hxL⟩, rfl⟩
    refine ⟨⟨g, hRH hg⟩ * x * ⟨g, hRH hg⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
    · exact (R.subgroupOf H).mul_mem ((R.subgroupOf H).mul_mem
        (Subgroup.mem_subgroupOf.mpr hg) hxR) ((R.subgroupOf H).inv_mem
        (Subgroup.mem_subgroupOf.mpr hg))
    · show π (⟨g, hRH hg⟩ * x * ⟨g, hRH hg⟩⁻¹) ∈ L
      rw [map_mul, map_mul, map_inv]
      exact hLn.conj_mem _ hxL _
  have hRN : R ≤ Subgroup.normalizer (Y : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj g hg y, fun hy => ?_⟩
    have := hconj g⁻¹ (R.inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hEN : E ≤ Subgroup.normalizer (Y : Set G) := hC.fieldOmega.1.trans hRN
  have hEY : E ⊓ Y ≠ ⊥ := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hC.fieldOmega.2.2.2.1
    obtain ⟨⟨x, hx, hxw⟩, hwL⟩ := hw
    have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    have hxL : π x ∈ L := by rw [hxw]; exact hwL
    refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨x, hxE,
      ⟨x, ⟨Subgroup.mem_subgroupOf.mpr (hC.fieldOmega.1 hxE), hxL⟩, rfl⟩⟩, fun h1 => hw1 ?_⟩
    have hx1 : x = 1 := Subtype.ext (by simpa using congrArg Subtype.val h1)
    apply Subtype.ext
    show w = 1
    rw [← hxw, hx1, map_one]
  by_contra hlt
  push Not at hlt
  obtain ⟨F, hFA, hF, hFc⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp (H := Y ⊔ E) (k := 3) (by omega)
  have := card_le_sq_of_le_sup_cyclic hYc hEN hC.fieldOmega.2.2.1 hEY hF hFA
  rw [hFc] at this
  have := Nat.pow_lt_pow_right hp.one_lt (show 2 < 3 by norm_num)
  omega

variable (G) in
@[expose] def InnerNotQRankTwoNineThree : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) (z : H)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G),
    InnerNotQConfig p P M H R Rbar z L E →
    ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → innerNotQBaseA p H R L E ≤ N →
      AGLCovers p H N (innerNotQJ p H L) → innerNotQBaseA p H R L E ≤ T → T ≤ N → T ≤ M →
      IsPGroup p T → (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) →
      Open.pRank p T ≤ 2 →
      (primeComplementCore (G := N) p).map N.subtype ≤ M ∧
      ∃ JN : Subgroup (N ⧸ primeComplementCore (G := N) p), Hyp111NineThree p M N JN ∧
        Nat.card JN ≤ Nat.card (innerNotQJ p H L) ∧ Group.IsSolvable (Outer JN)

theorem innerNotQRankTwoA_of_nineThree (hk : D1CaseTwoKFacts3 G)
    (h : InnerNotQRankTwoNineThree G) : InnerNotQRankTwoA G := by
  intro p P M H R Rbar z L E hC _ _
  haveI : Fact p.Prime := ⟨hC.cfg.ext.prime⟩
  obtain ⟨hKs, hKnab, hKp, -, -⟩ := hC.component_facts hk
  have hB2 := hC.pRank_baseA_le_two hk.out
  have hat := h p P M H R Rbar z L E hC
  rw [hC.innerNotQJ_eq hk.out] at hat ⊢
  refine aglRankTwoFactorAt_of_nineThree hKs hKnab hKp hC.not_le ?_
  intro N T hN hNM hBN hcov hBT hTN hTM hT hmax hor
  refine hat N T hN hNM hBN hcov hBT hTN hTM hT hmax ?_
  rcases hor with rfl | h2
  · exact hB2
  · exact h2

theorem d1CaseTwoCentral3InnerNotQK_of_nineThree (hk : D1CaseTwoKFacts3 G)
    (h3 : D1CaseThreeNotKlingen3 G) (hother : D1CaseThreeKlingenOther3 G)
    (hkl : KFactKlingenLocal) (hmod : StmtKlingenModel) (h : InnerNotQRankTwoNineThree G)
    (hBlock : InnerNotQBlockA G) (hBig : InnerNotQIndexBigK G) :
    D1CaseTwoCentral3InnerNotQK G :=
  d1CaseTwoCentral3InnerNotQK_of_baseA hk h3 hother hkl hmod
    (innerNotQRankTwoA_of_nineThree hk h) hBlock hBig

theorem InnerNotQConfig.false_of_blockR (hk : D1CaseTwoKFacts3 G)
    (h3 : D1CaseThreeNotKlingen3 G) (hother : D1CaseThreeKlingenOther3 G)
    (hkl : KFactKlingenLocal) (hmod : StmtKlingenModel)
    (hC : InnerNotQConfig p P M H R Rbar z L E) (hih : D1KappaIH p M H)
    (hblock : ∃ Lm : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) Lm ∧ (Lm.subgroupOf M).Normal ∧
      ∀ r ∈ R, ∀ l ∈ Lm, r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 M) : False := by
  have hext : D1Extremal p P M H R := hC.cfg.ext
  have he : D1Escape p P M H R := hext.toD1Escape
  have hglob : AGLGlobal G := hC.cfg.glob.toU.toAGLGlobal
  have hb3 : Hyp111B3 p H R (innerNotQJ p H L) :=
    (hC.b3 hk.out hk.seitzCyc hk.noTwo).mono hC.fieldOmega.1
  have h93 : Hyp111NineThree p M H (innerNotQJ p H L) :=
    innerNotQNineThree_of_out hk.out p P M H R Rbar z L E hC
  have htc : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := twoCore_inf_eq h93 hb3 he.le_H he.le_M he.twoCore_le
  have hOM : (primeComplementCore (G := H) p).map H.subtype ≤ M := by
    rw [map_primeComplementCore_eq]
    exact he.primeCore_le
  have hfac : AGLCompetitorFactorAt p M H (innerNotQJ p H L) R :=
    factorAt_of_kMax (d1KMaxR_of_ih hext (fun N R' hN hlt => hih P M N R' hN hlt) le_rfl)
      (hyp917R_of_ext_self hext (hC.hyp917Ext hk h3 hother hkl hmod R))
  obtain ⟨Lm, hLm, hLmn, hcomm⟩ := hblock
  exact false_of_centralizing_base_of_factorAtB ⟨he, hglob, htc⟩ hk.localCGT (hk.noXBlock G hglob)
    (fun h => hC.not_le ((le_innerNotQJ p H L).trans h)) hOM h93.factor hfac h93.plusCore_le hLm
    hLmn hext.isPGroup he.le_H he.le_M hb3 hcomm

variable (G) in
@[expose] def InnerNotQBlockRBig : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) (z : H)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G),
    InnerNotQConfig p P M H R Rbar z L E → D1KappaIH p M H →
    Nat.card R ≠ p * Nat.card (innerNotQBaseA p H R L E) →
    ∃ Lm : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) Lm ∧ (Lm.subgroupOf M).Normal ∧
      ∀ r ∈ R, ∀ l ∈ Lm, r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 M

theorem innerNotQIndexBigK_of_blockR (hk : D1CaseTwoKFacts3 G)
    (h3 : D1CaseThreeNotKlingen3 G) (hother : D1CaseThreeKlingenOther3 G)
    (hkl : KFactKlingenLocal) (hmod : StmtKlingenModel) (h : InnerNotQBlockRBig G) :
    InnerNotQIndexBigK G :=
  fun p P M H R Rbar z L E hC hih hidx =>
    hC.false_of_blockR hk h3 hother hkl hmod hih (h p P M H R Rbar z L E hC hih hidx)

theorem d1CaseTwoCentral3InnerNotQK_of_blocks (hk : D1CaseTwoKFacts3 G)
    (h3 : D1CaseThreeNotKlingen3 G) (hother : D1CaseThreeKlingenOther3 G)
    (hkl : KFactKlingenLocal) (hmod : StmtKlingenModel) (h : InnerNotQRankTwoNineThree G)
    (hBlock : InnerNotQBlockA G) (hR : InnerNotQBlockRBig G) :
    D1CaseTwoCentral3InnerNotQK G :=
  d1CaseTwoCentral3InnerNotQK_of_nineThree hk h3 hother hkl hmod h hBlock
    (innerNotQIndexBigK_of_blockR hk h3 hother hkl hmod hR)

end CFSG.LocalAnalysis.RankThreeTheoremC
