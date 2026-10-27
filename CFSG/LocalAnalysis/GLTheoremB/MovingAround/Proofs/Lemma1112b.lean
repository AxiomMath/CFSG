module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1112

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn card_of_isLThreeFour)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut)

namespace Lemma1112b

section Generic

variable {G : Type} [Group G]

theorem card_sylow_eq {p : ℕ} [Fact p.Prime] [Finite G] (P Q : Sylow p G) :
    Nat.card P = Nat.card Q := by
  rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]

theorem card_le_of_isSylowIn {p : ℕ} [hp : Fact p.Prime] [Finite G] {X Q : Subgroup G}
    (hQ : IsSylowIn p X Q) {R : Subgroup G} (hRX : R ≤ X) (hR : IsPGroup p R) :
    Nat.card R ≤ Nat.card Q := by
  have hRX' : IsPGroup p ↥(R.subgroupOf X) :=
    hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm
  have hQX' : IsPGroup p ↥(Q.subgroupOf X) :=
    hQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm
  obtain ⟨S₁, hS₁⟩ := IsPGroup.exists_le_sylow hRX'
  obtain ⟨S₂, hS₂⟩ := IsPGroup.exists_le_sylow hQX'
  set T₁ : Subgroup G := (S₁ : Subgroup X).map X.subtype with hT₁
  set T₂ : Subgroup G := (S₂ : Subgroup X).map X.subtype with hT₂
  have hcard : ∀ S : Sylow p X, Nat.card ((S : Subgroup X).map X.subtype) = Nat.card S := by
    intro S
    exact Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup X) X.subtype
      X.subtype_injective).symm
  have hT₁p : IsPGroup p T₁ := by
    have : IsPGroup p ↥((S₁ : Subgroup X).map X.subtype) :=
      S₁.isPGroup'.of_equiv (Subgroup.equivMapOfInjective (S₁ : Subgroup X) X.subtype
        X.subtype_injective)
    exact this
  have hT₂p : IsPGroup p T₂ := by
    have : IsPGroup p ↥((S₂ : Subgroup X).map X.subtype) :=
      S₂.isPGroup'.of_equiv (Subgroup.equivMapOfInjective (S₂ : Subgroup X) X.subtype
        X.subtype_injective)
    exact this
  have hT₁X : T₁ ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hT₂X : T₂ ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hQT₂ : Q ≤ T₂ := by
    intro q hq
    have hqX : (⟨q, hQ.1 hq⟩ : X) ∈ (Q.subgroupOf X) := by
      simpa [Subgroup.mem_subgroupOf] using hq
    have hmem := hS₂ hqX
    exact ⟨⟨q, hQ.1 hq⟩, hmem, rfl⟩
  have hQeq : T₂ = Q := hQ.2.2 T₂ hT₂X hT₂p hQT₂
  have hRT₁ : R ≤ T₁ := by
    intro r hr
    have hrX : (⟨r, hRX hr⟩ : X) ∈ (R.subgroupOf X) := by
      simpa [Subgroup.mem_subgroupOf] using hr
    have hmem := hS₁ hrX
    exact ⟨⟨r, hRX hr⟩, hmem, rfl⟩
  have h1 : Nat.card R ≤ Nat.card T₁ := Subgroup.card_le_of_le hRT₁
  have h2 : Nat.card T₁ = Nat.card T₂ := by
    rw [hT₁, hT₂, hcard, hcard]
    exact card_sylow_eq S₁ S₂
  rw [← hQeq]
  exact h1.trans h2.le

theorem le_pRank_of_card {p : ℕ} [Fact p.Prime] [Finite G] {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card H, ?_⟩
    rintro j ⟨F, hFH, -, hFj⟩
    have h1 : p ^ j ≤ Nat.card H := by
      rw [← hFj]
      exact Subgroup.card_le_of_le hFH
    exact le_trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le h1
  · exact ⟨E, hEH, hE, hk⟩

theorem exists_elemAb_card_pRank {p : ℕ} [Fact p.Prime] [Finite G] (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ CFSG.Open.pRank p H := by
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card H, ?_⟩
    rintro j ⟨F, hFH, -, hFj⟩
    have h1 : p ^ j ≤ Nat.card H := by
      rw [← hFj]
      exact Subgroup.card_le_of_le hFH
    exact le_trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le h1
  have hne : {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ k}.Nonempty := by
    refine ⟨0, ⊥, bot_le, ?_, by simp⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (by
        have ha := a.2
        have hb := b.2
        rw [Subgroup.mem_bot] at ha hb
        simp [ha, hb])
    · rw [Subgroup.mem_bot] at hx
      simp [hx]
  have hmem := Nat.sSup_mem hne hbdd
  unfold CFSG.Open.pRank
  obtain ⟨E, hEH, hE, hEc⟩ := hmem
  exact ⟨E, hEH, hE, hEc⟩


theorem mem_glbConj {g : G} {H : Subgroup G} {x : G} :
    x ∈ GLBConj g H ↔ ∃ y ∈ H, g⁻¹ * y * g = x := by
  unfold GLBConj
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩

theorem glbConj_glbConj (x y : G) (H : Subgroup G) :
    GLBConj x (GLBConj y H) = GLBConj (y * x) H := by
  ext z
  simp only [mem_glbConj]
  constructor
  · rintro ⟨w, ⟨u, hu, hw⟩, hz⟩
    subst hw
    subst hz
    exact ⟨u, hu, by group⟩
  · rintro ⟨u, hu, hz⟩
    exact ⟨y⁻¹ * u * y, ⟨u, hu, rfl⟩, by rw [← hz]; group⟩

theorem card_glbConj (g : G) (E : Subgroup G) : Nat.card (GLBConj g E) = Nat.card E := by
  unfold GLBConj
  exact Nat.card_congr (Subgroup.equivMapOfInjective E (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).symm.toEquiv

theorem isElemAbelian_glbConj {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) (g : G) :
    IsElemAbelian p (GLBConj g E) := by
  have hcomm : ∀ x ∈ GLBConj g E, ∀ y ∈ GLBConj g E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := mem_glbConj.1 hx
    obtain ⟨y0, hy0, rfl⟩ := mem_glbConj.1 hy
    have hc : x0 * y0 = y0 * x0 :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨x0, hx0⟩ ⟨y0, hy0⟩)
    calc g⁻¹ * x0 * g * (g⁻¹ * y0 * g) = g⁻¹ * (x0 * y0) * g := by group
      _ = g⁻¹ * (y0 * x0) * g := by rw [hc]
      _ = g⁻¹ * y0 * g * (g⁻¹ * x0 * g) := by group
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, ?_⟩
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := mem_glbConj.1 hx
  have key : g⁻¹ * x0 * g = g⁻¹ * x0 * g⁻¹⁻¹ := by rw [inv_inv]
  rw [key, conj_pow, hE.2 x0 hx0]
  group

theorem exists_glbConj_le_of_isSylowIn {p : ℕ} [hp : Fact p.Prime] [Finite G] {R : Subgroup G}
    (hR : IsSylowIn p ⊤ R) {E : Subgroup G} (hE : IsPGroup p E) :
    ∃ g : G, GLBConj g E ≤ R := by
  obtain ⟨P₀, hP₀⟩ := IsPGroup.exists_le_sylow hR.2.1
  have hP₀eq : (P₀ : Subgroup G) = R := hR.2.2 P₀ le_top P₀.isPGroup' hP₀
  obtain ⟨Q₀, hQ₀⟩ := IsPGroup.exists_le_sylow hE
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ Q₀
  refine ⟨g, ?_⟩
  intro x hx
  obtain ⟨e, he, rfl⟩ := mem_glbConj.1 hx
  have heQ : e ∈ (Q₀ : Subgroup G) := hQ₀ he
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at heQ
  rw [← hP₀eq]
  have h2 : (MulAut.conj g)⁻¹ • e ∈ (P₀ : Subgroup G) := heQ
  convert h2 using 1
  simp [MulAut.smul_def]

theorem fixed_of_card_two {H : Type} [Group H] (hH : IsPGroup 3 H) {α : Type} [MulAction H α]
    [Finite α] (hα : Nat.card α = 2) (x : α) (h : H) : h • x = x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := hH.card_modEq_card_fixedPoints α
  rw [hα] at hmod
  by_contra hne
  have hsub : MulAction.fixedPoints H α ⊆ ({x}ᶜ : Set α) := by
    intro y hy hyx
    rw [Set.mem_singleton_iff] at hyx
    subst hyx
    exact hne ((MulAction.mem_fixedPoints.1 hy) h)
  have h1 : (MulAction.fixedPoints H α).ncard ≤ ({x}ᶜ : Set α).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x} : Set α).ncard + ({x}ᶜ : Set α).ncard = Nat.card α :=
    Set.ncard_add_ncard_compl _
  rw [Set.ncard_singleton, hα] at h2
  have h3 : Nat.card (MulAction.fixedPoints H α) = (MulAction.fixedPoints H α).ncard :=
    (Nat.card_coe_set_eq _)
  rw [h3] at hmod
  unfold Nat.ModEq at hmod
  omega

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] [Finite G] {P Q : Subgroup G}
    (hP : IsPGroup p P) (hQP : Q ≤ P) (hne : Q ≠ P) :
    ∃ x ∈ P, x ∈ Subgroup.normalizer (Q : Set G) ∧ x ∉ Q := by
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  have hlt : Q.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hQP
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥P) ∈ Q.subgroupOf P := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem
  obtain ⟨-, y, hyN, hyQ'⟩ := SetLike.lt_iff_le_and_exists.1 (hnc (Q.subgroupOf P) hlt)
  refine ⟨(y : G), y.2, ?_, fun hxQ => hyQ' (Subgroup.mem_subgroupOf.2 hxQ)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ P
  · have hh := (Subgroup.mem_normalizer_iff.1 hyN) ⟨g, hg⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hh
    simpa using hh
  · have hgQ : g ∉ Q := fun h => hg (hQP h)
    have hxgQ : (y : G) * g * (y : G)⁻¹ ∉ Q := by
      intro h
      apply hg
      have h1 : (y : G)⁻¹ * ((y : G) * g * (y : G)⁻¹) * (y : G) ∈ P :=
        P.mul_mem (P.mul_mem (P.inv_mem y.2) (hQP h)) y.2
      have h2 : (y : G)⁻¹ * ((y : G) * g * (y : G)⁻¹) * (y : G) = g := by group
      rw [h2] at h1
      exact h1
    exact ⟨fun h => absurd h hgQ, fun h => absurd h hxgQ⟩

theorem finite_subgroup_of_finite [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

theorem not_isPCentral_of_pRank {a : G} [Finite G] (hC : CFSG.Open.pRank 3 (Cg a) = 3)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) : ¬ IsPCentralIn 3 ⊤ a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨R, hR, haR⟩
  have hRC : R ≤ Cg a := by
    intro r hr
    obtain ⟨z, hz, hza⟩ := Subgroup.mem_map.1 haR
    have hcomm := Subgroup.mem_center_iff.1 hz ⟨r, hr⟩
    have hval := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul] at hval
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hza' : (z : G) = a := hza
    rw [hza'] at hval
    exact hval.symm
  obtain ⟨E, -, hEab, hEc⟩ := exists_elemAb_card_pRank (p := 3) (⊤ : Subgroup G)
  have hEp : IsPGroup 3 E := IsPGroup.iff_card.2 ⟨_, hEc⟩
  obtain ⟨g, hg⟩ := exists_glbConj_le_of_isSylowIn hR hEp
  have hE' := isElemAbelian_glbConj hEab g
  have hcard' : Nat.card (GLBConj g E) = 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
    rw [card_glbConj, hEc]
  have hle := le_pRank_of_card (p := 3) (H := Cg a) (hg.trans hRC) hE' hcard'
  rw [hC] at hle
  omega

@[expose] def PsiPred {G : Type} [Group G] (Q : Subgroup G) (a : G) (U : Subgroup G) : Prop :=
  U ≤ centerOf Q ∧ Nat.card U = 3 ∧ GConj (Subgroup.zpowers a) U

theorem glbConj_one (U : Subgroup G) : GLBConj 1 U = U := by
  ext z
  simp [mem_glbConj]

theorem psiPred_glbConj {Q : Subgroup G} {a h : G} (hh : h ∈ Subgroup.normalizer (Q : Set G))
    {U : Subgroup G} (hU : PsiPred Q a U) : PsiPred Q a (GLBConj h⁻¹ U) := by
  obtain ⟨hUc, hUcard, hUg⟩ := hU
  refine ⟨?_, by rw [card_glbConj]; exact hUcard, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_glbConj.1 hz
    rw [inv_inv]
    obtain ⟨y', hy'c, hy'⟩ := Subgroup.mem_map.1 (hUc hy)
    have hy'' : (y' : G) = y := hy'
    have hyQ : y ∈ Q := by
      rw [← hy'']
      exact y'.2
    have hyc' : ∀ g : G, g ∈ Q → g * y = y * g := by
      intro g hg
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hy'c ⟨g, hg⟩)
      simpa [hy''] using this
    refine Subgroup.mem_map.2 ⟨⟨h * y * h⁻¹, ?_⟩, ?_, rfl⟩
    · exact (Subgroup.mem_normalizer_iff.1 hh y).1 hyQ
    · rw [Subgroup.mem_center_iff]
      intro g
      have hg' : (g : G) ∈ Q := g.2
      have hg2 : h⁻¹ * (g : G) * h ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hh)) (g : G)
        rw [inv_inv] at this
        exact this.1 hg'
      have hc : (h⁻¹ * (g : G) * h) * y = y * (h⁻¹ * (g : G) * h) := hyc' _ hg2
      apply Subtype.ext
      show (g : G) * (h * y * h⁻¹) = h * y * h⁻¹ * (g : G)
      calc (g : G) * (h * y * h⁻¹) = h * ((h⁻¹ * (g : G) * h) * y) * h⁻¹ := by group
        _ = h * (y * (h⁻¹ * (g : G) * h)) * h⁻¹ := by rw [hc]
        _ = h * y * h⁻¹ * (g : G) := by group
  · obtain ⟨g, hg⟩ := hUg
    exact ⟨g * h⁻¹, by rw [← hg, glbConj_glbConj]⟩

theorem three_dvd_card_psi {a : G} [Finite G] {Q : Subgroup G} (hQ : IsSylowIn 3 (Cg a) Q)
    (haQ : a ∈ Q) (ha1 : a ≠ 1) (hnc : ¬ IsPCentralIn 3 ⊤ a) :
    3 ∣ Nat.card {U : Subgroup G // PsiPred Q a U} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Subgroup G) := finite_subgroup_of_finite
  have hQN : Q ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer
  have hQp : IsPGroup 3 (Q : Subgroup G) := hQ.2.1
  set S : Set (Subgroup G) := {R | R ≤ Subgroup.normalizer (Q : Set G) ∧ IsPGroup 3 R ∧ Q ≤ R}
    with hS
  have hQS : Q ∈ S := ⟨hQN, hQp, le_rfl⟩
  obtain ⟨H, hHS, hHmax⟩ := Set.exists_max_image S (fun R : Subgroup G => Nat.card R)
    (Set.toFinite S) ⟨Q, hQS⟩
  obtain ⟨hHN, hHp, hQH⟩ := hHS
  have hHmaxW : ∀ R : Subgroup G, R ≤ Subgroup.normalizer (Q : Set G) → IsPGroup 3 R →
      H ≤ R → R = H := by
    intro R hRN hRp hHR
    have hRS : R ∈ S := ⟨hRN, hRp, le_trans hQH hHR⟩
    exact (Subgroup.eq_of_le_of_card_ge hHR (hHmax R hRS)).symm
  letI : MulAction H {U : Subgroup G // PsiPred Q a U} :=
    { smul := fun h U => ⟨GLBConj (h : G)⁻¹ U.1, psiPred_glbConj (hHN h.2) U.2⟩
      one_smul := fun U => Subtype.ext (by
        show GLBConj ((1 : H) : G)⁻¹ U.1 = U.1
        rw [Subgroup.coe_one, inv_one, glbConj_one])
      mul_smul := fun h₁ h₂ U => Subtype.ext (by
        show GLBConj ((h₁ * h₂ : H) : G)⁻¹ U.1 = GLBConj (h₁ : G)⁻¹ (GLBConj (h₂ : G)⁻¹ U.1)
        rw [glbConj_glbConj, Subgroup.coe_mul, mul_inv_rev]) }
  have hmod := (IsPGroup.card_modEq_card_fixedPoints (G := H) hHp
    {U : Subgroup G // PsiPred Q a U})
  have hfix : MulAction.fixedPoints H {U : Subgroup G // PsiPred Q a U} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro U hU
    rw [MulAction.mem_fixedPoints] at hU
    have hV : ∀ h : G, h ∈ H → GLBConj h⁻¹ U.1 = U.1 := fun h hh =>
      congrArg Subtype.val (hU ⟨h, hh⟩)
    obtain ⟨hUc, hUcard, hUg⟩ := U.2
    obtain ⟨g, hg⟩ := hUg
    set y : G := g⁻¹ * a * g with hy_def
    have hyU : y ∈ U.1 := by
      have : y ∈ GLBConj g (Subgroup.zpowers a) := mem_glbConj.2 ⟨a, Subgroup.mem_zpowers a, rfl⟩
      rw [hg] at this
      exact this
    have hy1 : y ≠ 1 := by
      intro h1
      apply ha1
      have h2 : g * y * g⁻¹ = g * 1 * g⁻¹ := by rw [h1]
      rw [hy_def] at h2
      simpa [mul_assoc] using h2
    have hαcard : Nat.card ↥((U.1 : Set G) \ {1}) = 2 := by
      have h1 : (1 : G) ∈ (U.1 : Set G) := U.1.one_mem
      have h2 : ((U.1 : Set G) \ {1}).ncard = (U.1 : Set G).ncard - 1 :=
        Set.ncard_diff_singleton_of_mem h1
      have h3 : (U.1 : Set G).ncard = 3 := by
        rw [← Nat.card_coe_set_eq]
        exact hUcard
      have h4 : Nat.card ↥((U.1 : Set G) \ {1}) = ((U.1 : Set G) \ {1}).ncard :=
        Nat.card_coe_set_eq _
      omega
    have hconj_mem : ∀ h : G, h ∈ H → ∀ u ∈ (U.1 : Set G) \ {1},
        h * u * h⁻¹ ∈ (U.1 : Set G) \ {1} := by
      intro h hh u hu
      have hu1 : u ∈ U.1 := hu.1
      have hu2 : u ≠ 1 := fun h' => hu.2 (Set.mem_singleton_iff.2 h')
      refine ⟨?_, ?_⟩
      · have hm : h * u * h⁻¹ ∈ GLBConj h⁻¹ U.1 := mem_glbConj.2 ⟨u, hu1, by simp⟩
        rw [hV h hh] at hm
        exact hm
      · intro hc
        apply hu2
        have h7 : h * u * h⁻¹ = 1 := Set.mem_singleton_iff.1 hc
        have h6 : h⁻¹ * (h * u * h⁻¹) * h = u := by group
        rw [h7, mul_one, inv_mul_cancel] at h6
        exact h6.symm
    letI : MulAction H ↥((U.1 : Set G) \ {1}) :=
      { smul := fun h u => ⟨(h : G) * u.1 * (h : G)⁻¹, hconj_mem (h : G) h.2 u.1 u.2⟩
        one_smul := fun u => Subtype.ext (by
          show ((1 : H) : G) * u.1 * ((1 : H) : G)⁻¹ = u.1
          rw [Subgroup.coe_one]
          group)
        mul_smul := fun h₁ h₂ u => Subtype.ext (by
          show ((h₁ * h₂ : H) : G) * u.1 * ((h₁ * h₂ : H) : G)⁻¹ =
            (h₁ : G) * ((h₂ : G) * u.1 * (h₂ : G)⁻¹) * (h₁ : G)⁻¹
          rw [Subgroup.coe_mul]
          group) }
    have hyα : y ∈ (U.1 : Set G) \ {1} := ⟨hyU, fun h => hy1 (Set.mem_singleton_iff.1 h)⟩
    have hcomm : ∀ h : G, h ∈ H → h * y = y * h := by
      intro h hh
      have hfx := fixed_of_card_two hHp hαcard ⟨y, hyα⟩ ⟨h, hh⟩
      have hval : h * y * h⁻¹ = y := congrArg Subtype.val hfx
      calc h * y = (h * y * h⁻¹) * h := by group
        _ = y * h := by rw [hval]
    have hH'C : GLBConj g⁻¹ (H : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
      intro z hz
      obtain ⟨h, hh, hzh⟩ := mem_glbConj.1 hz
      rw [inv_inv] at hzh
      rw [← hzh, Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      have hc := hcomm h hh
      calc a * (g * h * g⁻¹) = g * (y * h) * g⁻¹ := by rw [hy_def]; group
        _ = g * (h * y) * g⁻¹ := by rw [hc]
        _ = (g * h * g⁻¹) * a := by rw [hy_def]; group
    have hH'p : IsPGroup 3 ↥(GLBConj g⁻¹ (H : Subgroup G)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hHp
      exact IsPGroup.iff_card.2 ⟨n, by rw [card_glbConj]; exact hn⟩
    have hH'le : Nat.card (GLBConj g⁻¹ (H : Subgroup G)) ≤ Nat.card Q :=
      card_le_of_isSylowIn hQ hH'C hH'p
    have hHQ : H = Q := by
      have hle : Nat.card H ≤ Nat.card Q := by
        rw [← card_glbConj g⁻¹ (H : Subgroup G)]
        exact hH'le
      exact (Subgroup.eq_of_le_of_card_ge hQH hle).symm
    obtain ⟨P, hQP⟩ := IsPGroup.exists_le_sylow hQp
    have hPQ : (P : Subgroup G) = Q := by
      by_contra hne
      have hne' : Q ≠ (P : Subgroup G) := fun h => hne h.symm
      obtain ⟨x, hxP, hxN, hxQ⟩ := exists_mem_normalizer_not_mem P.isPGroup' hQP hne'
      have hMS : (P : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G) ∈ S :=
        ⟨inf_le_right, P.isPGroup'.to_le inf_le_left, le_inf hQP hQN⟩
      have hMle : Nat.card ↥((P : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G)) ≤ Nat.card Q := by
        have := hHmax _ hMS
        rw [hHQ] at this
        exact this
      have hM : (P : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G) = Q :=
        (Subgroup.eq_of_le_of_card_ge (le_inf hQP hQN) hMle).symm
      apply hxQ
      rw [← hM]
      exact Subgroup.mem_inf.2 ⟨hxP, hxN⟩
    have hQsyl : IsSylowIn 3 ⊤ Q := by
      refine ⟨le_top, hQp, fun R' _ hR' hQR' => ?_⟩
      have hR'eq := P.is_maximal' hR' (by rw [hPQ]; exact hQR')
      rw [hPQ] at hR'eq
      exact hR'eq
    have haZ : a ∈ centerOf Q := by
      refine Subgroup.mem_map.2 ⟨⟨a, haQ⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro q
      have hq : (q : G) ∈ Subgroup.centralizer ({a} : Set G) := hQ.1 q.2
      have hqa := Subgroup.mem_centralizer_iff.1 hq a (Set.mem_singleton a)
      apply Subtype.ext
      exact hqa.symm
    exact hnc ⟨Q, hQsyl, haZ⟩
  rw [hfix] at hmod
  have h0 : Nat.card ↥(∅ : Set {U : Subgroup G // PsiPred Q a U}) = 0 := by simp
  rw [h0] at hmod
  exact (Nat.modEq_zero_iff_dvd).1 hmod

theorem relIndex_sup_eq_of_le_normalizer {K X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (K : Set G)) :
    K.relIndex (K ⊔ X) = K.relIndex X := by
  have hY : K ⊔ X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hX
  have hXY : X ≤ K ⊔ X := le_sup_right
  have hKY : K ≤ K ⊔ X := le_sup_left
  haveI : (K.subgroupOf (K ⊔ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hY
  have h1 := Subgroup.relIndex_sup_right (H := X.subgroupOf (K ⊔ X)) (K := K.subgroupOf (K ⊔ X))
  have h2 : X.subgroupOf (K ⊔ X) ⊔ K.subgroupOf (K ⊔ X) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXY hKY, sup_comm, Subgroup.subgroupOf_self]
  rw [h2, Subgroup.relIndex_top_right] at h1
  have h3 := Subgroup.relIndex_subgroupOf (H := K) (K := X) (L := K ⊔ X) hXY
  rw [← h3]
  exact h1

theorem not_mem_of_centralizes {K : Subgroup G} [Finite G] {a : G}
    (hL : IsLThreeFour (barOf 3 K)) (haK : a ∈ K) (hcomm : ∀ k ∈ K, a * k = k * a)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (⟨a, haK⟩ : K) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime ha3 ha1
  have hz : (QuotientGroup.mk (⟨a, haK⟩ : K) : barOf 3 K) ∈ Subgroup.center (barOf 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (hcomm k.1 k.2).symm
  have hz1 : (QuotientGroup.mk (⟨a, haK⟩ : K) : barOf 3 K) = 1 := by
    rw [Lemma1112.center_eq_bot_of_isLThreeFour hL] at hz
    exact Subgroup.mem_bot.1 hz
  have hmem : (⟨a, haK⟩ : K) ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff _).1 hz1
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  have h3 : orderOf (⟨⟨a, haK⟩, hmem⟩ : ↥(GLAPPrimeCore 3 ↥K)) = 3 :=
    (Subgroup.orderOf_mk _ hmem).trans hord
  have hdvd := orderOf_dvd_natCard (⟨⟨a, haK⟩, hmem⟩ : ↥(GLAPPrimeCore 3 ↥K))
  rw [h3] at hdvd
  have := hcop.eq_one_of_dvd hdvd
  norm_num at this

theorem sup_eq_of_card_nine {A B : Subgroup G} [Finite G] (hA : Nat.card A = 27) (hBA : B ≤ A)
    (hB : Nat.card B = 9) {a : G} (haA : a ∈ A) (haB : a ∉ B) :
    B ⊔ Subgroup.zpowers a = A := by
  set H := B ⊔ Subgroup.zpowers a with hH
  have hHA : H ≤ A := sup_le hBA (Subgroup.zpowers_le.2 haA)
  have hBH : B ≤ H := le_sup_left
  have h1 : Nat.card B ∣ Nat.card H := Subgroup.card_dvd_of_le hBH
  have h2 : Nat.card H ∣ Nat.card A := Subgroup.card_dvd_of_le hHA
  rw [hB] at h1
  rw [hA] at h2
  obtain ⟨c, hc⟩ := h1
  have hc3 : c ≤ 3 := by
    have : 9 * c ∣ 27 := by rw [← hc]; exact h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hcases : Nat.card H = 9 ∨ Nat.card H = 27 := by
    interval_cases c
    · exfalso
      have := Nat.card_pos (α := H)
      omega
    · left; omega
    · exfalso
      rw [hc] at h2
      norm_num at h2
    · right; omega
  rcases hcases with h9 | h27
  · exfalso
    apply haB
    have haH : a ∈ H := (le_sup_right : Subgroup.zpowers a ≤ B ⊔ Subgroup.zpowers a)
      (Subgroup.mem_zpowers a)
    have hBeqH : B = H := Subgroup.eq_of_le_of_card_ge hBH (by rw [hB, h9])
    rw [hBeqH]
    exact haH
  · exact Subgroup.eq_of_le_of_card_ge hHA (by rw [hA, h27])

theorem card_inf_eq_nine {K A C : Subgroup G} [Finite G] (hA : Nat.card A = 27) (hAK : ¬ A ≤ K)
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hCN : C ≤ Subgroup.normalizer (K : Set G))
    (hAC : A ≤ K ⊔ C) (hC9 : ¬ 9 ∣ Nat.card C) : Nat.card ↥(K ⊓ A) = 9 := by
  have hρ : K.relIndex A * Nat.card ↥(K ⊓ A) = 27 := by
    have := Subgroup.relIndex_mul_card (H := K) (K := A)
    rw [hA] at this
    exact this
  have hρ' : K.relIndex C * Nat.card ↥(K ⊓ C) = Nat.card C :=
    Subgroup.relIndex_mul_card (H := K) (K := C)
  have hAKC : K ⊔ A ≤ K ⊔ C := sup_le le_sup_left hAC
  have hdiv : K.relIndex A ∣ K.relIndex C := by
    have h := Subgroup.relIndex_mul_relIndex (H := K) (K := K ⊔ A) (L := K ⊔ C) le_sup_left hAKC
    rw [relIndex_sup_eq_of_le_normalizer hAN] at h
    rw [relIndex_sup_eq_of_le_normalizer hCN] at h
    exact ⟨_, h.symm⟩
  have hnot9 : ¬ 9 ∣ K.relIndex C := by
    intro h9
    apply hC9
    rw [← hρ']
    exact Dvd.dvd.mul_right h9 _
  have hpow : K.relIndex A ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num]
    exact ⟨_, hρ.symm⟩
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hpow
  have hj1 : j ≤ 1 := by
    by_contra hj2
    apply hnot9
    have h9 : 9 ∣ K.relIndex A := by
      rw [hjeq, show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 3 (by omega)
    exact h9.trans hdiv
  have hK2 : K.relIndex A = 1 ∨ K.relIndex A = 3 := by
    interval_cases j
    · left; rw [hjeq]; norm_num
    · right; rw [hjeq]; norm_num
  rcases hK2 with h1 | h3
  · exfalso
    rw [h1, one_mul] at hρ
    apply hAK
    have hKA : K ⊓ A = A := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hA, hρ])
    intro x hx
    have : x ∈ K ⊓ A := by rw [hKA]; exact hx
    exact (Subgroup.mem_inf.1 this).1
  · rw [h3] at hρ
    omega

theorem centBar_le_normalizer (p : ℕ) (X L : Subgroup G) :
    centBar p X L ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  unfold centBar at hx
  obtain ⟨hk, -⟩ := hx
  obtain ⟨γ, -, hγx⟩ := Subgroup.mem_map.1 hk
  rw [← hγx]
  exact γ.2

theorem mem_centBar_of_mem_top {p : ℕ} {X L : Subgroup G} {c : G}
    (hc : c ∈ centBar p ⊤ L) (hX : c ∈ X) : c ∈ centBar p X L := by
  unfold centBar at hc ⊢
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hc).1, hX⟩

theorem barAut_eq_one_of_central {K : Subgroup G} (γ : ↥(Subgroup.normalizer (K : Set G)))
    (hγ : ∀ k ∈ K, (γ : G) * k = k * (γ : G)) : barAut 3 K γ = 1 := by
  refine MulEquiv.ext fun y => ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    have hx := hγ x.1 x.2
    show (γ : G) * x.1 * (γ : G)⁻¹ = x.1
    calc (γ : G) * x.1 * (γ : G)⁻¹ = x.1 * (γ : G) * (γ : G)⁻¹ := by rw [hx]
      _ = x.1 := by group

@[expose] def innerSub (K : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (K : Set G) ∧ ∃ k ∈ K, k⁻¹ * x ∈ centBar 3 ⊤ K}
  one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, by
    rw [inv_one, one_mul]; exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hxN, k, hk, hc⟩ ⟨hyN, k', hk', hc'⟩
    have hcN := centBar_le_normalizer 3 ⊤ K hc
    have hck : (k⁻¹ * x) * k' * (k⁻¹ * x)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 hcN k').1 hk'
    refine ⟨Subgroup.mul_mem _ hxN hyN, k * ((k⁻¹ * x) * k' * (k⁻¹ * x)⁻¹),
      Subgroup.mul_mem _ hk hck, ?_⟩
    have e : (k * ((k⁻¹ * x) * k' * (k⁻¹ * x)⁻¹))⁻¹ * (x * y) = (k⁻¹ * x) * (k'⁻¹ * y) := by
      group
    rw [e]
    exact Subgroup.mul_mem _ hc hc'
  inv_mem' := by
    rintro x ⟨hxN, k, hk, hc⟩
    have hcN := centBar_le_normalizer 3 ⊤ K hc
    have hck : (k⁻¹ * x)⁻¹ * k⁻¹ * (k⁻¹ * x)⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hcN) k⁻¹).1 (Subgroup.inv_mem _ hk)
    refine ⟨Subgroup.inv_mem _ hxN, (k⁻¹ * x)⁻¹ * k⁻¹ * (k⁻¹ * x)⁻¹⁻¹,
      hck, ?_⟩
    have e : ((k⁻¹ * x)⁻¹ * k⁻¹ * (k⁻¹ * x)⁻¹⁻¹)⁻¹ * x⁻¹ = (k⁻¹ * x)⁻¹ := by
      group
    rw [e]
    exact Subgroup.inv_mem _ hc

theorem mem_innerSub {K : Subgroup G} {x : G} :
    x ∈ innerSub K ↔ x ∈ Subgroup.normalizer (K : Set G) ∧ ∃ k ∈ K, k⁻¹ * x ∈ centBar 3 ⊤ K :=
  Iff.rfl

theorem le_sup_centBar_of_le_innerSub {K A : Subgroup G} {a : G} (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hAa : A ≤ Subgroup.centralizer ({a} : Set G)) (hA : A ≤ innerSub K) :
    A ≤ K ⊔ centBar 3 (Subgroup.centralizer ({a} : Set G)) K := by
  intro x hx
  obtain ⟨-, k, hk, hc⟩ := mem_innerSub.1 (hA hx)
  have hcCa : k⁻¹ * x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKa hk)) (hAa hx)
  have hcC := mem_centBar_of_mem_top hc hcCa
  have hx' : x = k * (k⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _ (le_sup_left (a := K) (b := centBar 3 _ K) hk)
    (le_sup_right (a := K) (b := centBar 3 _ K) hcC)

theorem exists_mul_of_mem_sup_of_commute {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let M : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
        refine ⟨h1 * h2, H.mul_mem hh1 hh2, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
        calc h1 * h2 * (k1 * k2) = h1 * (h2 * k1) * k2 := by group
          _ = h1 * (k1 * h2) * k2 := by rw [hc h2 hh2 k1 hk1]
          _ = h1 * k1 * (h2 * k2) := by group
      inv_mem' := by
        rintro _ ⟨h1, hh1, k1, hk1, rfl⟩
        have hc' : h1⁻¹ * k1⁻¹ = k1⁻¹ * h1⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, hc h1 hh1 k1 hk1]
        exact ⟨h1⁻¹, H.inv_mem hh1, k1⁻¹, K.inv_mem hk1, by
          rw [mul_inv_rev, ← hc']⟩ }
  have hHM : H ≤ M := fun h hh => ⟨h, hh, 1, K.one_mem, mul_one h⟩
  have hKM : K ≤ M := fun k hk => ⟨1, H.one_mem, k, hk, one_mul k⟩
  obtain ⟨h, hh, k, hk, hhk⟩ := (sup_le hHM hKM : H ⊔ K ≤ M) hx
  exact ⟨h, hh, k, hk, hhk⟩

theorem glbConj_zpowers (g x : G) :
    GLBConj g (Subgroup.zpowers x) = Subgroup.zpowers (g⁻¹ * x * g) := by
  unfold GLBConj
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem gConj_trans {A B C : Subgroup G} (h1 : ∃ g : G, GLBConj g A = B)
    (h2 : ∃ g : G, GLBConj g B = C) : ∃ g : G, GLBConj g A = C := by
  obtain ⟨g1, rfl⟩ := h1
  obtain ⟨g2, rfl⟩ := h2
  exact ⟨g1 * g2, by rw [glbConj_glbConj]⟩

theorem exists_zpowers_mul_of_card_three {A T : Subgroup G} {a : G} (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hAeq : T ⊔ Subgroup.zpowers a = A) (hcomm : ∀ t ∈ T, t * a = a * t)
    [Finite G] {U : Subgroup G} (hUA : U ≤ A) (hU3 : Nat.card U = 3) (hUT : ¬ U ≤ T) :
    ∃ k ∈ T, U = Subgroup.zpowers (k * a) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord3 : ∀ x : G, x ∈ U → x ≠ 1 → orderOf x = 3 := by
    intro x hx hx1
    have hdvd : orderOf x ∣ 3 := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : U)
      rw [hU3] at this
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hzU : ∀ x : G, x ∈ U → x ≠ 1 → Subgroup.zpowers x = U := by
    intro x hx hx1
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.2 hx
    · rw [Nat.card_zpowers, hU3, hord3 x hx hx1]
  obtain ⟨x, hxU, hx1⟩ : ∃ x ∈ U, x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hbot : U = ⊥ := (Subgroup.eq_bot_iff_forall U).2 hcon
    rw [hbot] at hU3
    simp at hU3
  have hUx : U = Subgroup.zpowers x := (hzU x hxU hx1).symm
  have hxA : x ∈ T ⊔ Subgroup.zpowers a := by rw [hAeq]; exact hUA hxU
  obtain ⟨t, ht, z, hz, htz⟩ := exists_mul_of_mem_sup_of_commute
    (fun h hh k hk => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact ((Commute.zpow_right (hcomm h hh : Commute h a) i) : h * a ^ i = a ^ i * h))
    hxA
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hred : a ^ i = a ^ (i % 3) := by
    simpa [hord] using (zpow_mod_orderOf a i).symm
  have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hr with h0 | h1 | h2
  ·
    exfalso
    apply hUT
    rw [hUx, ← htz, hred, h0, zpow_zero, mul_one]
    exact Subgroup.zpowers_le.2 ht
  · refine ⟨t, ht, ?_⟩
    rw [hUx, ← htz, hred, h1, zpow_one]
  · refine ⟨t ^ 2, Subgroup.pow_mem _ ht 2, ?_⟩
    have hcom : Commute t a := hcomm t ht
    have hxeq : x = t * a ^ 2 := by
      rw [← htz, hred, h2]
      simp
    have hsq : x ^ 2 = t ^ 2 * a := by
      rw [hxeq, (hcom.pow_right 2).mul_pow, ← pow_mul,
        show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_add, ha3, one_mul, pow_one]
    have hx2mem : x ^ 2 ∈ U := U.pow_mem hxU 2
    have hx2ne : x ^ 2 ≠ 1 := by
      intro h1'
      have hd := orderOf_dvd_of_pow_eq_one h1'
      rw [hord3 x hxU hx1] at hd
      norm_num at hd
    rw [← hsq]
    exact (hzU (x ^ 2) hx2mem hx2ne).symm

theorem zpowers_eq_of_card_three {U : Subgroup G} [Finite G] (hU3 : Nat.card U = 3) {x : G}
    (hx : x ∈ U) (hx1 : x ≠ 1) : Subgroup.zpowers x = U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : orderOf x ∣ 3 := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : U)
    rw [hU3, Subgroup.orderOf_mk] at this
    exact this
  have hord : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.2 hx
  · rw [Nat.card_zpowers, hU3, hord]

theorem two_mul_card_order_three_subgroups {V : Subgroup G} [Finite G] (hV : ∀ x ∈ V, x ^ 3 = 1) :
    2 * Nat.card {U : Subgroup G // U ≤ V ∧ Nat.card U = 3} + 1 = Nat.card V := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (Subgroup G) := finite_subgroup_of_finite
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  set s : Finset G := (Finset.univ.filter (fun x => x ∈ V)).erase 1 with hs_def
  set t : Finset (Subgroup G) := Finset.univ.filter (fun U : Subgroup G => U ≤ V ∧ Nat.card U = 3)
    with ht_def
  have hcardV : Nat.card V = (Finset.univ.filter (fun x : G => x ∈ V)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcardU : ∀ U : Subgroup G, Nat.card U = (Finset.univ.filter (fun x : G => x ∈ U)).card := by
    intro U
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1V : (1 : G) ∈ (Finset.univ.filter (fun x : G => x ∈ V)) := by
    simp [V.one_mem]
  have hs_card : s.card = Nat.card V - 1 := by
    rw [hs_def, Finset.card_erase_of_mem h1V, hcardV]
  have hmaps : ∀ x ∈ s, Subgroup.zpowers x ∈ t := by
    intro x hx
    rw [hs_def, Finset.mem_erase, Finset.mem_filter] at hx
    obtain ⟨hx1, -, hxV⟩ := hx
    have hord : orderOf x = 3 := by
      have h3 : x ^ 3 = 1 := hV x hxV
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hx1
      · exact h
    rw [ht_def, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Subgroup.zpowers_le.2 hxV, ?_⟩
    rw [Nat.card_zpowers, hord]
  have hfiber : ∀ U ∈ t, (s.filter (fun x => Subgroup.zpowers x = U)).card = 2 := by
    intro U hU
    rw [ht_def, Finset.mem_filter] at hU
    obtain ⟨-, hUV, hU3⟩ := hU
    have heq : s.filter (fun x => Subgroup.zpowers x = U) =
        (Finset.univ.filter (fun x : G => x ∈ U)).erase 1 := by
      ext x
      simp only [hs_def, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hx1, hxV⟩, hzx⟩
        refine ⟨hx1, ?_⟩
        rw [← hzx]
        exact Subgroup.mem_zpowers x
      · rintro ⟨hx1, hxU⟩
        refine ⟨⟨hx1, hUV hxU⟩, ?_⟩
        exact zpowers_eq_of_card_three hU3 hxU hx1
    have h1U : (1 : G) ∈ (Finset.univ.filter (fun x : G => x ∈ U)) := by
      simp [U.one_mem]
    rw [heq, Finset.card_erase_of_mem h1U, ← hcardU, hU3]
  have hsum : s.card = 2 * t.card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, mul_comm]
  have htcard : Nat.card {U : Subgroup G // U ≤ V ∧ Nat.card U = 3} = t.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpos : 0 < Nat.card V := Nat.card_pos
  rw [htcard]
  omega

theorem exists_isSylowIn_ge [Finite G] {X R : Subgroup G} (hRX : R ≤ X) (hR : IsPGroup 3 R) :
    ∃ Q : Subgroup G, IsSylowIn 3 X Q ∧ R ≤ Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Subgroup G) := finite_subgroup_of_finite
  set S : Set (Subgroup G) := {Q | Q ≤ X ∧ IsPGroup 3 Q ∧ R ≤ Q} with hS
  obtain ⟨Q, hQS, hQmax⟩ := Set.exists_max_image S (fun Q : Subgroup G => Nat.card Q)
    (Set.toFinite S) ⟨R, hRX, hR, le_rfl⟩
  obtain ⟨hQX, hQp, hRQ⟩ := hQS
  refine ⟨Q, ⟨hQX, hQp, fun R' hR'X hR'p hQR' => ?_⟩, hRQ⟩
  have hmem : R' ∈ S := ⟨hR'X, hR'p, le_trans hRQ hQR'⟩
  exact (Subgroup.eq_of_le_of_card_ge hQR' (hQmax R' hmem)).symm

theorem pRank_mono [Finite G] {E H : Subgroup G} (hEH : E ≤ H) :
    CFSG.Open.pRank 3 E ≤ CFSG.Open.pRank 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hFE, hF, hFc⟩ := exists_elemAb_card_pRank (p := 3) E
  exact le_pRank_of_card (hFE.trans hEH) hF hFc

theorem le_of_centerOf_of_isSCp {A Q U : Subgroup G} [Finite G] (hA : IsElemAbelian 3 A)
    (hsc : IsSCp 3 ⊤ A) (hAQ : A ≤ Q) (hUQ : U ≤ centerOf Q) (hU3 : Nat.card U = 3) :
    U ≤ A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxU, hx1⟩ : ∃ x ∈ U, x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hbot : U = ⊥ := (Subgroup.eq_bot_iff_forall U).2 hcon
    rw [hbot] at hU3
    simp at hU3
  have hUx : U = Subgroup.zpowers x := (zpowers_eq_of_card_three hU3 hxU hx1).symm
  have hUQ' : ∀ u ∈ U, u ∈ Q ∧ ∀ q ∈ Q, q * u = u * q := by
    intro u hu
    obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.1 (hUQ hu)
    have hzu' : (z : G) = u := hzu
    refine ⟨by rw [← hzu']; exact z.2, fun q hq => ?_⟩
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨q, hq⟩)
    rw [← hzu']
    exact h2
  have hUcomm : ∀ u ∈ U, ∀ v ∈ U, Commute u v := by
    intro u hu v hv
    rw [hUx] at hu hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact Commute.zpow_zpow_self x i j
  have hUexp : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    have hd := orderOf_dvd_natCard (⟨u, hu⟩ : U)
    rw [hU3, Subgroup.orderOf_mk] at hd
    exact orderOf_dvd_iff_pow_eq_one.1 hd
  have hcAU : ∀ a' ∈ A, ∀ u ∈ U, a' * u = u * a' := fun a' ha' u hu =>
    (hUQ' u hu).2 a' (hAQ ha')
  have hAc : ∀ x ∈ A, ∀ y ∈ A, Commute x y := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hD : IsElemAbelian 3 (A ⊔ U) := by
    have hcomm : ∀ x ∈ A ⊔ U, ∀ y ∈ A ⊔ U, x * y = y * x := by
      intro x hx y hy
      obtain ⟨a1, ha1, u1, hu1, rfl⟩ := exists_mul_of_mem_sup_of_commute hcAU hx
      obtain ⟨a2, ha2, u2, hu2, rfl⟩ := exists_mul_of_mem_sup_of_commute hcAU hy
      have hl1 : Commute (a1 * u1) a2 :=
        Commute.mul_left (hAc a1 ha1 a2 ha2) (hcAU a2 ha2 u1 hu1).symm
      have hl2 : Commute (a1 * u1) u2 :=
        Commute.mul_left (hcAU a1 ha1 u2 hu2) (hUcomm u1 hu1 u2 hu2)
      exact (Commute.mul_right hl1 hl2).eq
    refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, fun x hx => ?_⟩
    obtain ⟨a1, ha1, u1, hu1, rfl⟩ := exists_mul_of_mem_sup_of_commute hcAU hx
    have hc1 : Commute a1 u1 := hcAU a1 ha1 u1 hu1
    rw [hc1.mul_pow, hA.2 a1 ha1, hUexp u1 hu1, one_mul]
  have hDeq : A ⊔ U = A := hsc.2.2 (A ⊔ U) le_top hD le_sup_left
  have hUD : U ≤ A ⊔ U := le_sup_right
  rw [hDeq] at hUD
  exact hUD

theorem exists_ne_one_of_card_three {U : Subgroup G} (hU3 : Nat.card U = 3) :
    ∃ x ∈ U, x ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  have hbot : U = ⊥ := (Subgroup.eq_bot_iff_forall U).2 hcon
  rw [hbot] at hU3
  simp at hU3

theorem mem_centerOf_of_mem {Q : Subgroup G} {a : G} (haQ : a ∈ Q)
    (hQC : Q ≤ Subgroup.centralizer ({a} : Set G)) : a ∈ centerOf Q := by
  refine Subgroup.mem_map.2 ⟨⟨a, haQ⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro q
  apply Subtype.ext
  have hq := Subgroup.mem_centralizer_iff.1 (hQC q.2) a (Set.mem_singleton a)
  exact hq.symm

theorem fusion_core [Finite G] {a : G} {Q A T K : Subgroup G}
    (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1)
    (hQ : IsSylowIn 3 (Cg a) Q) (haQ : a ∈ Q) (hAQ : A ≤ Q) (hnc : ¬ IsPCentralIn 3 ⊤ a)
    (hA : IsElemAbelian 3 A) (hsc : IsSCp 3 ⊤ A) (haA : a ∈ A)
    (hTA : T ≤ A) (hT9 : Nat.card T = 9) (haT : a ∉ T) (hAeq : T ⊔ Subgroup.zpowers a = A)
    (hTK : T ≤ K) (hKC : K ≤ Cg a)
    (hfus : ∀ k ∈ T, ∀ k' ∈ T, k ≠ 1 → k' ≠ 1 → ∃ z ∈ K, z⁻¹ * k * z = k')
    (U : Subgroup G) (hUA : U ≤ A) (hU3 : Nat.card U = 3) (hUT : ¬ U ≤ T) :
    GConj (Subgroup.zpowers a) U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Subgroup G) := finite_subgroup_of_finite
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hTa : ∀ t ∈ T, t * a = a * t := fun t ht => hAc t (hTA ht) a haA
  have hzK : ∀ z ∈ K, z * a = a * z := fun z hz =>
    ((Subgroup.mem_centralizer_iff.1 (hKC hz)) a (Set.mem_singleton a)).symm
  have hz_conj : ∀ z ∈ K, z⁻¹ * a * z = a := fun z hz => by
    rw [mul_assoc, ← hzK z hz, ← mul_assoc, inv_mul_cancel, one_mul]
  have hfusA : ∀ k ∈ T, ∀ k' ∈ T, k ≠ 1 → k' ≠ 1 →
      GConj (Subgroup.zpowers (k * a)) (Subgroup.zpowers (k' * a)) := by
    intro k hk k' hk' hk1 hk1'
    obtain ⟨z, hzK', hzk⟩ := hfus k hk k' hk' hk1 hk1'
    refine ⟨z, ?_⟩
    rw [glbConj_zpowers]
    congr 1
    rw [show z⁻¹ * (k * a) * z = (z⁻¹ * k * z) * (z⁻¹ * a * z) by group, hzk, hz_conj z hzK']
  have hfusT : ∀ k ∈ T, ∀ k' ∈ T, k ≠ 1 → k' ≠ 1 →
      GConj (Subgroup.zpowers k) (Subgroup.zpowers k') := by
    intro k hk k' hk' hk1 hk1'
    obtain ⟨z, -, hzk⟩ := hfus k hk k' hk' hk1 hk1'
    exact ⟨z, by rw [glbConj_zpowers, hzk]⟩
  have hzaQ : Subgroup.zpowers a ≤ centerOf Q :=
    Subgroup.zpowers_le.2 (mem_centerOf_of_mem haQ hQ.1)
  have hord_a : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hnotT_a : ¬ Subgroup.zpowers a ≤ T := fun h => haT (h (Subgroup.mem_zpowers a))
  have hVexp : ∀ x ∈ T, x ^ 3 = 1 := fun x hx => hA.2 x (hTA hx)
  by_cases hS : ∃ k ∈ T, k ≠ 1 ∧ GConj (Subgroup.zpowers a) (Subgroup.zpowers (k * a))
  · obtain ⟨k0, hk0T, hk01, hk0G⟩ := hS
    obtain ⟨k, hkT, hUk⟩ := exists_zpowers_mul_of_card_three ha3 ha1 hAeq hTa hUA hU3 hUT
    by_cases hk1 : k = 1
    · rw [hUk, hk1, one_mul]
      exact ⟨1, glbConj_one _⟩
    · rw [hUk]
      exact gConj_trans hk0G (hfusA k0 hk0T k hkT hk01 hk1)
  · exfalso
    push_neg at hS
    have hSnot : ∀ k ∈ T, k ≠ 1 → ¬ GConj (Subgroup.zpowers a) (Subgroup.zpowers (k * a)) :=
      fun k hk hk1 => hS k hk hk1
    have hΨcard : 3 ∣ Set.ncard {U : Subgroup G | PsiPred Q a U} := by
      rw [← Nat.card_coe_set_eq]
      exact three_dvd_card_psi hQ haQ ha1 hnc
    by_cases hT : ∃ t ∈ T, t ≠ 1 ∧ GConj (Subgroup.zpowers a) (Subgroup.zpowers t)
    · obtain ⟨t0, ht0T, ht01, ht0G⟩ := hT
      have hTall : ∀ x ∈ T, x ≠ 1 → GConj (Subgroup.zpowers a) (Subgroup.zpowers x) :=
        fun x hx hx1 => gConj_trans ht0G (hfusT t0 ht0T x hx ht01 hx1)
      set V : Subgroup G := T ⊓ centerOf Q with hV
      set E₁ : Set (Subgroup G) := {U' | U' ≤ V ∧ Nat.card U' = 3} with hE₁
      have hnotE : Subgroup.zpowers a ∉ E₁ := fun h => hnotT_a (le_trans h.1 inf_le_left)
      have hΨeq : {U' : Subgroup G | PsiPred Q a U'} = insert (Subgroup.zpowers a) E₁ := by
        ext U'
        constructor
        · rintro ⟨hUc, hUcard, hUg⟩
          have hUA' : U' ≤ A := le_of_centerOf_of_isSCp hA hsc hAQ hUc hUcard
          by_cases hUT' : U' ≤ T
          · right
            exact ⟨le_inf hUT' hUc, hUcard⟩
          · left
            obtain ⟨k, hkT, hUk⟩ := exists_zpowers_mul_of_card_three ha3 ha1 hAeq hTa hUA' hUcard hUT'
            by_cases hk1 : k = 1
            · rw [hUk, hk1, one_mul]
            · exfalso
              apply hSnot k hkT hk1
              rw [← hUk]
              exact hUg
        · rintro (rfl | ⟨hVU, hUcard⟩)
          · exact ⟨hzaQ, hord_a, ⟨1, glbConj_one _⟩⟩
          · refine ⟨hVU.trans inf_le_right, hUcard, ?_⟩
            obtain ⟨x, hxU, hx1⟩ := exists_ne_one_of_card_three hUcard
            have hUx : U' = Subgroup.zpowers x := (zpowers_eq_of_card_three hUcard hxU hx1).symm
            have hxT : x ∈ T := (hVU.trans inf_le_left) hxU
            rw [hUx]
            exact hTall x hxT hx1
      have hcardΨ : Set.ncard {U' : Subgroup G | PsiPred Q a U'} = Nat.card {U' : Subgroup G // U' ≤ V ∧ Nat.card U' = 3} + 1 := by
        rw [hΨeq, Set.ncard_insert_of_notMem hnotE (Set.toFinite _)]
        rw [← Nat.card_coe_set_eq]
        rfl
      have hKCV := two_mul_card_order_three_subgroups (V := V) (fun x hx => hVexp x ((show V ≤ T from inf_le_left) hx))
      have hVdvd : Nat.card V ∣ 9 := by
        rw [← hT9]
        exact Subgroup.card_dvd_of_le (inf_le_left : V ≤ T)
      obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
        (show Nat.card V ∣ 3 ^ 2 by norm_num; exact hVdvd)
      have hVcases : Nat.card V = 1 ∨ Nat.card V = 3 ∨ Nat.card V = 9 := by
        interval_cases j
        · left; rw [hjeq]; norm_num
        · right; left; rw [hjeq]; norm_num
        · right; right; rw [hjeq]; norm_num
      rw [hcardΨ] at hΨcard
      rcases hVcases with h1 | h1 | h1 <;> omega
    · push_neg at hT
      have hΨone : {U' : Subgroup G | PsiPred Q a U'} = {Subgroup.zpowers a} := by
        ext U'
        constructor
        · rintro ⟨hUc, hUcard, hUg⟩
          have hUA' : U' ≤ A := le_of_centerOf_of_isSCp hA hsc hAQ hUc hUcard
          by_cases hUT' : U' ≤ T
          · exfalso
            obtain ⟨x, hxU, hx1⟩ := exists_ne_one_of_card_three hUcard
            have hUx : U' = Subgroup.zpowers x := (zpowers_eq_of_card_three hUcard hxU hx1).symm
            apply hT x (hUT' hxU) hx1
            rw [← hUx]
            exact hUg
          · obtain ⟨k, hkT, hUk⟩ := exists_zpowers_mul_of_card_three ha3 ha1 hAeq hTa hUA' hUcard hUT'
            by_cases hk1 : k = 1
            · rw [Set.mem_singleton_iff, hUk, hk1, one_mul]
            · exfalso
              apply hSnot k hkT hk1
              rw [← hUk]
              exact hUg
        · rintro rfl
          exact ⟨hzaQ, hord_a, ⟨1, glbConj_one _⟩⟩
      rw [hΨone, Set.ncard_singleton] at hΨcard
      omega

@[expose] def InputL34FusionK : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), IsLThreeFour (barOf 3 K) →
    ∀ x y : K, orderOf x = 3 → orderOf y = 3 → ∃ z : K, z⁻¹ * x * z = y

theorem mem_normalizer_of_central {K : Subgroup G} {a : G} (hcomm : ∀ k ∈ K, a * k = k * a) :
    a ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hk
    have e : a * h * a⁻¹ = h := by rw [hcomm h hk]; group
    rw [e]
    exact hk
  · intro hk
    have hck := hcomm _ hk
    have e1 : a⁻¹ * (a * h * a⁻¹) * a = a * h * a⁻¹ := by
      calc a⁻¹ * (a * h * a⁻¹) * a = a⁻¹ * ((a * h * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * h * a⁻¹)) := by rw [← hck]
        _ = a * h * a⁻¹ := by group
    have e2 : a⁻¹ * (a * h * a⁻¹) * a = h := by group
    rw [e1] at e2
    rw [← e2]
    exact hk

theorem mem_centBar_top_of_central {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hcomm : ∀ k ∈ K, a * k = k * a) :
    a ∈ centBar 3 ⊤ K := by
  unfold centBar
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨a, ha⟩, ?_, rfl⟩, Subgroup.mem_top _⟩
  rw [MonoidHom.mem_ker]
  exact barAut_eq_one_of_central ⟨a, ha⟩ (fun k hk => hcomm k hk)

theorem not_nine_dvd_of_isSylowIn [Finite G] {a : G} {X : Subgroup G} (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hs : IsSylowIn 3 X (Subgroup.zpowers a)) : ¬ 9 ∣ Nat.card X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h9
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥X) 3 (n := 2)
    (by norm_num; exact h9)
  have hRX : P.map X.subtype ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hcardR : Nat.card ↥(P.map X.subtype) = 9 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective P X.subtype X.subtype_injective).toEquiv.symm,
      hP]
    norm_num
  have hRp : IsPGroup 3 (P.map X.subtype) :=
    IsPGroup.iff_card.2 ⟨2, by rw [hcardR]; norm_num⟩
  have hle := card_le_of_isSylowIn hs hRX hRp
  rw [hcardR, Nat.card_zpowers, orderOf_eq_prime ha3 ha1] at hle
  norm_num at hle

@[expose] def P1SylowClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m 3 B M E A a K → IsSylowIn 3 (centBar 3 (Cg a) K) (Subgroup.zpowers a)

theorem p2Claim_of_inputs (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h113 : Lemma113_iStatement) (hL34 : InputL34FusionK) (hsyl : P1SylowClaim) :
    Lemma1112.P2Claim := by
  intro G _ _ m B M E A a K h hsc hr U hU hnU
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hpA, hLK⟩ := h1111 h
  have hAel : IsElemAbelian 3 A := hsc.2.1
  have hcardA : Nat.card A = 27 := by
    rw [Lemma1112.card_eq_pow_pRank hAel, hpA]
    norm_num
  obtain ⟨hE9, hEfaith⟩ := h119 h
  have hEA_el : IsElemAbelian 3 (E ⊓ A) := Lemma1112.isElemAbelian_of_le hAel inf_le_right
  have hcardEA : Nat.card ↥(E ⊓ A) = 9 := by
    rw [Lemma1112.card_eq_pow_pRank hEA_el, hE9]
    norm_num
  obtain ⟨ha, ha1⟩ := h.ha
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hKC : K ≤ Cg a := h.hK.1
  have hcomm : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hKC hk)) a (Set.mem_singleton a)
  have haK : a ∉ K := fun haK => not_mem_of_centralizes hLK haK hcomm ha3 ha1
  have hnotA : ¬ A ≤ K := Lemma1112.not_le_K h hAel hLK
  have haE : a ∉ E ⊓ A := by
    intro haEA
    exact h.notD ⟨E, h.pair.1.1, (Subgroup.mem_inf.1 haEA).1⟩
  have hAsup : (E ⊓ A) ⊔ Subgroup.zpowers a = A :=
    sup_eq_of_card_nine hcardA inf_le_right hcardEA ha haE
  have haN : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_central hcomm
  have hEN : E ⊓ A ≤ Subgroup.normalizer (K : Set G) := hEfaith.1
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := by
    rw [← hAsup]
    exact sup_le hEN (Subgroup.zpowers_le.2 haN)
  have hAin : A ≤ innerSub K := by
    rw [← hAsup]
    refine sup_le (fun x hx => mem_innerSub.2 ⟨hEN hx, hEfaith.2.2 x hx⟩) ?_
    refine Subgroup.zpowers_le.2 (mem_innerSub.2 ⟨haN, 1, Subgroup.one_mem _, ?_⟩)
    rw [inv_one, one_mul]
    exact mem_centBar_top_of_central haN hcomm
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 (fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hAc a ha x hx)
  have hAK : A ≤ K ⊔ centBar 3 (Cg a) K := le_sup_centBar_of_le_innerSub hKC hAa hAin
  have hCN : centBar 3 (Cg a) K ≤ Subgroup.normalizer (K : Set G) := centBar_le_normalizer 3 _ K
  have hsylC : IsSylowIn 3 (centBar 3 (Cg a) K) (Subgroup.zpowers a) := hsyl h
  have hC9 : ¬ 9 ∣ Nat.card (centBar 3 (Cg a) K) := not_nine_dvd_of_isSylowIn ha3 ha1 hsylC
  have hKA9 : Nat.card ↥(K ⊓ A) = 9 := card_inf_eq_nine hcardA hnotA hAN hCN hAK hC9
  have hTA : K ⊓ A ≤ A := inf_le_right
  have hTK : K ⊓ A ≤ K := inf_le_left
  have haT : a ∉ K ⊓ A := fun h' => haK (hTK h')
  have hAeq : (K ⊓ A) ⊔ Subgroup.zpowers a = A :=
    sup_eq_of_card_nine hcardA hTA hKA9 ha haT
  have hA3 : IsPGroup 3 (A : Subgroup G) := IsPGroup.iff_card.2 ⟨3, by rw [hcardA]; norm_num⟩
  obtain ⟨Q, hQ, hAQ⟩ := exists_isSylowIn_ge hAa hA3
  have haQ : a ∈ Q := hAQ ha
  have hC : CFSG.Open.pRank 3 (Cg a) = 3 := hr
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
    le_trans (h113 h.toCex117Base.toSec11 ha ha1 (fun hx => h.notD hx)) (pRank_mono le_top)
  have hnc : ¬ IsPCentralIn 3 ⊤ a := not_isPCentral_of_pRank hC h4
  have hfus : ∀ k ∈ K ⊓ A, ∀ k' ∈ K ⊓ A, k ≠ 1 → k' ≠ 1 → ∃ z ∈ K, z⁻¹ * k * z = k' := by
    intro k hk k' hk' hk1 hk1'
    have hord : ∀ x ∈ K ⊓ A, x ≠ 1 → orderOf x = 3 := fun x hx hx1 =>
      orderOf_eq_prime (hAel.2 x (hTA hx)) hx1
    obtain ⟨z, hz⟩ := hL34 G K hLK ⟨k, hTK hk⟩ ⟨k', hTK hk'⟩
      (by rw [Subgroup.orderOf_mk]; exact hord k hk hk1)
      (by rw [Subgroup.orderOf_mk]; exact hord k' hk' hk1')
    refine ⟨z.1, z.2, ?_⟩
    have := congrArg Subtype.val hz
    simpa using this
  have hU3 : Nat.card U = 3 := by rw [hU.2.2, pow_one]
  have hUT : ¬ U ≤ K ⊓ A := fun hUT' => hnU (le_of_le_of_eq hUT' (inf_comm K A))
  exact fusion_core h.ha.2 ha3 hQ haQ hAQ hnc hAel hsc ha hTA hKA9 haT hAeq hTK hKC hfus U hU.1 hU3 hUT

@[expose] def InputCgNormalizesK : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m 3 B M E A a K → Cg a ≤ Subgroup.normalizer (K : Set G)

@[expose] def InputCentBarRankOne : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m 3 B M E A a K → CFSG.Open.pRank 3 (centBar 3 (Cg a) K) = 1

@[expose] def InputAutL34Order9 : Prop :=
  ∀ (X : Type) [Group X], IsLThreeFour X → ∀ E : Subgroup (MulAut X), IsElemAbelian 3 E →
    Nat.card E ≤ 9

theorem isElemAbelian_map {p : ℕ} {H G' : Type*} [Group H] [Group G'] {E : Subgroup H}
    (hE : IsElemAbelian p E) (f : H →* G') : IsElemAbelian p (E.map f) := by
  have hcomm : ∀ x ∈ E.map f, ∀ y ∈ E.map f, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pow, hE.2 x hx, map_one]

theorem isElemAbelian_subgroupOf {p : ℕ} {S : Subgroup G} (hS : IsElemAbelian p S)
    (C : Subgroup G) : IsElemAbelian p (S.subgroupOf C) := by
  have hcomm : ∀ x y : ↥(S.subgroupOf C), x * y = y * x := by
    intro x y
    have hc : (x : G) * (y : G) = (y : G) * (x : G) :=
      congrArg Subtype.val (hS.1.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.1 x.2⟩
        ⟨(y : G), Subgroup.mem_subgroupOf.1 y.2⟩)
    exact Subtype.ext (Subtype.ext hc)
  refine ⟨⟨⟨fun x y => hcomm x y⟩⟩, fun x hx => ?_⟩
  apply Subtype.ext
  exact hS.2 (x : G) (Subgroup.mem_subgroupOf.1 hx)

theorem isPGroup_of_isElemAbelian {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsPGroup p E := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  have hd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hE.2 g hg)
  rw [Subgroup.orderOf_mk]
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hd with h1 | h1
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [h1, pow_one]⟩

theorem mem_centBar_top_of_barAut_eq_one {K : Subgroup G} (y : ↥(Subgroup.normalizer (K : Set G)))
    (hy : barAut 3 K y = 1) : (y : G) ∈ centBar 3 ⊤ K := by
  unfold centBar
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨y, MonoidHom.mem_ker.2 hy, rfl⟩, Subgroup.mem_top _⟩

theorem p1rank_of_inputs (h1111 : Lemma1111Statement) (hKn : InputCgNormalizesK)
    (hC1 : InputCentBarRankOne) (hAut : InputAutL34Order9) :
    ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
      (h : Cex117 G m 3 B M E A a K), CFSG.Open.pRank 3 (Cg a) = 3 := by
  intro G _ _ m B M E A a K h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hpA, hLK⟩ := h1111 h
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have ha : a ∈ A := h.ha.1
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 (fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨x, hx⟩))
  have hcardA : Nat.card A = 3 ^ 3 := by
    rw [Lemma1112.card_eq_pow_pRank hAel, hpA]
  have hlow : 3 ≤ CFSG.Open.pRank 3 (Cg a) :=
    le_pRank_of_card hAC hAel hcardA
  refine le_antisymm ?_ hlow
  have hKN : Cg a ≤ Subgroup.normalizer (K : Set G) := hKn h
  have hC := hC1 h
  unfold CFSG.Open.pRank
  apply csSup_le
  · have hbot : IsElemAbelian 3 (⊥ : Subgroup G) :=
      ⟨⟨⟨fun x y => Subtype.ext (by
        simp [Subgroup.mem_bot.1 x.2, Subgroup.mem_bot.1 y.2])⟩⟩,
        fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩
    exact ⟨0, ⊥, bot_le, hbot, by simp⟩
  · rintro k ⟨F, hFC, hFab, hFk⟩
    have hFN : F ≤ Subgroup.normalizer (K : Set G) := le_trans hFC hKN
    set F' : Subgroup ↥(Subgroup.normalizer (K : Set G)) := F.subgroupOf _ with hF'
    have hF'ab : IsElemAbelian 3 F' := isElemAbelian_subgroupOf hFab _
    have hA1 : ((barAut 3 K).ker).relIndex F' = Nat.card ↥(F'.map (barAut 3 K)) :=
      Subgroup.relIndex_ker F' (barAut 3 K)
    have hA2 : ((barAut 3 K).ker).relIndex F' * Nat.card ↥((barAut 3 K).ker ⊓ F') = Nat.card F' :=
      Subgroup.relIndex_mul_card (barAut 3 K).ker F'
    have hA3 : Nat.card ↥(F'.map (barAut 3 K)) ≤ 9 :=
      hAut _ hLK _ (isElemAbelian_map hF'ab (barAut 3 K))
    have hcardF' : Nat.card F' = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
    set F'' : Subgroup G := ((barAut 3 K).ker ⊓ F').map (Subgroup.normalizer (K : Set G)).subtype
      with hF''
    have hF''F : F'' ≤ F := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hy).2
    have hF''C : F'' ≤ centBar 3 (Cg a) K := by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_centBar_of_mem_top
        (mem_centBar_top_of_barAut_eq_one y (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hy).1))
        (hFC (hF''F ⟨y, hy, rfl⟩))
    have hF''ab : IsElemAbelian 3 F'' := Lemma1112.isElemAbelian_of_le hFab hF''F
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hF''ab)
    have hn1 : n ≤ 1 := by
      have := le_pRank_of_card hF''C hF''ab hn
      rw [hC] at this
      exact this
    have hcardF''le : Nat.card ↥((barAut 3 K).ker ⊓ F') ≤ 3 := by
      have hcardF''eq : Nat.card F'' = Nat.card ↥((barAut 3 K).ker ⊓ F') :=
        Nat.card_congr (Subgroup.equivMapOfInjective _ _
          (Subgroup.subtype_injective _)).toEquiv.symm
      rw [← hcardF''eq, hn]
      calc (3 : ℕ) ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
        _ = 3 := by norm_num
    have hbound : Nat.card F ≤ 27 := by
      rw [← hcardF', ← hA2, hA1]
      calc Nat.card ↥(F'.map (barAut 3 K)) * Nat.card ↥((barAut 3 K).ker ⊓ F')
          ≤ 9 * 3 := Nat.mul_le_mul hA3 hcardF''le
        _ = 27 := by norm_num
    have hk3 : 3 ^ k ≤ 3 ^ 3 := by
      rw [← hFk]
      exact hbound.trans (by norm_num)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hk3

theorem p1Claim_of_inputs (hsyl : P1SylowClaim) (h1111 : Lemma1111Statement)
    (hKn : InputCgNormalizesK) (hC1 : InputCentBarRankOne) (hAut : InputAutL34Order9) :
    Lemma1112.P1Claim := by
  intro G _ _ m B M E A a K h
  exact ⟨hsyl h, p1rank_of_inputs h1111 hKn hC1 hAut h⟩

end Generic

end Lemma1112b

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
