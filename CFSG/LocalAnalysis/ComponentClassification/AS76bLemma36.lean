module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma36Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma36Defs

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Goldschmidt Asc75Lemma31 Lemma36

namespace Lemma36

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSub_eq_rightConjugate (x : G) (Q : Subgroup G) : conjSub x Q = rightConjugate Q x :=
  rfl

omit [Finite G] in
theorem rightConjugate_le {Q V : Subgroup G} (hQ : Q ≤ V) {a : G}
    (ha : a ∈ normalizer (V : Set G)) : rightConjugate Q a ≤ V := by
  have h1 := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hQ
  change rightConjugate Q a ≤ rightConjugate V a at h1
  rwa [(rightConjugate_eq_self_iff V a).mpr ha] at h1

theorem four_le_card {A R : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) : 4 ≤ Nat.card R := by
  obtain ⟨E, hEK, hE, hcard⟩ :=
    CFSG.SectionRank.exists_pRank one_lt_two (centralizer (A : Set G))
  have hEp : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
  obtain ⟨S, hS, hES⟩ := exists_isSylowOf_le hEK hEp
  obtain ⟨h, -, hh⟩ := Lemma22.exists_conj_eq_of_isSylowOf hR hS
  have hSR : Nat.card S = Nat.card R := by
    rw [hh]
    exact Lemma34.card_conj R h
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (centralizer (A : Set G)) := Nat.pow_le_pow_right two_pos hA.rank
  calc 4 ≤ Nat.card E := h4
    _ ≤ Nat.card S := card_le_of_le hES
    _ = Nat.card R := hSR

theorem exists_conj_eq {A R T : Subgroup G} {g : G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    ∃ x : G, T = rightConjugate R x ∧ rightConjugate A x = rightConjugate A g := by
  obtain ⟨h, hh, hTh⟩ :=
    Lemma22.exists_conj_eq_of_isSylowOf (AschbacherTheorem3.isSylowOf_rightConjugate hR g) hT
  refine ⟨g * h⁻¹, ?_, ?_⟩
  · rw [hTh, ← rightConjugate_mul]
    change (rightConjugate R g).map (MulAut.conj h).toMonoidHom =
      (rightConjugate R g).map (MulAut.conj h⁻¹⁻¹).toMonoidHom
    rw [inv_inv]
  · rw [← rightConjugate_mul]
    apply (rightConjugate_eq_self_iff _ _).mpr
    have hc : h ∈ centralizer (rightConjugate A g : Set G) := by
      rw [centralizer_rightConjugate]
      exact hh
    exact inv_mem (centralizer_le_normalizer _ hc)

theorem inf_eq_bot_of_not_mem {A R T : Subgroup G} {g : G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hg : g ∉ normalizer (A : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) : R ⊓ T = ⊥ := by
  have hKte := tightlyEmbedded_centralizer hA.standard
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rwa [normalizer_centralizer_eq hA.standard]
  have h1 := two_subgroup_inf_conjugate_eq_bot _ T hKte hT.isPGroup g hgK hT.le
  rw [eq_bot_iff, ← h1]
  exact le_inf inf_le_right (inf_le_left.trans hR.le)

theorem conjData (h332 : Lemma33Two) {A R T : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hVe : IsElemAbelian 2 (sec3V R T))
    (hcard : Nat.card R * Nat.card R ≤ Nat.card (sec3V R T)) (hR4 : 4 ≤ Nat.card R) {x y : G}
    (hx : rightConjugate R x ≤ sec3V R T)
    (hy : y ∈ rightConjugate A x ⊓ normalizer (sec3V R T : Set G)) (hodd : Odd (orderOf y))
    (htr : ∀ b ∈ sec3V R T ⊓ rightConjugate A x, ∀ c ∈ sec3V R T ⊓ rightConjugate A x,
      b ≠ 1 → c ≠ 1 → ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c) :
    ConjData (sec3V R T) (rightConjugate R x) (rightConjugate A x) y := by
  have hVp : IsPGroup 2 ↥(sec3V R T) := fun v => ⟨1, Subtype.ext (by simpa using hVe.2 v v.2)⟩
  have hRxC : rightConjugate R x ≤ centralizer (rightConjugate A x : Set G) := by
    rw [centralizer_rightConjugate]
    exact map_mono hR.le
  have hVAK : sec3V R T ≤ rightConjugate A x ⊔ rightConjugate (centralizer (A : Set G)) x := by
    refine iSup₂_le fun z hz => ?_
    have hzV : rightConjugate R z ≤ sec3V R T := le_sec3V hz
    have hzc : rightConjugate R z ≤ centralizer (rightConjugate R x : Set G) :=
      (hzV.trans (le_centralizer_self_of_isElemAbelian hVe)).trans
        (centralizer_le fun v hv => hx hv)
    have hc : rightConjugate (rightConjugate R z) x⁻¹ ≤ centralizer (R : Set G) := by
      have h1 : centralizer (R : Set G) =
          rightConjugate (centralizer (rightConjugate R x : Set G)) x⁻¹ := by
        rw [← centralizer_rightConjugate, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
      rw [h1]
      exact map_mono hzc
    have hle := conj_le_sup_centralizer h332 hA hR ⟨z * x⁻¹, by rw [rightConjugate_mul]⟩ hc
    calc rightConjugate R z = rightConjugate (rightConjugate (rightConjugate R z) x⁻¹) x := by
          rw [rightConjugate_mul, rightConjugate_mul]
          congr 1
          group
      _ ≤ rightConjugate (A ⊔ centralizer (A : Set G)) x := map_mono hle
      _ = rightConjugate A x ⊔ rightConjugate (centralizer (A : Set G)) x := Subgroup.map_sup _ _ _
  have hKxA : rightConjugate (centralizer (A : Set G)) x ≤ normalizer (rightConjugate A x : Set G) :=
    by
      rw [← centralizer_rightConjugate]
      exact centralizer_le_normalizer _
  have hVle : sec3V R T ≤ rightConjugate R x ⊔ rightConjugate A x :=
    le_sup_of_isSylowOf hKxA (AschbacherTheorem3.isSylowOf_rightConjugate hR x) hx hVp hVAK
  have hR4' : 4 ≤ Nat.card (rightConjugate R x) := by
    rw [rightConjugate_card]
    exact hR4
  exact
    { elem := hVe
      le := hx
      sup_eq := (eq_sup_inf_of_le_sup hx (hRxC.trans (centralizer_le_normalizer _)) hVle).symm
      le_centralizer := hRxC
      mem := (mem_inf.mp hy).1
      mem_normalizer := (mem_inf.mp hy).2
      odd := hodd
      trans := htr
      four_le := hR4'
      card_lt := by
        rw [rightConjugate_card]
        have h1 : 4 * Nat.card R ≤ Nat.card R * Nat.card R := Nat.mul_le_mul_right _ hR4
        omega }

theorem inf_eq_bot_of_ne {A R V : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) {x₁ x₂ y₁ : G}
    (d₁ : ConjData V (rightConjugate R x₁) (rightConjugate A x₁) y₁)
    (hx₂ : rightConjugate R x₂ ≤ V) (hne : rightConjugate R x₁ ≠ rightConjugate R x₂) :
    rightConjugate R x₁ ⊓ rightConjugate R x₂ = ⊥ := by
  have hKte := tightlyEmbedded_centralizer hA.standard
  have hK1te := tightlyEmbedded_rightConjugate hKte x₁
  have hR2p : IsPGroup 2 ↥(rightConjugate R x₂) := hR.isPGroup.map _
  have hR2K : rightConjugate R x₂ ≤ rightConjugate (centralizer (A : Set G)) x₂ := map_mono hR.le
  by_cases hu : x₁⁻¹ * x₂ ∈ normalizer (rightConjugate (centralizer (A : Set G)) x₁ : Set G)
  · exfalso
    apply hne
    have hK : rightConjugate (centralizer (A : Set G)) x₂ =
        rightConjugate (centralizer (A : Set G)) x₁ := by
      rw [show x₂ = x₁ * (x₁⁻¹ * x₂) by group, ← rightConjugate_mul,
        (rightConjugate_eq_self_iff _ _).mpr hu]
    have hle : rightConjugate R x₂ ≤ rightConjugate R x₁ := by
      rw [← d₁.fixGrp_eq]
      intro v hv
      refine mem_inf.mpr ⟨hx₂ hv, mem_centralizer_singleton_iff.mpr ?_⟩
      have hvK : v ∈ rightConjugate (centralizer (A : Set G)) x₁ := hK ▸ hR2K hv
      rw [← centralizer_rightConjugate] at hvK
      exact (mem_centralizer_iff.mp hvK y₁ d₁.mem).symm
    exact (eq_of_le_of_card_ge hle (by rw [rightConjugate_card, rightConjugate_card])).symm
  · have hle : rightConjugate R x₂ ≤
        rightConjugate (rightConjugate (centralizer (A : Set G)) x₁) (x₁⁻¹ * x₂) := by
      rw [rightConjugate_mul, mul_inv_cancel_left]
      exact hR2K
    have h1 := two_subgroup_inf_conjugate_eq_bot _ _ hK1te hR2p _ hu hle
    rw [eq_bot_iff, ← h1]
    exact le_inf inf_le_right (inf_le_left.trans (map_mono hR.le))

theorem normalizer_le {A R : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (x : G) :
    normalizer (rightConjugate R x : Set G) ≤ normalizer (rightConjugate A x : Set G) := by
  have hKte := tightlyEmbedded_centralizer hA.standard
  have hR1 : R ≠ ⊥ := Lemma22.ne_bot_of_isSylowOf_of_tightlyEmbedded hKte hR
  have hRx1 : rightConjugate R x ≠ ⊥ := by
    intro h
    apply hR1
    have hc := rightConjugate_card R x
    rw [h, card_bot] at hc
    exact card_eq_one.mp hc.symm
  intro z hz
  have h1 := normalizer_two_subgroup_le _ _ (tightlyEmbedded_rightConjugate hKte x)
    (hR.isPGroup.map _) (map_mono hR.le) hRx1 hz
  rw [mem_normalizer_rightConjugate_iff] at h1 ⊢
  rwa [← normalizer_centralizer_eq hA.standard]

theorem pairData {A R V : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) {x₁ x₂ y₁ y₂ : G}
    (d₁ : ConjData V (rightConjugate R x₁) (rightConjugate A x₁) y₁)
    (d₂ : ConjData V (rightConjugate R x₂) (rightConjugate A x₂) y₂)
    (hn₁ : ∀ z ∈ normalizer (rightConjugate A x₁ : Set G) ⊓ normalizer (V : Set G),
      z⁻¹ * y₁ * z ∈ zpowers y₁ ⊔ centralizer (V : Set G))
    (hn₂ : ∀ z ∈ normalizer (rightConjugate A x₂ : Set G) ⊓ normalizer (V : Set G),
      z⁻¹ * y₂ * z ∈ zpowers y₂ ⊔ centralizer (V : Set G))
    (hne : rightConjugate R x₁ ≠ rightConjugate R x₂) :
    PairData V (rightConjugate R x₁) (rightConjugate A x₁) (rightConjugate R x₂)
      (rightConjugate A x₂) y₁ y₂ where
  d₁ := d₁
  d₂ := d₂
  inf_eq_bot := inf_eq_bot_of_ne hA hR d₁ d₂.le hne
  ti₁ := fun x hx hxne => by
    rw [conjSub_eq_rightConjugate, rightConjugate_mul] at hxne ⊢
    exact inf_eq_bot_of_ne hA hR d₁ (by
      rw [← rightConjugate_mul]
      exact rightConjugate_le d₁.le (pairGroup_le hx)) (Ne.symm hxne)
  ti₂ := fun x hx hxne => by
    rw [conjSub_eq_rightConjugate, rightConjugate_mul] at hxne ⊢
    exact inf_eq_bot_of_ne hA hR d₂ (by
      rw [← rightConjugate_mul]
      exact rightConjugate_le d₂.le (pairGroup_le hx)) (Ne.symm hxne)
  norm₁ := fun x hx hxQ => hn₁ x (mem_inf.mpr
    ⟨normalizer_le hA hR x₁ (mem_normalizer_of_conjSub_eq hxQ), pairGroup_le hx⟩)
  norm₂ := fun x hx hxQ => hn₂ x (mem_inf.mpr
    ⟨normalizer_le hA hR x₂ (mem_normalizer_of_conjSub_eq hxQ), pairGroup_le hx⟩)

theorem main_of_data {A R T V : Subgroup G} {g xT : G} {y : G → G}
    (hTx : T = rightConjugate R xT) (hAx : rightConjugate A xT = rightConjugate A g)
    (hRV : R ≤ V) (hTV : T ≤ V) (hRneT : R ≠ T)
    (hd : ∀ x, rightConjugate R x ≤ V →
      ConjData V (rightConjugate R x) (rightConjugate A x) (y x))
    (hp : ∀ x₁ x₂, rightConjugate R x₁ ≤ V → rightConjugate R x₂ ≤ V →
      rightConjugate R x₁ ≠ rightConjugate R x₂ →
      PairData V (rightConjugate R x₁) (rightConjugate A x₁) (rightConjugate R x₂)
        (rightConjugate A x₂) (y x₁) (y x₂)) :
    (⁅A ⊓ normalizer (V : Set G), V⁆ = T ∧
      ⁅rightConjugate A g ⊓ normalizer (V : Set G), V⁆ = R ∧
      ∀ x : G, rightConjugate R x ≤ V → rightConjugate R x = R ∨ rightConjugate R x = T) ∨
    (⁅A ⊓ normalizer (V : Set G), V⁆ = ⁅rightConjugate A g ⊓ normalizer (V : Set G), V⁆ ∧
      (∀ v ∈ V, v ∉ ⁅A ⊓ normalizer (V : Set G), V⁆ ↔
        ∃ x : G, rightConjugate R x ≤ V ∧ v ∈ rightConjugate R x ∧ v ≠ 1) ∧
      ∀ x₁ x₂ x₁' x₂' : G, rightConjugate R x₁ ≤ V → rightConjugate R x₂ ≤ V →
        rightConjugate R x₁' ≤ V → rightConjugate R x₂' ≤ V →
        rightConjugate R x₁ ≠ rightConjugate R x₂ →
        rightConjugate R x₁' ≠ rightConjugate R x₂' →
        ∃ n ∈ normalizer (V : Set G),
          rightConjugate (rightConjugate R x₁) n = rightConjugate R x₁' ∧
            rightConjugate (rightConjugate R x₂) n = rightConjugate R x₂') := by
  have hR1 : rightConjugate R 1 ≤ V := by
    rw [rightConjugate_one]
    exact hRV
  have hT1 : rightConjugate R xT ≤ V := by
    rw [← hTx]
    exact hTV
  have dR : ConjData V R A (y 1) := by
    have := hd 1 hR1
    rwa [rightConjugate_one, rightConjugate_one] at this
  have dT : ConjData V T (rightConjugate A g) (y xT) := by
    have := hd xT hT1
    rwa [← hTx, hAx] at this
  have hpR : ∀ x, rightConjugate R x ≤ V → R ≠ rightConjugate R x →
      PairData V R A (rightConjugate R x) (rightConjugate A x) (y 1) (y x) := by
    intro x hx hne
    have := hp 1 x hR1 hx (by rwa [rightConjugate_one])
    rwa [rightConjugate_one, rightConjugate_one] at this
  have hpT : ∀ x, rightConjugate R x ≤ V → T ≠ rightConjugate R x →
      PairData V T (rightConjugate A g) (rightConjugate R x) (rightConjugate A x) (y xT) (y x) := by
    intro x hx hne
    have := hp xT x hT1 hx (by rwa [← hTx])
    rwa [← hTx, hAx] at this
  have hpRT : PairData V R A T (rightConjugate A g) (y 1) (y xT) := by
    have := hpR xT hT1 (by rwa [← hTx])
    rwa [← hTx, hAx] at this
  have hyR : ∀ k : ℕ, conjSub (y 1 ^ k) R = R := by
    intro k
    rw [← dR.fixGrp_eq]
    exact Hyp.conjSub_fixGrp (npow_mem_zpowers _ k)
  by_cases hXR : ∀ x ∈ pairGroup V A (rightConjugate A g), conjSub x R = R
  ·
    obtain ⟨hT0, hR0, -⟩ := hpRT.eq_of_normalizes hXR
    refine Or.inl ⟨by rw [dR.commutator_eq, hT0], by rw [dT.commutator_eq, hR0], fun x hx => ?_⟩
    by_cases hxR : rightConjugate R x = R
    · exact Or.inl hxR
    refine Or.inr ?_
    have dQ := hd x hx
    have hpRQ := hpR x hx (Ne.symm hxR)
    by_cases hX' : ∀ x' ∈ pairGroup V A (rightConjugate A x), conjSub x' R = R
    · obtain ⟨h1, -, -⟩ := hpRQ.eq_of_normalizes hX'
      rw [h1, hT0]
    push Not at hX'
    obtain ⟨x₀, hx₀, hx₀R⟩ := hX'
    have hTQ : V ⊓ A ≤ V ⊓ rightConjugate A x :=
      hpRQ.le_of_ne_bot₁ hx₀ hx₀R inf_le_left hpRQ.normalizes₂ dQ.inf_ne_bot
    by_contra hQT
    have hpTQ := hpT x hx (Ne.symm hQT)
    by_cases hX'' : ∀ x' ∈ pairGroup V (rightConjugate A g) (rightConjugate A x),
        conjSub x' T = T
    · obtain ⟨h1, -, -⟩ := hpTQ.eq_of_normalizes hX''
      exact hxR (h1.trans hR0.symm)
    push Not at hX''
    obtain ⟨x₀', hx₀', hx₀T⟩ := hX''
    have hRQ : V ⊓ rightConjugate A g ≤ V ⊓ rightConjugate A x :=
      hpTQ.le_of_ne_bot₁ hx₀' hx₀T inf_le_left hpTQ.normalizes₂ dQ.inf_ne_bot
    have hVle : V ≤ V ⊓ rightConjugate A x :=
      calc V = R ⊔ (V ⊓ A) := dR.sup_eq.symm
        _ ≤ V ⊓ rightConjugate A x := sup_le ((le_of_eq hR0).trans hRQ) hTQ
    apply dQ.ne_bot
    rw [eq_bot_iff, ← dQ.inf_eq_bot]
    exact le_inf le_rfl (dQ.le.trans hVle)
  ·
    push Not at hXR
    obtain ⟨x₀, hx₀, hx₀R⟩ := hXR
    obtain ⟨htr, hcov⟩ := hpRT.case_three₁ hx₀ hx₀R
    have hVV : V ⊓ rightConjugate A g = V ⊓ A := by
      have hle : V ⊓ A ≤ V ⊓ rightConjugate A g :=
        hpRT.le_of_ne_bot₁ hx₀ hx₀R inf_le_left hpRT.normalizes₂ dT.inf_ne_bot
      refine (eq_of_le_of_card_ge hle ?_).symm
      have h1 := dR.card_eq
      have h2 := dT.card_eq
      have hRT' : Nat.card T = Nat.card R := by rw [hTx, rightConjugate_card]
      rw [hRT'] at h2
      exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.symm.trans h1)).le
    have hall : ∀ x, rightConjugate R x ≤ V →
        ∃ a ∈ pairGroup V A (rightConjugate A g), rightConjugate R x = conjSub a R := by
      intro x hx
      by_contra hnot
      push Not at hnot
      have hQ0 : rightConjugate R x ≤ V ⊓ A := by
        intro q hq
        by_contra hq0
        obtain ⟨a, ha, hqa, hq1⟩ := (hcov q (hx hq)).mp hq0
        have haV : rightConjugate R a ≤ V := rightConjugate_le hRV (pairGroup_le ha)
        have hQa : rightConjugate R x ⊓ conjSub a R = ⊥ :=
          (hp x a hx haV (hnot a ha)).inf_eq_bot
        have hmem : q ∈ rightConjugate R x ⊓ conjSub a R := mem_inf.mpr ⟨hq, hqa⟩
        rw [hQa, mem_bot] at hmem
        exact hq1 hmem
      have hQR : R ≠ rightConjugate R x := fun h1 =>
        hnot 1 (one_mem _) (h1.symm.trans (G2.conjSub_one R).symm)
      have hpRQ := hpR x hx hQR
      obtain ⟨hQ0', hR0', -⟩ := hpRQ.eq_of_normalizes (hpRQ.normalizes_of_le hQ0)
      have hQT : T ≠ rightConjugate R x := by
        intro h1
        apply dT.ne_bot
        rw [eq_bot_iff, ← dT.inf_eq_bot]
        exact le_inf le_rfl (h1.trans (hQ0'.trans hVV.symm)).le
      have hpTQ := hpT x hx hQT
      obtain ⟨-, hT0', -⟩ := hpTQ.eq_of_normalizes (hpTQ.normalizes_of_le
        (hQ0'.trans hVV.symm).le)
      exact hRneT (hR0'.trans hT0'.symm)
    refine Or.inr ⟨by rw [dR.commutator_eq, dT.commutator_eq, hVV], fun v hv => ?_, ?_⟩
    · rw [dR.commutator_eq]
      constructor
      · intro hv0
        obtain ⟨a, ha, hva, hv1⟩ := (hcov v hv).mp hv0
        exact ⟨a, rightConjugate_le hRV (pairGroup_le ha), hva, hv1⟩
      · rintro ⟨x, hx, hvx, hv1⟩ hv0
        obtain ⟨a, ha, hxa⟩ := hall x hx
        have hmem : v ∈ conjSub a R ⊓ (V ⊓ A) := mem_inf.mpr ⟨hxa ▸ hvx, hv0⟩
        have hbot : conjSub a R ⊓ (V ⊓ A) = ⊥ := by
          rw [← hpRT.normalizes₁ a ha, ← G2.conjSub_inf, dR.inf_eq_bot, conjSub_bot]
        rw [hbot, mem_bot] at hmem
        exact hv1 hmem
    · intro x₁ x₂ x₁' x₂' h₁ h₂ h₁' h₂' hne hne'
      obtain ⟨a₁, ha₁, e₁⟩ := hall x₁ h₁
      obtain ⟨a₂, ha₂, e₂⟩ := hall x₂ h₂
      obtain ⟨a₁', ha₁', e₁'⟩ := hall x₁' h₁'
      obtain ⟨a₂', ha₂', e₂'⟩ := hall x₂' h₂'
      have hc : ∀ {b₁ b₂ : G}, conjSub b₁ R ≠ conjSub b₂ R → conjSub (b₂ * b₁⁻¹) R ≠ R := by
        intro b₁ b₂ hb h0
        apply hb
        calc conjSub b₁ R = conjSub b₁ (conjSub (b₂ * b₁⁻¹) R) := by rw [h0]
          _ = conjSub b₂ R := by rw [G2.conjSub_conjSub, inv_mul_cancel_right]
      obtain ⟨k, hk⟩ := htr _ (mul_mem ha₂ (inv_mem ha₁)) _ (mul_mem ha₂' (inv_mem ha₁'))
        (hc (by rwa [← e₁, ← e₂])) (hc (by rwa [← e₁', ← e₂']))
      refine ⟨a₁⁻¹ * y 1 ^ k * a₁', pairGroup_le (mul_mem (mul_mem (inv_mem ha₁)
        (pow_mem hpRT.mem₁ k)) ha₁'), ?_, ?_⟩
      · rw [e₁, e₁']
        change conjSub (a₁⁻¹ * y 1 ^ k * a₁') (conjSub a₁ R) = conjSub a₁' R
        rw [G2.conjSub_conjSub, show a₁ * (a₁⁻¹ * y 1 ^ k * a₁') = y 1 ^ k * a₁' by group,
          ← G2.conjSub_conjSub, hyR]
      · rw [e₂, e₂']
        change conjSub (a₁⁻¹ * y 1 ^ k * a₁') (conjSub a₂ R) = conjSub a₂' R
        calc conjSub (a₁⁻¹ * y 1 ^ k * a₁') (conjSub a₂ R)
            = conjSub a₁' (conjSub (y 1 ^ k) (conjSub (a₂ * a₁⁻¹) R)) := by
              rw [G2.conjSub_conjSub, G2.conjSub_conjSub, G2.conjSub_conjSub]
              congr 1
              group
          _ = conjSub a₁' (conjSub (a₂' * a₁'⁻¹) R) := by rw [hk]
          _ = conjSub a₂' R := by rw [G2.conjSub_conjSub, inv_mul_cancel_right]

end Lemma36

theorem lemma36 (h32 : Lemma32) (h332 : Lemma33Two) :
    ∀ (G : Type) [Group G] [Finite G] (A R T : Subgroup G) (g : G), Hyp31 A →
      IsSylowOf 2 R (centralizer (A : Set G)) → g ∉ normalizer (A : Set G) →
      IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) →
      T ≤ centralizer (R : Set G) → Star36 A R (sec3V R T) →
      (⁅A ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ = T ∧
        ⁅rightConjugate A g ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ = R ∧
        ∀ x : G, rightConjugate R x ≤ sec3V R T →
          rightConjugate R x = R ∨ rightConjugate R x = T) ∨
      (⁅A ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ =
          ⁅rightConjugate A g ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ ∧
        (∀ v ∈ sec3V R T, v ∉ ⁅A ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ ↔
          ∃ x : G, rightConjugate R x ≤ sec3V R T ∧ v ∈ rightConjugate R x ∧ v ≠ 1) ∧
        ∀ x₁ x₂ x₁' x₂' : G, rightConjugate R x₁ ≤ sec3V R T → rightConjugate R x₂ ≤ sec3V R T →
          rightConjugate R x₁' ≤ sec3V R T → rightConjugate R x₂' ≤ sec3V R T →
          rightConjugate R x₁ ≠ rightConjugate R x₂ →
          rightConjugate R x₁' ≠ rightConjugate R x₂' →
          ∃ n ∈ normalizer (sec3V R T : Set G),
            rightConjugate (rightConjugate R x₁) n = rightConjugate R x₁' ∧
              rightConjugate (rightConjugate R x₂) n = rightConjugate R x₂') := by
  intro G _ _ A R T g hA hR hg hT hTR hstar
  have hRe : IsElemAbelian 2 R := h32 G A hA R hR
  obtain ⟨xT, hTx, hAx⟩ := Lemma36.exists_conj_eq hR hT
  have hTconj : ∃ y, T = rightConjugate R y := ⟨xT, hTx⟩
  have hVe := isElemAbelian_sec3V hRe hTR hTconj
  have hRTV := le_sec3V_of hTconj
  have hRT := Lemma36.inf_eq_bot_of_not_mem hA hR hg hT
  have hR4 := Lemma36.four_le_card hA hR
  have hRneT : R ≠ T := by
    intro h
    apply Lemma22.ne_bot_of_isSylowOf_of_tightlyEmbedded (tightlyEmbedded_centralizer hA.standard) hR
    rw [← inf_idem R]
    nth_rewrite 2 [h]
    exact hRT
  have hcard : Nat.card R * Nat.card R ≤ Nat.card (sec3V R T) := by
    have h1 : Nat.card (R ⊔ T : Subgroup G) = Nat.card R * Nat.card T :=
      card_sup_eq_mul (hTR.trans (centralizer_le_normalizer _)) hRT
    have h2 : Nat.card T = Nat.card R := by rw [hTx, rightConjugate_card]
    calc Nat.card R * Nat.card R = Nat.card R * Nat.card T := by rw [h2]
      _ = Nat.card (R ⊔ T : Subgroup G) := h1.symm
      _ ≤ Nat.card (sec3V R T) := card_le_of_le hRTV
  unfold Star36 at hstar
  choose! y hyB hyodd hytr hynorm using hstar
  have hd : ∀ x, rightConjugate R x ≤ sec3V R T →
      Lemma36.ConjData (sec3V R T) (rightConjugate R x) (rightConjugate A x) (y x) :=
    fun x hx => Lemma36.conjData h332 hA hR hVe hcard hR4 hx (hyB x hx) (hyodd x hx) (hytr x hx)
  exact Lemma36.main_of_data hTx hAx (le_sup_left.trans hRTV) (le_sup_right.trans hRTV) hRneT hd
    fun x₁ x₂ h₁ h₂ hne => Lemma36.pairData hA hR (hd x₁ h₁) (hd x₂ h₂) (hynorm x₁ h₁)
      (hynorm x₂ h₂) hne

end CFSG.ComponentClassification.AS76b
