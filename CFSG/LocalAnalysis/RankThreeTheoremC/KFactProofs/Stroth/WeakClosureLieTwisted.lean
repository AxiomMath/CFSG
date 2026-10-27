module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieDerived
public import CFSG.LieType.BorelTits.Twisted

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.BorelTits

theorem wcT_d4_theta_height :
    0 < height (rootAt TwistTag.D4.tag 19 (by decide)).1 := by
  change 0 < height (d4Certificate.root 19)
  decide +kernel

section Assembly

variable {t : TwistTag} {K : Type} [Field K] [Finite K] {σ : K →+* K} {p : ℕ} [Fact p.Prime]
  [CharP K p]

theorem wcT_wcOn_of_noncomm_pair (hσ : Function.Surjective σ)
    (hU : ∀ x ∈ (nativeData t.tag K).U, twistC t K σ x = x → x ∈ twistDerived t K σ)
    [Finite (DerivedCentralQuotient (twistedFixedGroup t K σ))]
    {x y : adjointGroup t.tag K} (hxU : x ∈ (nativeData t.tag K).U)
    (hyU : y ∈ (nativeData t.tag K).U) (hxF : twistC t K σ x = x) (hyF : twistC t K σ y = y)
    (hxy : x * y ≠ y * x) : WCOn p (DerivedCentralQuotient (twistedFixedGroup t K σ)) := by
  obtain ⟨S, hS⟩ := exists_sylow_twistFixed t K σ p hσ
  have hSle : (S : Subgroup (twistFixed t K σ)) ≤ commutator (twistFixed t K σ) := by
    intro g hg
    rw [hS] at hg
    obtain ⟨y', hy', hyx⟩ := hU g hg g.2
    rwa [Subtype.ext hyx] at hy'
  refine WCOn.of_derivedCentralQuotient_noncomm (twistedFixedGroup t K σ)
    (twistedFixedGroupEquiv t K σ) (holds_twistFixed t K σ p hσ) S hSle S.isPGroup' hSle
    (x := ⟨x, hxF⟩) (y := ⟨y, hyF⟩) ?_ ?_ ?_
  · rw [hS]
    exact hxU
  · rw [hS]
    exact hyU
  · intro h
    exact hxy (congrArg Subtype.val h)

end Assembly

section E6

variable {K : Type} [Field K]

theorem wcT_e6_noncomm :
    xElement (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) (1 : K) * xElement ⟨3, by decide⟩ 1 ≠
      xElement ⟨3, by decide⟩ 1 * xElement (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) 1 := by
  intro h
  have hc := e6_commutator (K := K) 1 1
  have h1 : xElement (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) (1 : K) *
      xElement ⟨3, by decide⟩ 1 * (xElement (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) 1)⁻¹ *
        (xElement ⟨3, by decide⟩ 1)⁻¹ = 1 := by
    rw [h]
    group
  rw [hc] at h1
  have h2 := eltElement_injective (rootAt TwistTag.E6.tag 9 (by decide))
    (h1.trans ((rootOperatorFamily TwistTag.E6.tag).eltElement_zero _).symm)
  simp at h2

variable [Finite K] {σ : K →+* K} {p : ℕ} [Fact p.Prime] [CharP K p]

theorem wcT_wcOn_twistedE6 (hσ : Function.Surjective σ)
    (hU : ∀ x ∈ (nativeData TwistTag.E6.tag K).U, twistC .E6 K σ x = x →
      x ∈ twistDerived .E6 K σ)
    [Finite (DerivedCentralQuotient (twistedFixedGroup .E6 K σ))] :
    WCOn p (DerivedCentralQuotient (twistedFixedGroup .E6 K σ)) :=
  wcT_wcOn_of_noncomm_pair hσ hU
    ((nativeData TwistTag.E6.tag K).simple_le_U ⟨1, by decide⟩ (xElement_mem_X _ _))
    ((nativeData TwistTag.E6.tag K).simple_le_U ⟨3, by decide⟩ (xElement_mem_X _ _))
    (xElement_mem_twistFixed (t := .E6) (i := ⟨1, by decide⟩) (by decide) (map_one σ))
    (xElement_mem_twistFixed (t := .E6) (i := ⟨3, by decide⟩) (by decide) (map_one σ))
    wcT_e6_noncomm

end E6

section D4

variable {K : Type} [Field K]

theorem wcT_d4_noncomm :
    xElement (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) (1 : K) *
        (rootOperatorFamily TwistTag.D4.tag).eltElement
          (rootAt TwistTag.D4.tag 19 (by decide)) (1 : K) ≠
      (rootOperatorFamily TwistTag.D4.tag).eltElement
          (rootAt TwistTag.D4.tag 19 (by decide)) (1 : K) *
        xElement (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by
  intro h
  have hc := d4_commutator (K := K) 1 1
  have h1 : xElement (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) (1 : K) *
      (rootOperatorFamily TwistTag.D4.tag).eltElement
        (rootAt TwistTag.D4.tag 19 (by decide)) (1 : K) *
        (xElement (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) 1)⁻¹ *
        ((rootOperatorFamily TwistTag.D4.tag).eltElement
          (rootAt TwistTag.D4.tag 19 (by decide)) (1 : K))⁻¹ = 1 := by
    rw [h]
    group
  rw [hc] at h1
  have h2 := eltElement_injective (rootAt TwistTag.D4.tag 22 (by decide))
    (h1.trans ((rootOperatorFamily TwistTag.D4.tag).eltElement_zero _).symm)
  simp at h2

theorem wcT_d4_theta_mem_twistFixed (σ : K →+* K) :
    (rootOperatorFamily TwistTag.D4.tag).eltElement
      (rootAt TwistTag.D4.tag 19 (by decide)) (1 : K) ∈ twistFixed .D4 K σ := by
  have hw := d4_weylTwist_w
  obtain ⟨ε, hε, h⟩ := exists_conj_nrep (K := K)
    ((coxeterSystem TwistTag.D4.tag).wordProd (twistOrbitWord .D4 ⟨0, by decide⟩))
    (simpleRoot TwistTag.D4.tag ⟨2, by decide⟩)
  rw [d4_w_smul] at h
  have h1 := h ε
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  rw [hεε, eltElement_simpleRoot] at h1
  rw [← h1]
  exact mul_mem (mul_mem (nrep_mem_twistFixed' hw)
    (xElement_mem_twistFixed (by decide) (ringHom_eq_of_sign hε)))
    (inv_mem (nrep_mem_twistFixed' hw))

variable [Finite K] {σ : K →+* K} {p : ℕ} [Fact p.Prime] [CharP K p]

theorem wcT_d4_theta_mem_U :
    (rootOperatorFamily TwistTag.D4.tag).eltElement
      (rootAt TwistTag.D4.tag 19 (by decide)) (1 : K) ∈ (nativeData TwistTag.D4.tag K).U :=
  RootGroupData.X_le_U (D := nativeData TwistTag.D4.tag K)
    (by
      change 0 < height (rootAt TwistTag.D4.tag 19 (by decide)).1
      exact wcT_d4_theta_height)
    ((rootOperatorFamily TwistTag.D4.tag).eltElement_mem_rootSubgroup _ _)

theorem wcT_wcOn_trialityD4 (hσ : Function.Surjective σ)
    (hU : ∀ x ∈ (nativeData TwistTag.D4.tag K).U, twistC .D4 K σ x = x →
      x ∈ twistDerived .D4 K σ)
    [Finite (DerivedCentralQuotient (twistedFixedGroup .D4 K σ))] :
    WCOn p (DerivedCentralQuotient (twistedFixedGroup .D4 K σ)) :=
  wcT_wcOn_of_noncomm_pair hσ hU
    ((nativeData TwistTag.D4.tag K).simple_le_U ⟨2, by decide⟩ (xElement_mem_X _ _))
    wcT_d4_theta_mem_U
    (xElement_mem_twistFixed (t := .D4) (i := ⟨2, by decide⟩) (by decide) (map_one σ))
    (wcT_d4_theta_mem_twistFixed σ)
    wcT_d4_noncomm

end D4

theorem wcT_model_data {G : Type} [Group G] {t : TwistTag} {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) (h : TwistedChevalleyModel G t (p ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p) (σ : F →+* F),
      Function.Surjective σ ∧
      (∀ x ∈ (nativeData t.tag F).U, twistC t F σ x = x → x ∈ twistDerived t F σ) ∧
      Nonempty (G ≃* DerivedCentralQuotient (twistedFixedGroup t F σ)) := by
  obtain ⟨F, _, _, hF, σ, hσc, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hcard : Nat.card F = p ^ (f * t.order) := by rw [hF, pow_mul]
  have : CharP F p := charP_of_natCard_eq hcard
  have hσ : Function.Surjective σ := surjective_ringHom_of_finite F σ
  have hfr : ∀ c : F, c ^ Nat.card F = c := fun c => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hq : 2 ≤ p ^ f :=
    (Nat.Prime.two_le Fact.out).trans (Nat.le_self_pow (by omega) p)
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    have hm : 2 ≤ t.order := by cases t <;> decide
    calc 4 = 2 ^ 2 := rfl
      _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ (p ^ f) ^ t.order := Nat.pow_le_pow_right (by omega) hm
  obtain ⟨u, hu⟩ := exists_units_sq_ne_one h4
  have hU : ∀ x ∈ (nativeData t.tag F).U, twistC t F σ x = x → x ∈ twistDerived t F σ := by
    cases t with
    | E6 =>
      refine e6_U_le_twistDerived hσ (fun c => ?_) hu
      have hc : p ^ f * p ^ f = Nat.card F := by
        rw [hF]
        change _ = (p ^ f) ^ 2
        ring
      rw [hσc, hσc, ← pow_mul, hc, hfr]
    | D4 =>
      refine d4_U_le_twistDerived hσ (fun c => ?_) hu
      have hc : p ^ f * (p ^ f * p ^ f) = Nat.card F := by
        rw [hF]
        change _ = (p ^ f) ^ 3
        ring
      rw [hσc, hσc, hσc, ← pow_mul, ← pow_mul, hc, hfr]
  exact ⟨F, inferInstance, inferInstance, inferInstance, σ, hσ, hU, ⟨e⟩⟩

theorem wcOn_twistedE6 {K : Type} [Group K] [Finite K] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h : TwistedChevalleyModel K .E6 (p ^ f)) : WCOn p K := by
  obtain ⟨F, _, _, _, σ, hσ, hU, ⟨e⟩⟩ := wcT_model_data hf h
  have := Finite.of_equiv _ e.toEquiv
  exact WCOn.of_mulEquiv e (wcT_wcOn_twistedE6 hσ hU)

theorem wcOn_trialityD4 {K : Type} [Group K] [Finite K] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h : TwistedChevalleyModel K .D4 (p ^ f)) : WCOn p K := by
  obtain ⟨F, _, _, _, σ, hσ, hU, ⟨e⟩⟩ := wcT_model_data hf h
  have := Finite.of_equiv _ e.toEquiv
  exact WCOn.of_mulEquiv e (wcT_wcOn_trialityD4 hσ hU)

theorem wcOn_chevalley_twisted {K : Type} [Group K] [Finite K] {t : CFSG.Open.StatedLieTag}
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ht : t = .twistedE6 ∨ t = .trialityD4)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel K t p f) : WCOn p K := by
  obtain ⟨hadm, hmodel⟩ := h
  rcases ht with rfl | rfl
  · exact wcOn_twistedE6 hadm.2.1 hmodel
  · exact wcOn_trialityD4 hadm.2.1 hmodel

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
