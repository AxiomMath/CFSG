module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidConj
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6JBoundTw
public import CFSG.LieType.Chevalley.E6GraphLeviIntersections

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section TwE6

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def LangSetup.DescendsTwE6 (S : LangSetup TwistTag.E6.tag L p) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra K L) (σ : K ≃+* K)
    (e : twistedE6RootGroup K σ ≃* S.Γ), Nat.card K = S.D.q ^ 2 ∧
      (∀ c : K, algebraMap K L (σ c) = (algebraMap K L c) ^ S.D.q) ∧
      ∀ h : twistedE6RootGroup K σ, (e h : ModGL TwistTag.E6.tag L) =
        S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL TwistTag.E6.tag K) * S.D.g0

theorem LangSetup.descendsTwE6 (S : LangSetup TwistTag.E6.tag L p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr)
    (hAlg : S.IsAlgebraic) : S.DescendsTwE6 := by
  classical
  obtain ⟨Fr, hFr, hΦ⟩ := hΦ
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hfin, hcard⟩ := ncard_pow_eq_self (L := L) r (2 * e) (by omega)
  let K : Subfield L := (iterateFrobenius L r (2 * e)).eqLocusField (RingHom.id L)
  have hset : (K : Set L) = {c : L | c ^ (r ^ (2 * e)) = c} := by
    ext c
    change iterateFrobenius L r (2 * e) c = c ↔ _
    rw [iterateFrobenius_def]
    rfl
  have hfinK : Finite K := by
    have h1 : (K : Set L).Finite := by rw [hset]; exact hfin
    exact h1.to_subtype
  have hKcard : Nat.card K = (r ^ e) ^ 2 := by
    have h1 : Nat.card K = (K : Set L).ncard := Nat.card_coe_set_eq (K : Set L)
    rw [h1, hset, hcard, ← pow_mul, mul_comm]
  let σh : K →+* K := iterateFrobenius K r e
  have hσb : Function.Bijective σh :=
    Finite.injective_iff_bijective.1 σh.injective
  let σ : K ≃+* K := RingEquiv.ofBijective σh hσb
  have hσ : ∀ c : K, σ c = c ^ (r ^ e) := fun c => iterateFrobenius_def r e c
  have hFr' : ∀ c : L, Fr c = c ^ (r ^ e) := fun c => by rw [hFr, hq]
  have : IsAlgClosure K L := ⟨inferInstance, ⟨fun c => by
    obtain ⟨n, hn, hc⟩ := hAlg c
    refine ⟨Polynomial.X ^ (S.D.q ^ n) - Polynomial.X, ?_, ?_⟩
    · have hq1 : 1 < S.D.q ^ n := Nat.one_lt_pow hn.ne' S.hqpow.1.one_lt
      exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hc, sub_self]⟩⟩
  have hσ' : ∀ c : K, σ c = c ^ (r ^ e) := hσ
  have hℓ := hr
  have hf : 1 ≤ e := he
  have hK' : Nat.card K = (r ^ e) ^ 2 := hKcard
  have hΦ' : S.D.Φ = twistHom TwistTag.E6 L Fr := hΦ
  refine ⟨K, inferInstance, hfinK, inferInstance, σ,
    twistedE6EquivΓ hℓ hf hK' hσ' hFr' S.D hΦ', ?_, ?_, fun h => ?_⟩
  · rw [hKcard, hq]
  · intro c
    have : (algebraMap K L) (σ c) = (algebraMap K L) (c ^ (r ^ e)) := by rw [hσ']
    rw [this, map_pow, hq]
  · exact coe_twistedE6EquivΓ hℓ hf hK' hσ' hFr' S.D hΦ' h

@[expose] def CosetCentralizerEmpty {τ : Tag} (S : LangSetup τ L p)
    (D₁ : Subgroup (ModGL τ L)) (P : ModGL τ L) : Prop :=
  ∀ w ∈ adjointGroup τ L, ¬ ∀ x ∈ rigidTestSet S D₁, Commute (w * P) x

theorem twE6_hnf {r e : ℕ} (hr : r.Prime) (K : Type) [Field K] [Finite K] [Algebra K L]
    (hK : Nat.card K = (r ^ e) ^ 2) (he : 1 ≤ e) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (r ^ e))
    (α : MulAut (twistedE6RootGroup K σ)) :
    ∃ (y : ModGL TwistTag.E6.tag K) (δ : K ≃+* K),
      baseChangeGL (algebraMap K L) y ∈ adjointGroup TwistTag.E6.tag L ∧
        ∀ h : twistedE6RootGroup K σ, (α h : ModGL TwistTag.E6.tag K) =
          y * Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) * y⁻¹ := by
  obtain ⟨-, -, -, -, -, hcd, hfa, hex, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hr he K hK σ hσ
  obtain ⟨g, u, δ, hα⟩ := hex α
  refine ⟨(g : ModGL TwistTag.E6.tag K) *
    rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u), δ, ?_, fun h => ?_⟩
  · rw [map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (LieType.Chevalley.baseChangeGL_mem_adjointGroup _
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedE6RootGroup_le σ g.2))
      (torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _))
  · rw [hα]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hcd, hfa]
    group

theorem setupRigid_of_descends_twistedE6 (S : LangSetup TwistTag.E6.tag L p)
    (hd : S.DescendsTwE6)
    (hF : ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁)
    (hIg : ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CosetCentralizerEmpty S D₁ (diagramMap TwistTag.E6 L)) : SetupRigid S := by
  classical
  obtain ⟨K, _, _, _, σ, e, hK2, hσL, he⟩ := hd
  obtain ⟨r, f, hr, hchar, hf, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hKf : Nat.card K = (r ^ f) ^ 2 := by rw [hK2, hq]
  have hσK : ∀ c : K, σ c = c ^ (r ^ f) := fun c => by
    apply (algebraMap K L).injective
    rw [hσL, map_pow, hq]
  set P : ModGL TwistTag.E6.tag L := diagramMap TwistTag.E6 L with hPdef
  have hPadj : ∀ x ∈ adjointGroup TwistTag.E6.tag L, P * x * P⁻¹ ∈ adjointGroup TwistTag.E6.tag L :=
    fun x hx => E6GraphLevi.diagramMap_conj_mem_adjointGroup' hx
  obtain ⟨-, -, -, -, -, -, hfa, -, -, hσP, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hr hf K hKf σ hσK
  have hg0C := S.D.g0_mem
  obtain ⟨u, hu⟩ : ∃ u : ModGL TwistTag.E6.tag L,
      u = (Units.map (entrywiseHom (iterateFrobenius L r f)) S.D.g0)⁻¹ * P * S.D.g0 :=
    ⟨_, rfl⟩
  have hbase : ∀ g : ModGL TwistTag.E6.tag K,
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ.toRingHom) g) =
        Units.map (entrywiseHom (iterateFrobenius L r f)) (baseChangeGL (algebraMap K L) g) :=
    fun g => by
    have h1 : (iterateFrobenius L r f).comp (algebraMap K L) =
        (algebraMap K L).comp σ.toRingHom := RingHom.ext fun c => by
      change iterateFrobenius L r f (algebraMap K L c) = algebraMap K L (σ c)
      rw [iterateFrobenius_def, hσK, map_pow]
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h1]
  have hshift : ∀ x : S.Γ, Units.map (entrywiseHom (iterateFrobenius L r f))
      (x : ModGL TwistTag.E6.tag L) = u * x * u⁻¹ := by
    intro x
    obtain ⟨h, rfl⟩ := e.surjective x
    have hx := he h
    have hσh : Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
          (diagramMap TwistTag.E6 K)⁻¹ := (hfa σ h).symm.trans (hσP h)
    have hbcP : baseChangeGL (algebraMap K L) (diagramMap TwistTag.E6 K) = P :=
      baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6
    rw [hx, hu, map_mul, map_mul, map_inv, ← hbase, hσh, map_mul, map_mul, map_inv, hbcP]
    group
  refine setupRigid_of_conj_gen S hr (by omega : 1 ≤ f * 2) (by rw [hKf, ← pow_mul])
    (twistedE6RootGroup K σ) e he (adjointGroup TwistTag.E6.tag L : Set _)
    {w | w ∈ adjointGroup TwistTag.E6.tag L ∨
      ∃ c ∈ adjointGroup TwistTag.E6.tag L, w = c * P}
    (fun α => ?_) ?_ (fun D₁ hD₁ hc w hw hwc x => ?_)
  · obtain ⟨y, δ, hyC, hy⟩ := twE6_hnf (L := L) hr K hKf hf σ hσK α
    exact ⟨y, δ, hyC, hy⟩
  · intro D₁ hD₁ hc j hj y hyC z hz hfix
    have hψ0 : ∀ x : ModGL TwistTag.E6.tag L,
        Units.map (entrywiseHom (iterateFrobenius L r 0)) x = x := fun x => by
      rw [iterateFrobenius_zero]
      exact Units.ext (entrywise_id _)
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨z, Or.inl ?_, fun x => ?_⟩
      · rw [hz, hψ0]
        exact mul_mem (mul_mem (inv_mem hg0C) hyC) hg0C
      · rw [hψ0]
    by_cases hjf : j < f
    · exact absurd hfix (hF D₁ hD₁ hc r f j hr hq (Nat.pos_of_ne_zero hj0) hjf z)
    by_cases hjeq : j = f
    · subst hjeq
      refine ⟨S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * P * S.D.g0,
        Or.inr ⟨S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * (P * S.D.g0 * P⁻¹), ?_, by group⟩,
        fun x => ?_⟩
      · exact mul_mem (mul_mem (inv_mem hg0C) hyC) (hPadj _ hg0C)
      · rw [hshift x, hz, hu]
        group
    · exfalso
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + f := ⟨j - f, by omega⟩
      have hj'0 : 0 < j' := by omega
      have hj'f : j' < f := by omega
      refine hF D₁ hD₁ hc r f j' hr hq hj'0 hj'f
        (z * Units.map (entrywiseHom (iterateFrobenius L r j')) u) ?_
      intro x hx
      have hxΓ : x ∈ S.Γ := rigidTestSet_subset_Γ S hD₁ hx
      have h1 := hfix x hx
      have e1 : Units.map (entrywiseHom (iterateFrobenius L r (j' + f))) x =
          Units.map (entrywiseHom (iterateFrobenius L r j')) u *
            Units.map (entrywiseHom (iterateFrobenius L r j')) x *
              (Units.map (entrywiseHom (iterateFrobenius L r j')) u)⁻¹ := by
        rw [iterateFrobenius_add, ← units_map_entrywiseHom_comp (t := TwistTag.E6)]
        have := hshift ⟨x, hxΓ⟩
        simp only at this
        rw [this, map_mul, map_mul, map_inv]
      rw [e1] at h1
      calc z * Units.map (entrywiseHom (iterateFrobenius L r j')) u *
            Units.map (entrywiseHom (iterateFrobenius L r j')) x *
              (z * Units.map (entrywiseHom (iterateFrobenius L r j')) u)⁻¹ =
          z * (Units.map (entrywiseHom (iterateFrobenius L r j')) u *
            Units.map (entrywiseHom (iterateFrobenius L r j')) x *
              (Units.map (entrywiseHom (iterateFrobenius L r j')) u)⁻¹) * z⁻¹ := by group
        _ = x := h1
  · rcases hw with hw | ⟨c, hcC, rfl⟩
    · rw [hI D₁ hD₁ hc w hw hwc]
      exact Commute.one_left _
    · exact absurd hwc (hIg D₁ hD₁ hc c hcC)

theorem setupRigid_twistedE6 (S : LangSetup TwistTag.E6.tag L p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr)
    (hAlg : S.IsAlgebraic)
    (hF : ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁)
    (hIg : ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CosetCentralizerEmpty S D₁ (diagramMap TwistTag.E6 L)) : SetupRigid S :=
  setupRigid_of_descends_twistedE6 S (S.descendsTwE6 hΦ hAlg) hF hI hIg

theorem setupRigid_twistedE6_of_big (S : LangSetup TwistTag.E6.tag L p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr)
    (hAlg : S.IsAlgebraic)
    (hbig : ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      HasBigInnerComponent S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁)
    (hIg : ∀ D₁ : Subgroup (ModGL TwistTag.E6.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CosetCentralizerEmpty S D₁ (diagramMap TwistTag.E6 L)) : SetupRigid S :=
  setupRigid_twistedE6 S hΦ hAlg
    (fun D₁ hD₁ hc => noFrobeniusInner_of_big_inner S (by decide) (Or.inr (Or.inr (Or.inl rfl))) hD₁ (hbig D₁ hD₁ hc))
    hI hIg

end TwE6

end CFSG.HardMathSupport.Timmesfeld.LangTorus
