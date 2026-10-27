module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidTwE6

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley


section Conj

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem normal_form_of_conj_testSet (S : LangSetup τ L p) {K : Type} [Field K] [Finite K]
    [Algebra K L] {p₀ fK : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ fK) (hK : Nat.card K = p₀ ^ fK)
    [ExpChar L p₀] (C : Subgroup (ModGL τ K)) (e : C ≃* S.Γ)
    (he : ∀ h : C, (e h : ModGL τ L) =
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * S.D.g0)
    (Y0 Ycl : Set (ModGL τ L))
    (hnf : ∀ α : MulAut C, ∃ (y : ModGL τ K) (σ : K ≃+* K),
      baseChangeGL (algebraMap K L) y ∈ Y0 ∧ ∀ h : C,
        (α h : ModGL τ K) = y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * y⁻¹)
    (X : Set (ModGL τ L)) (hXΓ : X ⊆ S.Γ)
    (hreal : ∀ j : ℕ, j < fK → ∀ y : ModGL τ K, baseChangeGL (algebraMap K L) y ∈ Y0 →
      ∀ z : ModGL τ L, z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y *
        Units.map (entrywiseHom (iterateFrobenius L p₀ j)) S.D.g0 →
      (∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L p₀ j)) x * z⁻¹ = x) →
      ∃ w ∈ Ycl, ∀ x : S.Γ,
        z * Units.map (entrywiseHom (iterateFrobenius L p₀ j)) (x : ModGL τ L) * z⁻¹ =
          w * x * w⁻¹)
    (δ : MulAut S.Γ) (hfixX : ∀ x : S.Γ, (x : ModGL τ L) ∈ X → δ x = x) :
    ∃ w ∈ Ycl, ∀ x : S.Γ, (δ x : ModGL τ L) = w * x * w⁻¹ := by
  classical
  obtain ⟨y, σ, hyY, hy⟩ := hnf ((e.trans δ).trans e.symm)
  obtain ⟨j, hj, hσj⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow hp₀ hf hK σ
  obtain ⟨σ', hσ'⟩ : ∃ σ' : L →+* L, σ' = iterateFrobenius L p₀ j := ⟨_, rfl⟩
  have hσ'ι : ∀ c : K, σ' (algebraMap K L c) = algebraMap K L (σ.toRingHom c) := fun c => by
    rw [hσ', iterateFrobenius_def, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσj, map_pow]
  have hbase : ∀ g : ModGL τ K,
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ.toRingHom) g) =
        Units.map (entrywiseHom σ') (baseChangeGL (algebraMap K L) g) := fun g => by
    have h1 : σ'.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom := RingHom.ext hσ'ι
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h1]
  obtain ⟨z, hz⟩ : ∃ z : ModGL τ L, z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y *
      Units.map (entrywiseHom σ') S.D.g0 := ⟨_, rfl⟩
  have hδx : ∀ x : S.Γ, (δ x : ModGL τ L) = z * Units.map (entrywiseHom σ') x * z⁻¹ := by
    intro x
    obtain ⟨h, rfl⟩ := e.surjective x
    have h1 : δ (e h) = e (((e.trans δ).trans e.symm) h) := by simp
    have h2 : baseChangeGL (algebraMap K L) (h : ModGL τ K) =
        S.D.g0 * (e h : ModGL τ L) * S.D.g0⁻¹ := by
      rw [he]
      group
    rw [h1, he, hy, map_mul, map_mul, map_inv, hbase, h2, map_mul, map_mul, map_inv, hz]
    group
  have hfix : ∀ x ∈ X, z * Units.map (entrywiseHom σ') x * z⁻¹ = x := by
    intro x hx
    have h1 : δ ⟨x, hXΓ hx⟩ = ⟨x, hXΓ hx⟩ := hfixX ⟨x, hXΓ hx⟩ hx
    have h2 := hδx ⟨x, hXΓ hx⟩
    rw [h1] at h2
    exact h2.symm
  rw [hσ'] at hz hfix hδx
  obtain ⟨w, hwY, hw⟩ := hreal j hj y hyY z hz hfix
  exact ⟨w, hwY, fun x => (hδx x).trans (hw x)⟩

end Conj

section TwE6

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem normal_form_twE6 (S : LangSetup TwistTag.E6.tag L p) (hd : S.DescendsTwE6)
    (X : Set (ModGL TwistTag.E6.tag L)) (hXΓ : X ⊆ S.Γ)
    (hF : ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL TwistTag.E6.tag L,
        ¬ ∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x)
    (δ : MulAut S.Γ) (hfix : ∀ x : S.Γ, (x : ModGL TwistTag.E6.tag L) ∈ X → δ x = x) :
    ∃ z : ModGL TwistTag.E6.tag L, (z ∈ adjointGroup TwistTag.E6.tag L ∨
        ∃ w ∈ adjointGroup TwistTag.E6.tag L, z = w * diagramMap TwistTag.E6 L) ∧
      ∀ x : S.Γ, (δ x : ModGL TwistTag.E6.tag L) = z * x * z⁻¹ := by
  classical
  obtain ⟨K, _, _, _, σ, e, hK2, hσL, he⟩ := hd
  obtain ⟨r, f, hr, hchar, hf, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hKf : Nat.card K = (r ^ f) ^ 2 := by rw [hK2, hq]
  have hσK : ∀ c : K, σ c = c ^ (r ^ f) := fun c => by
    apply (algebraMap K L).injective
    rw [hσL, map_pow, hq]
  set P : ModGL TwistTag.E6.tag L := diagramMap TwistTag.E6 L with hPdef
  have hPadj : ∀ x ∈ adjointGroup TwistTag.E6.tag L,
      P * x * P⁻¹ ∈ adjointGroup TwistTag.E6.tag L :=
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
  have hnf : ∀ α : MulAut (twistedE6RootGroup K σ), ∃ (y : ModGL TwistTag.E6.tag K) (δ' : K ≃+* K),
      baseChangeGL (algebraMap K L) y ∈ (adjointGroup TwistTag.E6.tag L : Set _) ∧
        ∀ h : twistedE6RootGroup K σ, (α h : ModGL TwistTag.E6.tag K) =
          y * Units.map (entrywiseHom δ'.toRingHom) (h : ModGL TwistTag.E6.tag K) * y⁻¹ := by
    intro α
    obtain ⟨y, δ', hyC, hy⟩ := twE6_hnf (L := L) hr K hKf hf σ hσK α
    exact ⟨y, δ', hyC, hy⟩
  have hreal : ∀ j : ℕ, j < f * 2 → ∀ y : ModGL TwistTag.E6.tag K,
      baseChangeGL (algebraMap K L) y ∈ (adjointGroup TwistTag.E6.tag L : Set _) →
      ∀ z : ModGL TwistTag.E6.tag L, z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y *
        Units.map (entrywiseHom (iterateFrobenius L r j)) S.D.g0 →
      (∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x) →
      ∃ w ∈ {w | w ∈ adjointGroup TwistTag.E6.tag L ∨
          ∃ c ∈ adjointGroup TwistTag.E6.tag L, w = c * P}, ∀ x : S.Γ,
        z * Units.map (entrywiseHom (iterateFrobenius L r j)) (x : ModGL TwistTag.E6.tag L) *
          z⁻¹ = w * x * w⁻¹ := by
    intro j hj y hyC z hz hfix'
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
    · exact absurd hfix' (hF r f j hr hq (Nat.pos_of_ne_zero hj0) hjf z)
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
      refine hF r f j' hr hq hj'0 hj'f
        (z * Units.map (entrywiseHom (iterateFrobenius L r j')) u) ?_
      intro x hx
      have h1 := hfix' x hx
      have e1 : Units.map (entrywiseHom (iterateFrobenius L r (j' + f))) x =
          Units.map (entrywiseHom (iterateFrobenius L r j')) u *
            Units.map (entrywiseHom (iterateFrobenius L r j')) x *
              (Units.map (entrywiseHom (iterateFrobenius L r j')) u)⁻¹ := by
        rw [iterateFrobenius_add, ← units_map_entrywiseHom_comp (t := TwistTag.E6)]
        have := hshift ⟨x, hXΓ hx⟩
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
  obtain ⟨w, hwY, hw⟩ := normal_form_of_conj_testSet S hr (by omega : 1 ≤ f * 2)
    (by rw [hKf, ← pow_mul]) (twistedE6RootGroup K σ) e he (adjointGroup TwistTag.E6.tag L : Set _)
    {w | w ∈ adjointGroup TwistTag.E6.tag L ∨
      ∃ c ∈ adjointGroup TwistTag.E6.tag L, w = c * P}
    hnf X hXΓ hreal δ hfix
  exact ⟨w, hwY, hw⟩

theorem normalFormAt_of_descendsTw (S : LangSetup TwistTag.E6.tag L p) (hd : S.DescendsTwE6) :
    NormalFormAt S :=
  fun X hXΓ hF δ hfix => normal_form_twE6 S hd X hXΓ hF δ hfix

end TwE6

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
