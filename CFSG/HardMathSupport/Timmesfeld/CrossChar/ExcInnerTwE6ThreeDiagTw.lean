module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwAutBalance
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTest

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

section Conj

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}


theorem rigid_of_conj_testSet (S : LangSetup τ L p) {K : Type} [Field K] [Finite K]
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
    (hI : ∀ w ∈ Ycl, (∀ x ∈ X, Commute w x) → ∀ x : S.Γ, Commute w (x : ModGL τ L))
    (δ : MulAut S.Γ) (hfixX : ∀ x : S.Γ, (x : ModGL τ L) ∈ X → δ x = x) : δ = 1 := by
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
  have hwc : ∀ x ∈ X, Commute w x := by
    intro x hx
    have h2 : w * x * w⁻¹ = x := by
      rw [← hw ⟨x, hXΓ hx⟩]
      exact hfix x hx
    show w * x = x * w
    calc w * (x : ModGL τ L) = w * x * w⁻¹ * w := by group
      _ = x * w := by rw [h2]
  have hwΓ := hI w hwY hwc
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hδx, hw x, MulAut.one_apply]
  have := (hwΓ x).eq
  calc w * (x : ModGL τ L) * w⁻¹ = x * w * w⁻¹ := by rw [this]
    _ = x := by group

end Conj

section TwE6

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}


theorem rigid_twistedE6_of_testSet (S : LangSetup TwistTag.E6.tag L p) (hd : S.DescendsTwE6)
    (X : Set (ModGL TwistTag.E6.tag L)) (hXΓ : X ⊆ S.Γ)
    (hF : ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL TwistTag.E6.tag L,
        ¬ ∀ x ∈ X, z * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z⁻¹ = x)
    (hI : ∀ z ∈ adjointGroup TwistTag.E6.tag L, (∀ x ∈ X, Commute z x) →
      ∀ x : S.Γ, Commute z (x : ModGL TwistTag.E6.tag L))
    (hIg : ∀ w ∈ adjointGroup TwistTag.E6.tag L,
      ¬ ∀ x ∈ X, Commute (w * diagramMap TwistTag.E6 L) x)
    (δ : MulAut S.Γ) (hfix : ∀ x : S.Γ, (x : ModGL TwistTag.E6.tag L) ∈ X → δ x = x) :
    δ = 1 := by
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
  refine rigid_of_conj_testSet S hr (by omega : 1 ≤ f * 2) (by rw [hKf, ← pow_mul])
    (twistedE6RootGroup K σ) e he (adjointGroup TwistTag.E6.tag L : Set _)
    {w | w ∈ adjointGroup TwistTag.E6.tag L ∨
      ∃ c ∈ adjointGroup TwistTag.E6.tag L, w = c * P}
    (fun α => ?_) X hXΓ ?_ (fun w hw hwc x => ?_) δ hfix
  · obtain ⟨y, δ', hyC, hy⟩ := twE6_hnf (L := L) hr K hKf hf σ hσK α
    exact ⟨y, δ', hyC, hy⟩
  · intro j hj y hyC z hz hfix'
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
  · rcases hw with hw | ⟨c, hcC, rfl⟩
    · exact hI w hw hwc x
    · exact absurd hwc (hIg c hcC)

end TwE6

section TwBalance


theorem twistedE6Three_rigid_of_torus (hAK : AnyKindCommuteT) (hbig : ThreeBigComponents)
    {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (S : LangSetup TwistTag.E6.tag L 3) (hd : S.DescendsTwE6)
    (hq4 : 4 ≤ S.D.q) {D : Subgroup (ModGL TwistTag.E6.tag L)} [Finite D] (hDT : D ≤ S.D.torus)
    (hpow : ∀ x ∈ D, x ^ 3 = 1) (hcard : 3 < Nat.card D) (δ : MulAut S.Γ)
    (hfix : ∀ x : S.Γ, (x : ModGL TwistTag.E6.tag L) ∈ bigComponentSet S D → δ x = x) :
    δ = 1 := by
  have hΓC : ∀ x : S.Γ, (x : ModGL TwistTag.E6.tag L) ∈ adjointGroup TwistTag.E6.tag L :=
    fun x => (S.Γ_le_model x.2).1
  refine rigid_twistedE6_of_testSet S hd (bigComponentSet S D) (bigComponentSet_subset_Γ S D)
    (fun r f j _ hr hqf hj0 hjf z => noFrobenius_testSet_of_torus hbig S (by decide) hq4
      (Or.inr (Or.inr (Or.inl rfl))) hDT hpow hcard r f j hr hqf hj0 hjf z)
    (fun z _ hzc x => commute_adjointGroup_of_torus hAK hbig S (by decide) hq4 hDT hpow hcard
      hzc _ (hΓC x))
    (fun w hw hcomm => not_forall_commute_mul_diagramMap_E6 (K := K) hw
      (commute_adjointGroup_of_torus hAK hbig S (by decide) hq4 hDT hpow hcard hcomm)) δ hfix

theorem twistedE6Three_langTorusPlaneBalanceInndiag (hsub : LangSubnormalT)
    (hin : LangComponentsQuasisimpleT .inner) (hsu : LangComponentsQuasisimpleT .suN)
    (htw : LangComponentsQuasisimpleT .twoD) (hex : LangComponentsQuasisimpleT .exc)
    (hAK : AnyKindCommuteT) (hbig : ThreeBigComponents) (v : WeylGroup TwistTag.E6.tag) :
    TwistedE6LangTorusPlaneBalanceInndiag v 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2 := by
  classical
  intro ℓ f hℓ hf hQq K _ hK σ hσ Fr hFr g0 hg0C hg0 D₀ hpow hcard htor H hH
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hιdef
  have hq4 : 4 ≤ ℓ ^ f := four_le_of_not_three_dvd
    (le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)) hQq.1 hQq.2
  let D : LangDatum TwistTag.E6.tag L := LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0
  have hΦ : D.Φ = twistHom TwistTag.E6 L Fr := rfl
  have hfin := finite_model_twistedE6 hℓ hf hK hσ hFr D hΦ
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag L D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    refine ⟨hℓ.isPrimePow.pow (by omega), ?_⟩
    change ((ℓ ^ f : ℕ) : L) = 0
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  let S : LangSetup TwistTag.E6.tag L 3 :=
    D.toSetup 3 ρ hρ Nat.prime_three (Or.inr hq4) hqpow hQq.1 hfin
  have hSq : S.D.q = ℓ ^ f := rfl
  set φ : twistedE6RootGroup K σ ≃* S.Γ := twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ with hφdef
  have hφ : ∀ h : twistedE6RootGroup K σ, ((φ h : S.Γ) : ModGL TwistTag.E6.tag L) =
      g0⁻¹ * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * g0 :=
    fun h => coe_twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ h
  have hdesc : S.DescendsTwE6 := ⟨K, inferInstance, inferInstance, inferInstance, σ, φ, hK,
    fun c => by rw [hσ, map_pow, hSq], hφ⟩
  set θ : ↥(twistedE6InndiagGL K σ) →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL ι).comp (twistedE6InndiagGL K σ).subtype)
    with hθdef
  have hθ : ∀ x : ↥(twistedE6InndiagGL K σ),
      θ x = g0⁻¹ * baseChangeGL ι (x : ModGL TwistTag.E6.tag K) * g0 := fun x => by
    change (MulAut.conj g0⁻¹) (baseChangeGL ι (x : ModGL TwistTag.E6.tag K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hθinj : Function.Injective θ :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective ι).comp Subtype.val_injective)
  set D' : Subgroup (ModGL TwistTag.E6.tag L) := D₀.map θ with hD'def
  have hD₀fin : Finite D₀ := Nat.finite_of_card_ne_zero (by omega)
  have hD'fin : Finite D' := Finite.of_surjective (fun x : D₀ => (⟨θ x, x, x.2, rfl⟩ : D'))
    (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  have hD'T : D' ≤ S.D.torus := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := htor x hx
    rw [hθ, ← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y by group]
    exact hy
  have hD'pow : ∀ x ∈ D', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hD'card : 3 < Nat.card D' := by
    rw [hD'def, Subgroup.card_map_of_injective hθinj]
    exact hcard
  set ψ : MulAut (twistedE6RootGroup K σ) ≃* MulAut S.Γ := MulAut.congr φ with hψdef
  have hψc : ∀ (x : ↥(twistedE6InndiagGL K σ)) (y : S.Γ),
      ((ψ (twistedE6InndiagConj K σ x) y : S.Γ) : ModGL TwistTag.E6.tag L) =
        θ x * y * (θ x)⁻¹ := by
    intro x y
    obtain ⟨h, rfl⟩ := φ.surjective y
    change ((φ (twistedE6InndiagConj K σ x (φ.symm (φ h))) : S.Γ) :
      ModGL TwistTag.E6.tag L) = _
    rw [MulEquiv.symm_apply_apply, hφ, hφ, twistedE6InndiagConj_apply, map_mul, map_mul, map_inv,
      hθ]
    group
  have hψconj : ∀ g : twistedE6RootGroup K σ, ψ (MulAut.conj g) = MulAut.conj (φ g) :=
    fun g => by
      ext z
      simp [hψdef, MulAut.congr_apply, MulAut.conj_apply]
  have hC : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)
  have hinj : Function.Injective (MulAut.conj : S.Γ →* MulAut S.Γ) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv φ.symm hC
  have := S.finite_Γ
  have hcinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hH' : innerAut S.Γ ≤ H.map ψ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (φ.symm y), hH ⟨φ.symm y, rfl⟩, ?_⟩
    change ψ (MulAut.conj (φ.symm y)) = MulAut.conj y
    rw [hψconj, MulEquiv.apply_symm_apply]
  have hE' : (D₀.map (twistedE6InndiagConj K σ)).map ψ.toMonoidHom ≠ ⊥ := by
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ D₀, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 hcon
      rw [hbot, Subgroup.card_bot] at hcard
      omega
    intro hbot
    have hmem : ψ (twistedE6InndiagConj K σ x) ∈
        (D₀.map (twistedE6InndiagConj K σ)).map ψ.toMonoidHom := ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← map_one ψ] at hmem
    exact hx1 (hcinj (ψ.injective hmem |>.trans (map_one _).symm))
  have key : localDeltaIn 3 (H.map ψ.toMonoidHom)
      ((D₀.map (twistedE6InndiagConj K σ)).map ψ.toMonoidHom) = ⊥ := by
    refine localDeltaIn_eq_bot_of_aut_components_rigid Nat.prime_three hinj hH' hE'
      (S := {s : S.Γ | (s : ModGL TwistTag.E6.tag L) ∈ bigComponentSet S D'})
      (fun δ _ _ hδ => twistedE6Three_rigid_of_torus (K := K) hAK hbig S hdesc
        (by rw [hSq]; exact hq4) hD'T hD'pow hD'card δ hδ) ?_
    rintro s ⟨a, haD, ha1, i, hbig', hsR⟩
    obtain ⟨x, hx, hxa⟩ := haD
    have hT : rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus := hD'T ⟨x, hx, hxa⟩
    have hTp : rootDiagUnit TwistTag.E6.tag a ^ 3 = 1 := hD'pow _ ⟨x, hx, hxa⟩
    obtain ⟨hRC, hRsn⟩ := hsub TwistTag.E6.tag L 3 S a hT hTp ha1 i
    set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hRdef
    have hRΓ : R ≤ S.Γ := hRC.trans inf_le_left
    have hfixe : fixSub (ψ (twistedE6InndiagConj K σ x)) =
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit TwistTag.E6.tag a}).subgroupOf S.Γ := by
      ext y
      rw [mem_fixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hy
        refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have h1 := congrArg Subtype.val hy
        rw [hψc, hxa] at h1
        calc (y : ModGL TwistTag.E6.tag L) * rootDiagUnit TwistTag.E6.tag a =
            (rootDiagUnit TwistTag.E6.tag a * y * (rootDiagUnit TwistTag.E6.tag a)⁻¹) *
              rootDiagUnit TwistTag.E6.tag a := by rw [h1]
          _ = rootDiagUnit TwistTag.E6.tag a * y := by group
      · rintro ⟨-, hy⟩
        apply Subtype.ext
        rw [hψc, hxa]
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hy
        calc rootDiagUnit TwistTag.E6.tag a * (y : ModGL TwistTag.E6.tag L) *
              (rootDiagUnit TwistTag.E6.tag a)⁻¹ =
            y * rootDiagUnit TwistTag.E6.tag a * (rootDiagUnit TwistTag.E6.tag a)⁻¹ := by
              rw [h1]
          _ = y := by group
    refine ⟨ψ (twistedE6InndiagConj K σ x), ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_, R.subgroupOf S.Γ, hsR,
      ?_, ?_, ?_, ?_⟩
    · intro h1
      apply ha1
      rw [← hxa, ← map_one θ]
      congr 1
      exact hcinj ((ψ.injective (h1.trans (map_one ψ).symm)).trans (map_one _).symm)
    · intro y hy
      rw [hfixe, Subgroup.mem_subgroupOf]
      exact hRC hy
    · have hq : CFSG.IsQuasisimple R := by
        cases hkind : twistKind S.ρ (rootCharHom a) i
        · exact hin TwistTag.E6.tag L 3 S a hT hTp ha1 i hkind hbig'
        · exact hsu TwistTag.E6.tag L 3 S a hT hTp ha1 i hkind hbig'
        · exact htw TwistTag.E6.tag L 3 S a hT hTp ha1 i hkind hbig'
        · exact hex TwistTag.E6.tag L 3 S a hT hTp ha1 i hkind hbig'
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRΓ).symm hq
    · rw [hfixe]
      exact isSubnormal_subgroupOf_subgroupOf inf_le_left hRsn
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRΓ).toEquiv]
  have hle := Coordinator.map_localDeltaIn_le 3 ψ.toMonoidHom ψ.injective H
    (D₀.map (twistedE6InndiagConj K σ))
  rw [key, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ ψ.injective] at hle
  exact hle

end TwBalance

end CFSG.HardMathSupport.Timmesfeld.CrossChar
