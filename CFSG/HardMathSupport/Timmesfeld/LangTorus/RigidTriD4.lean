module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTriD4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidConj
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD

set_option linter.unusedSectionVars false


section TriD4

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def LangSetup.DescendsTriD4 (S : LangSetup TwistTag.D4.tag L p) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra K L) (σ : K ≃+* K)
    (e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* S.Γ), Nat.card K = S.D.q ^ 3 ∧
      (∀ c : K, algebraMap K L (σ c) = (algebraMap K L c) ^ S.D.q) ∧
      ∀ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        (e h : ModGL TwistTag.D4.tag L) = S.D.g0⁻¹ *
          baseChangeGL (algebraMap K L) (h : ModGL TwistTag.D4.tag K) * S.D.g0

theorem LangSetup.descendsTriD4
    (S : LangSetup TwistTag.D4.tag L p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) : S.DescendsTriD4 := by
  classical
  obtain ⟨Fr, hFr, hΦ⟩ := hΦ
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hfin, hcard⟩ := ncard_pow_eq_self (L := L) r (3 * e) (by omega)
  let K : Subfield L := (iterateFrobenius L r (3 * e)).eqLocusField (RingHom.id L)
  have hset : (K : Set L) = {c : L | c ^ (r ^ (3 * e)) = c} := by
    ext c
    change iterateFrobenius L r (3 * e) c = c ↔ _
    rw [iterateFrobenius_def]
    rfl
  have hfinK : Finite K := by
    have h1 : (K : Set L).Finite := by rw [hset]; exact hfin
    exact h1.to_subtype
  have hKcard : Nat.card K = (r ^ e) ^ 3 := by
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
  have hd := langDescent_triD4 (p := p) hr he hKcard σ hσ hFr' S.D hΦ
  have hι : Function.Injective (triEmb K σ L) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  refine ⟨K, inferInstance, hfinK, inferInstance, σ, hd.mulEquiv' hι, ?_, ?_, fun h => ?_⟩
  · rw [hKcard, hq]
  · intro c
    have : (algebraMap K L) (σ c) = (algebraMap K L) (c ^ (r ^ e)) := by rw [hσ]
    rw [this, map_pow, hq]
  · exact hd.coe_mulEquiv' hι h

theorem psi_comp {t : TwistTag} (r : ℕ) [ExpChar L r] (m n : ℕ) (x : ModGL t.tag L) :
    Units.map (entrywiseHom (iterateFrobenius L r (m + n))) x =
      Units.map (entrywiseHom (iterateFrobenius L r m))
        (Units.map (entrywiseHom (iterateFrobenius L r n)) x) := by
  rw [iterateFrobenius_add, units_map_entrywiseHom_comp]

theorem psi_zero {τ : Tag} (r : ℕ) [ExpChar L r] (x : ModGL τ L) :
    Units.map (entrywiseHom (iterateFrobenius L r 0)) x = x := by
  rw [iterateFrobenius_zero]
  exact Units.ext (entrywise_id _)

@[expose] def TriCosetEmpty {τ : Tag} (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L))
    (P : ModGL τ L) : Prop :=
  ∀ c ∈ adjointGroup τ L, ∀ a : ℕ, 0 < a → a < 3 →
    ¬ ∀ x ∈ rigidTestSet S D₁, Commute (c * (P⁻¹) ^ a) x

theorem triD4_hnf {r e : ℕ} (hr : r.Prime) (K : Type) [Field K] [Finite K] [Algebra K L]
    (hK : Nat.card K = (r ^ e) ^ 3) (he : 1 ≤ e) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (r ^ e))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ (y : ModGL TwistTag.D4.tag K) (δ : K ≃+* K),
      baseChangeGL (algebraMap K L) y ∈ adjointGroup TwistTag.D4.tag L ∧
        ∀ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          (α h : ModGL TwistTag.D4.tag K) =
            y * Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.D4.tag K) * y⁻¹ := by
  have key : ∀ (hfa : ∀ (δ : K ≃+* K) (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        ((fieldActor σ δ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          ModGL TwistTag.D4.tag K) = Units.map (entrywiseHom δ.toRingHom) g),
      (∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
        α = MulAut.conj g * fieldActor σ δ) → ∃ (y : ModGL TwistTag.D4.tag K) (δ : K ≃+* K),
      baseChangeGL (algebraMap K L) y ∈ adjointGroup TwistTag.D4.tag L ∧
        ∀ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          (α h : ModGL TwistTag.D4.tag K) =
            y * Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.D4.tag K) * y⁻¹ := by
    intro hfa ⟨g, δ, hα⟩
    refine ⟨(g : ModGL TwistTag.D4.tag K), δ, ?_, fun h => ?_⟩
    · exact LieType.Chevalley.baseChangeGL_mem_adjointGroup _
        ((twistedFixedGroup_le_adjointGroup TwistTag.D4 K σ.toRingHom)
          ((graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom) g.2))
    · rw [hα]
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hfa]
  rcases hr.eq_two_or_odd' with rfl | hodd
  · obtain ⟨hfa, hex, -⟩ := even_triality_exact_automorphism_normal_form he K hK σ hσ
    obtain ⟨⟨g, δ⟩, hα, -⟩ := hex α
    exact key hfa ⟨g, δ, hα⟩
  · have hp2 : r ≠ 2 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
    obtain ⟨hfa, hex, -⟩ := odd_triality_exact_automorphism_normal_form hr hp2 he K hK σ hσ
    obtain ⟨⟨g, δ⟩, hα, -⟩ := hex α
    exact key hfa ⟨g, δ, hα⟩

theorem setupRigid_of_descends_triD4 (S : LangSetup TwistTag.D4.tag L p) (hd : S.DescendsTriD4)
    (hF : ∀ D₁ : Subgroup (ModGL TwistTag.D4.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL TwistTag.D4.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁)
    (hIg : ∀ D₁ : Subgroup (ModGL TwistTag.D4.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      TriCosetEmpty S D₁ (diagramMap TwistTag.D4 L)) : SetupRigid S := by
  classical
  obtain ⟨K, _, _, _, σ, e, hK3, hσL, he⟩ := hd
  obtain ⟨r, f, hr, hchar, hf, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hKf : Nat.card K = (r ^ f) ^ 3 := by rw [hK3, hq]
  have hσK : ∀ c : K, σ c = c ^ (r ^ f) := fun c => by
    apply (algebraMap K L).injective
    rw [hσL, map_pow, hq]
  set P : ModGL TwistTag.D4.tag L := diagramMap TwistTag.D4 L with hPdef
  have hPz : ∀ a : ℕ, ∀ x ∈ adjointGroup TwistTag.D4.tag L,
      (P⁻¹) ^ a * x * ((P⁻¹) ^ a)⁻¹ ∈ adjointGroup TwistTag.D4.tag L := by
    intro a x hx
    have h := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.D4 L (-(a : ℤ)))
      x hx
    rw [zpow_neg, zpow_natCast] at h
    rw [inv_pow]
    exact h
  have hg0C := S.D.g0_mem
  have hψP : ∀ k : ℕ, Units.map (entrywiseHom (iterateFrobenius L r k)) P = P := fun k =>
    units_map_entrywiseHom_diagramMap (iterateFrobenius L r k)
  have hσP : ∀ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.D4.tag K) =
        (diagramMap TwistTag.D4 K)⁻¹ * (h : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K := by
    intro h
    have h1 : twistHom TwistTag.D4 K σ.toRingHom (h : ModGL TwistTag.D4.tag K) = h :=
      (Subgroup.mem_inf.1 ((graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom) h.2)).2
    have h2 : diagramMap TwistTag.D4 K *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.D4.tag K) *
          (diagramMap TwistTag.D4 K)⁻¹ = h := h1
    calc Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.D4.tag K) =
        (diagramMap TwistTag.D4 K)⁻¹ * (diagramMap TwistTag.D4 K *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.D4.tag K) *
            (diagramMap TwistTag.D4 K)⁻¹) * diagramMap TwistTag.D4 K := by group
      _ = _ := by rw [h2]
  have hbase : ∀ g : ModGL TwistTag.D4.tag K,
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ.toRingHom) g) =
        Units.map (entrywiseHom (iterateFrobenius L r f)) (baseChangeGL (algebraMap K L) g) :=
    fun g => by
    have h1 : (iterateFrobenius L r f).comp (algebraMap K L) =
        (algebraMap K L).comp σ.toRingHom := RingHom.ext fun c => by
      change iterateFrobenius L r f (algebraMap K L c) = algebraMap K L (σ c)
      rw [iterateFrobenius_def, hσK, map_pow]
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h1]
  have hshift1 : ∀ x : S.Γ, Units.map (entrywiseHom (iterateFrobenius L r f))
      (x : ModGL TwistTag.D4.tag L) =
      ((Units.map (entrywiseHom (iterateFrobenius L r f)) S.D.g0)⁻¹ * P⁻¹ * S.D.g0) * x *
        ((Units.map (entrywiseHom (iterateFrobenius L r f)) S.D.g0)⁻¹ * P⁻¹ * S.D.g0)⁻¹ := by
    intro x
    obtain ⟨h, rfl⟩ := e.surjective x
    have hx := he h
    have hbcP : baseChangeGL (algebraMap K L) (diagramMap TwistTag.D4 K) = P :=
      baseChangeGL_diagramMap (algebraMap K L) TwistTag.D4
    rw [hx, map_mul, map_mul, map_inv, ← hbase, hσP, map_mul, map_mul, map_inv, hbcP]
    group
  have hshiftn : ∀ a : ℕ, ∀ x : S.Γ,
      Units.map (entrywiseHom (iterateFrobenius L r (f * a))) (x : ModGL TwistTag.D4.tag L) =
      ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ * (P⁻¹) ^ a *
        S.D.g0) * x * ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ *
          (P⁻¹) ^ a * S.D.g0)⁻¹ := by
    intro a
    induction a with
    | zero =>
      intro x
      simp only [Nat.mul_zero, psi_zero, pow_zero]
      group
    | succ a ih =>
      intro x
      have hsplit : f * (a + 1) = f * a + f := by ring
      have hψPinv : ∀ k : ℕ, Units.map (entrywiseHom (iterateFrobenius L r k)) P⁻¹ = P⁻¹ :=
        fun k => by rw [map_inv, hψP]
      have e3 : Units.map (entrywiseHom (iterateFrobenius L r (f * a)))
          (Units.map (entrywiseHom (iterateFrobenius L r f)) S.D.g0) =
          Units.map (entrywiseHom (iterateFrobenius L r (f * a + f))) S.D.g0 :=
        (psi_comp r (f * a) f S.D.g0).symm
      have hU : Units.map (entrywiseHom (iterateFrobenius L r (f * a)))
          ((Units.map (entrywiseHom (iterateFrobenius L r f)) S.D.g0)⁻¹ * P⁻¹ * S.D.g0) *
          ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ * (P⁻¹) ^ a *
            S.D.g0) = (Units.map (entrywiseHom (iterateFrobenius L r (f * a + f))) S.D.g0)⁻¹ *
              (P⁻¹) ^ (a + 1) * S.D.g0 := by
        rw [map_mul, map_mul, map_inv, e3, hψPinv, pow_succ']
        group
      rw [hsplit, psi_comp, hshift1 x, map_mul, map_mul, map_inv, ih x, ← hU]
      group
  refine setupRigid_of_conj_gen S hr (by omega : 1 ≤ f * 3) (by rw [hKf, ← pow_mul])
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) e he
    (adjointGroup TwistTag.D4.tag L : Set _)
    {w | ∃ c ∈ adjointGroup TwistTag.D4.tag L, ∃ a : ℕ, a < 3 ∧ w = c * (P⁻¹) ^ a}
    (fun α => ?_) ?_ (fun D₁ hD₁ hc w hw hwc x => ?_)
  · obtain ⟨y, δ, hyC, hy⟩ := triD4_hnf (L := L) hr K hKf hf σ hσK α
    exact ⟨y, δ, hyC, hy⟩
  · intro D₁ hD₁ hc j hj y hyC z hz hfix
    have hyC' : baseChangeGL (algebraMap K L) y ∈ adjointGroup TwistTag.D4.tag L := hyC
    have hfpos : 0 < f := hf
    obtain ⟨a, ha3, j', hj'f, hja⟩ : ∃ a, a < 3 ∧ ∃ j', j' < f ∧ j = j' + f * a :=
      ⟨j / f, by
        rw [Nat.div_lt_iff_lt_mul hfpos]
        omega, j % f, Nat.mod_lt _ hfpos, by
        rw [Nat.mod_add_div]⟩
    by_cases hj'0 : j' = 0
    · subst hj'0
      have hj' : j = f * a := by omega
      subst hj'
      refine ⟨S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * (P⁻¹) ^ a * S.D.g0,
        ⟨S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y *
          ((P⁻¹) ^ a * S.D.g0 * ((P⁻¹) ^ a)⁻¹), ?_, a, ha3, by group⟩, fun x => ?_⟩
      · exact mul_mem (mul_mem (inv_mem hg0C) hyC') (hPz a _ hg0C)
      · rw [hshiftn a x, hz]
        group
    · exfalso
      refine hF D₁ hD₁ hc r f j' hr hq (Nat.pos_of_ne_zero hj'0) hj'f
        (z * Units.map (entrywiseHom (iterateFrobenius L r j'))
          ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ * (P⁻¹) ^ a *
            S.D.g0)) ?_
      intro x hx
      have hxΓ : x ∈ S.Γ := rigidTestSet_subset_Γ S hD₁ hx
      have h1 := hfix x hx
      rw [hja] at h1
      have e1 : Units.map (entrywiseHom (iterateFrobenius L r (j' + f * a))) x =
          Units.map (entrywiseHom (iterateFrobenius L r j'))
            ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ * (P⁻¹) ^ a *
              S.D.g0) * Units.map (entrywiseHom (iterateFrobenius L r j')) x *
            (Units.map (entrywiseHom (iterateFrobenius L r j'))
              ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ * (P⁻¹) ^ a *
                S.D.g0))⁻¹ := by
        rw [psi_comp]
        have := hshiftn a ⟨x, hxΓ⟩
        simp only at this
        rw [this, map_mul, map_mul, map_inv]
      rw [e1] at h1
      calc z * Units.map (entrywiseHom (iterateFrobenius L r j'))
            ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ * (P⁻¹) ^ a *
              S.D.g0) * Units.map (entrywiseHom (iterateFrobenius L r j')) x *
              (z * Units.map (entrywiseHom (iterateFrobenius L r j'))
                ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ *
                  (P⁻¹) ^ a * S.D.g0))⁻¹ =
          z * (Units.map (entrywiseHom (iterateFrobenius L r j'))
            ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ * (P⁻¹) ^ a *
              S.D.g0) * Units.map (entrywiseHom (iterateFrobenius L r j')) x *
            (Units.map (entrywiseHom (iterateFrobenius L r j'))
              ((Units.map (entrywiseHom (iterateFrobenius L r (f * a))) S.D.g0)⁻¹ * (P⁻¹) ^ a *
                S.D.g0))⁻¹) * z⁻¹ := by group
        _ = x := h1
  · obtain ⟨c, hcC, a, ha3, rfl⟩ := hw
    by_cases ha0 : a = 0
    · subst ha0
      rw [pow_zero, mul_one] at hwc ⊢
      rw [hI D₁ hD₁ hc c hcC hwc]
      exact Commute.one_left _
    · exact absurd hwc (hIg D₁ hD₁ hc c hcC a (Nat.pos_of_ne_zero ha0) ha3)

theorem setupRigid_triD4
    (S : LangSetup TwistTag.D4.tag L p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic)
    (hF : ∀ D₁ : Subgroup (ModGL TwistTag.D4.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL TwistTag.D4.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁)
    (hIg : ∀ D₁ : Subgroup (ModGL TwistTag.D4.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      TriCosetEmpty S D₁ (diagramMap TwistTag.D4 L)) : SetupRigid S :=
  setupRigid_of_descends_triD4 S (S.descendsTriD4 hΦ hAlg) hF hI hIg

theorem setupRigid_triD4_of_big
    (S : LangSetup TwistTag.D4.tag L p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic)
    (hbig : ∀ D₁ : Subgroup (ModGL TwistTag.D4.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      HasBigInnerComponent S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL TwistTag.D4.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁)
    (hIg : ∀ D₁ : Subgroup (ModGL TwistTag.D4.tag L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      TriCosetEmpty S D₁ (diagramMap TwistTag.D4 L)) : SetupRigid S :=
  setupRigid_triD4 S hΦ hAlg
    (fun D₁ hD₁ hc => noFrobeniusInner_of_big_inner S (by decide) (Or.inr (Or.inl rfl)) hD₁ (hbig D₁ hD₁ hc))
    hI hIg

end TriD4

end CFSG.HardMathSupport.Timmesfeld.LangTorus
