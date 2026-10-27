module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtExact
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveOrbit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.RankThree.Lattice

set_option linter.unusedSectionVars false

section Setup

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def bigComponentSet (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L)) :
    Set (ModGL τ L) :=
  {x | ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ ∧ rootDiagUnit τ a ≠ 1 ∧
    ∃ i : KernelComponent (rootCharHom a),
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∧
      x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i}

@[expose] def SetupRigid (S : LangSetup τ L p) : Prop :=
  ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
    ∀ δ : MulAut ↥S.Γ, Nat.Coprime p (orderOf δ) →
      (∀ x : ↥S.Γ, (x : ModGL τ L) ∈ D₁ → δ x = x) →
      (∀ x : ↥S.Γ, (x : ModGL τ L) ∈ bigComponentSet S D₁ → δ x = x) → δ = 1

theorem frameBalanced_of_langSetup (S : LangSetup τ L p) (hrig : SetupRigid S)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc)
    (hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ)) :
    FrameBalanced p S.Γ S.E := by
  classical
  have hp := S.hp
  have : Fact p.Prime := ⟨hp⟩
  have := S.finite_Γ
  intro D₁ hD₁E hpow hcard H hH
  have hD₁p : IsPGroup p D₁ := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hpow g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hD₁p
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n
    · rw [hn, pow_zero] at hcard
      exact absurd hcard (by have := hp.one_lt; omega)
    · rw [hn, pow_one] at hcard
      exact lt_irrefl _ hcard
  obtain ⟨K₂, hK₂⟩ := Sylow.exists_subgroup_card_pow_prime p
    (show p ^ 2 ∣ Nat.card D₁ by rw [hn]; exact pow_dvd_pow p hn2)
  set D₂ : Subgroup ↥S.Γ := K₂.map D₁.subtype with hD₂
  have hD₂D₁ : D₂ ≤ D₁ := Subgroup.map_subtype_le K₂
  have hD₂c : Nat.card D₂ = p ^ 2 := by
    rw [hD₂, Subgroup.card_map_of_injective D₁.subtype_injective, hK₂]
  refine eq_bot_iff.2 ((localDeltaIn_antitone H (Subgroup.map_mono hD₂D₁)).trans
    (le_of_eq ?_))
  set D₂' : Subgroup (ModGL τ L) := D₂.map S.Γ.subtype with hD₂'
  have hD₂'E : D₂' ≤ S.E := by
    rintro _ ⟨x, hx, rfl⟩
    exact hD₁E x (hD₂D₁ hx)
  have hD₂'c : Nat.card D₂' = p ^ 2 := by
    rw [hD₂', Subgroup.card_map_of_injective S.Γ.subtype_injective, hD₂c]
  have hD₂ne : D₂ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hD₂c
    have h1 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  refine localDeltaIn_eq_bot_of_inner_components_rigid_ambient (A := S.Γ)
    (S := bigComponentSet S D₂') hp hinj hH hD₂ne
    (fun δ _ hδ hfixD hfixX => hrig D₂' hD₂'E hD₂'c δ hδ (fun x hx => ?_) hfixX) ?_
  · obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hfixD y hy
  rintro x ⟨a, ha, ha1, i, hbig, hx⟩
  obtain ⟨d, hd, hda⟩ := ha
  have hdE : rootDiagUnit τ a ∈ S.E := hda ▸ hD₂'E ⟨d, hd, rfl⟩
  obtain ⟨hLC, hLsn⟩ := hsub τ L p S a hdE ha1 i
  refine ⟨d, hd, fun h1 => ha1 (by rw [← hda, h1]; rfl),
    rationalComponent S.ρ S.Γ (rootCharHom a) i, hx, ?_, ?_, ?_, hbig⟩
  · rw [← hda] at hLC
    exact hLC
  · cases hkind : twistKind S.ρ (rootCharHom a) i
    · exact hin τ L p S a hdE ha1 i hkind hbig
    · exact hsu τ L p S a hdE ha1 i hkind hbig
    · exact htw τ L p S a hdE ha1 i hkind hbig
    · exact hex τ L p S a hdE ha1 i hkind hbig
  · rw [← hda] at hLsn
    exact hLsn

end Setup

section Perfect

theorem commutator_adjointGroup_F4_eq_top
    (K : Type) [Field K] :
    commutator ↥(adjointGroup .F4 K) = ⊤ :=
  (CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 K).commutator_eq_top

theorem commutator_adjointGroup_E6_eq_top
    (K : Type) [Field K] [Finite K] :
    commutator ↥(adjointGroup .E6 K) = ⊤ :=
  (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K).1.commutator_eq_top

theorem commutator_adjointGroup_E7_eq_top
    (K : Type) [Field K] [Finite K] :
    commutator ↥(adjointGroup .E7 K) = ⊤ :=
  (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1.commutator_eq_top

theorem commutator_adjointGroup_E8_eq_top
    (K : Type) [Field K] :
    commutator ↥(adjointGroup .E8 K) = ⊤ :=
  (CFSG.LieType.Steinberg.Adjoint.isPerfect_e8 K).commutator_eq_top

end Perfect

theorem langTorusPlaneBalance_of_setupRigidAt {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hperf : ∀ (K : Type) [Field K] [Finite K], commutator ↥(adjointGroup τ K) = ⊤)
    (w : WeylGroup τ) {p : ℕ} (hp : p.Prime) {Q : ℕ → Prop}
    (hQ : ∀ q, 2 ≤ q → Q q → ¬ p ∣ q ∧ (5 ≤ p ∨ 4 ≤ q))
    (hrig : ∀ (K : Type) [Field K] [Finite K] (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL τ (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
      (S : LangSetup τ (AlgebraicClosure K) p),
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 → Q (Nat.card K) →
        SetupRigid S)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) : LangTorusPlaneBalance τ w p Q := by
  classical
  intro K _ _ hQK Fr hFr g0 hg0C hg0 D₀ hpow hcard htor H hH
  obtain ⟨hpq, hq⟩ := hQ _ Finite.one_lt_card hQK
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  let D : LangDatum τ (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  have hd : LangDescent D 7
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype) := by
    rcases hτ with h | h | h | h
    · exact langDescent_exact (Or.inr h) hFr D rfl (hperf K)
    · exact langDescent_untw 3 (Or.inl ⟨h, rfl⟩) hFr D rfl Nat.prime_seven (by norm_num)
        (hperf K)
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h, rfl⟩)) hFr D rfl Nat.prime_seven
        (by norm_num) (hperf K)
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h, rfl⟩)) hFr D rfl Nat.prime_seven
        (by norm_num) (hperf K)
  have hΓ : D.Γ = langModel τ K (AlgebraicClosure K) g0 := by
    rw [hd.Γ_eq, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ (AlgebraicClosure K) D
  have hK0 : ((Nat.card K : ℕ) : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), Nat.card_eq_fintype_card,
      FiniteField.cast_card_eq_zero K, map_zero]
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 :=
    ⟨by
      rw [show D.q = Fintype.card K from Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card K, hK0⟩
  let S : LangSetup τ (AlgebraicClosure K) p :=
    D.toSetup p ρ hρ hp hq hqpow hpq hd.finite_model
  have hinj : Function.Injective (MulAut.conj : ↥D.Γ →* MulAut ↥D.Γ) := by
    rw [hΓ]
    exact conj_injective_of_mulEquiv (langModelMulEquiv τ K (AlgebraicClosure K) g0).symm
      (mulAut_conj_injective_adjointGroup (τ := τ) (K := K))
  have hbal : FrameBalanced p D.Γ (D.torsion p) :=
    frameBalanced_of_langSetup S (hrig K Fr hFr g0 hg0C hg0 S rfl hQK) hsub hin hsu htw hex hinj
  rw [hΓ] at hbal
  refine localDeltaIn_eq_bot_of_frameBalanced_mulEquiv hbal
    (langModelMulEquiv τ K (AlgebraicClosure K) g0) D₀ hpow hcard (fun x hx => ?_) hH
  refine (LangDatum.mem_torsion D).2 ⟨⟨?_, by rw [hΓ]; exact (langModelMulEquiv τ K _ g0 x).2⟩, ?_⟩
  · obtain ⟨y, hy, hyx⟩ := htor x hx
    rw [coe_langModelMulEquiv]
    change g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0⁻¹⁻¹ ∈ _
    rw [← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g0⁻¹ * (g0 * y * g0⁻¹) * g0⁻¹⁻¹ = y by group]
    exact hy
  · rw [← Subgroup.coe_pow, ← map_pow, hpow x hx, map_one, Subgroup.coe_one]

theorem twistedE6LangTorusPlaneBalance_of_setupRigidAt (v : WeylGroup TwistTag.E6.tag) {p : ℕ}
    (hp : p.Prime) {Q : ℕ → Prop} (hQ : ∀ q, 2 ≤ q → Q q → ¬ p ∣ q ∧ (5 ≤ p ∨ 4 ≤ q))
    (hrig : ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f → Q (ℓ ^ f) → ∀ (K : Type) [Field K],
      Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
      ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
        (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
        (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
        (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
        (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p),
        S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0 → SetupRigid S)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) : TwistedE6LangTorusPlaneBalance v p Q := by
  classical
  intro ℓ f hℓ hf hQq K _ hK σ hσ Fr hFr g0 hg0C hg0 D₀ hpow hcard htor H hH
  obtain ⟨hpq, hq⟩ := hQ _ (Nat.one_lt_pow (by omega) hℓ.one_lt) hQq
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
  let D : LangDatum TwistTag.E6.tag (AlgebraicClosure K) :=
    LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0
  have hΦ : D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr := rfl
  have hfin := finite_model_twistedE6 hℓ hf hK hσ hFr D hΦ
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag (AlgebraicClosure K) D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 := by
    refine ⟨hℓ.isPrimePow.pow (by omega), ?_⟩
    change ((ℓ ^ f : ℕ) : AlgebraicClosure K) = 0
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  let S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p :=
    D.toSetup p ρ hρ hp hq hqpow hpq hfin
  have hC : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)
  have hinj : Function.Injective (MulAut.conj : ↥D.Γ →* MulAut ↥D.Γ) :=
    conj_injective_of_mulEquiv (twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ).symm hC
  have hbal : FrameBalanced p D.Γ (D.torsion p) :=
    frameBalanced_of_langSetup S (hrig ℓ f hℓ hf hQq K hK σ hσ Fr hFr g0 hg0C hg0 S rfl) hsub hin
      hsu htw hex hinj
  refine localDeltaIn_eq_bot_of_frameBalanced_mulEquiv hbal
    (twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ) D₀ hpow hcard (fun x hx => ?_) hH
  refine (LangDatum.mem_torsion D).2 ⟨⟨?_, (twistedE6EquivΓ hℓ hf hK hσ hFr D hΦ x).2⟩, ?_⟩
  · obtain ⟨y, hy, hyx⟩ := htor x hx
    rw [coe_twistedE6EquivΓ]
    change g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 ∈ _
    rw [← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y by group]
    exact hy
  · rw [← Subgroup.coe_pow, ← map_pow, hpow x hx, map_one, Subgroup.coe_one]

@[expose] def SetupRigidAtFrobenius (τ : Tag) (w : WeylGroup τ) (p : ℕ) (Q : ℕ → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL τ (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (S : LangSetup τ (AlgebraicClosure K) p),
    S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 → Q (Nat.card K) →
      SetupRigid S

@[expose] def SetupRigidAtTwistedE6 (v : WeylGroup TwistTag.E6.tag) (p : ℕ) (Q : ℕ → Prop) :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f → Q (ℓ ^ f) → ∀ (K : Type) [Field K],
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
      (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
      (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p),
      S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0 → SetupRigid S

section FrontierRigidAt

theorem langTorusPlaneBalance_E6_two_five_of_setupRigidAt
    (hrig : SetupRigidAtFrobenius Tag.E6 e6PhiTwoWeyl 5 fun q => 5 ∣ q + 1)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) :
    LangTorusPlaneBalance Tag.E6 e6PhiTwoWeyl 5 fun q => 5 ∣ q + 1 :=
  langTorusPlaneBalance_of_setupRigidAt (Or.inr (Or.inl rfl))
    (fun K _ _ => commutator_adjointGroup_E6_eq_top K) e6PhiTwoWeyl Nat.prime_five
    (fun q _ (hq : 5 ∣ q + 1) => ⟨by omega, Or.inl le_rfl⟩) hrig hsub hin hsu htw hex

theorem twistedE6LangTorusPlaneBalance_one_five_of_setupRigidAt
    (hrig : SetupRigidAtTwistedE6 twE6PhiOneWeyl 5 fun q => 5 ∣ q - 1)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) :
    TwistedE6LangTorusPlaneBalance twE6PhiOneWeyl 5 fun q => 5 ∣ q - 1 :=
  twistedE6LangTorusPlaneBalance_of_setupRigidAt twE6PhiOneWeyl Nat.prime_five
    (fun q hq2 (hq : 5 ∣ q - 1) => ⟨by omega, Or.inl le_rfl⟩) hrig hsub hin hsu htw hex

end FrontierRigidAt

end CFSG.HardMathSupport.Timmesfeld.CrossChar
