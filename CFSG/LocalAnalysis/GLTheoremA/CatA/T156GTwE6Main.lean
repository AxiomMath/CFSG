module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GTwE6Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.RecipeExcLang

@[expose] def TwE6FixOn (K : Type) [Field K] (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop)
    (n p : ℕ) : Prop :=
  ∀ H : Subgroup (MarkChev.GLS S K),
    H = MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n →
    ∀ f ∈ RecipeFieldExcInn.markFieldImage S K H, orderOf f = p →
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = (2 ^ (n / p)) ^ 2 ∧
        ∀ H₀ : Subgroup (MarkChev.GLS S k),
          H₀ = MarkChev.twistedH TwistTag.E6.tag.cartan S k TwistTag.E6.perm (n / p) →
            IsSimpleGroup (LargeEvenCenterQuot H₀) ∧
              (∃ a b : LargeEvenCenterQuot H₀, a * b ≠ b * a) ∧
              ∃ θ₀ : ggFixDer f ≃* LargeEvenCenterQuot H₀,
                GGFixGeom (markIDImage S K H) f (markIDImage S k H₀) θ₀

theorem TwE6FixOn.of_eq {K : Type} [Field K] {S S' : (Fin TwistTag.E6.tag.rank → ℤ) → Prop}
    {n p : ℕ} (hS : S = S') (h : TwE6FixOn K S n p) : TwE6FixOn K S' n p :=
  hS ▸ h

section Core


theorem twE6FixOn_isRoot {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    TwE6FixOn K (IsRoot TwistTag.E6.tag) n p := by
  intro H hH f hf hord
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card]; exact hK2)
  set σ : K ≃+* K := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hperf, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hH' : H = graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    hH.trans ((twistedH_eq_commutator K TwistTag.E6 n σ.toRingHom hσ).trans hperf)
  subst hH'
  obtain ⟨hpn, κ, σ₀, hk, hσ₀, hs, hna, θ₀, hθ₀⟩ := twE6_fixGeom_model hn hK σ hσ hp hp2 hf hord
  refine ⟨fixSubfield κ, inferInstance, inferInstance, hk, fun H₀ hH₀ => ?_⟩
  have hd1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hperf₀, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hd1
      (fixSubfield κ) hk σ₀ hσ₀
  have hH₀' : H₀ = graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom :=
    hH₀.trans ((twistedH_eq_commutator (fixSubfield κ) TwistTag.E6 (n / p) σ₀.toRingHom
      hσ₀).trans hperf₀)
  subst hH₀'
  exact ⟨hs, hna, θ₀, hθ₀⟩

theorem twE6_fixStd {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {f : MulAut (LargeEvenCenterQuot
      (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))}
    (hf : f ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
      (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
    (hord : orderOf f = p) :
    LargeEvenRecipeTwisted TwistTag.E6.tag.cartan TwistTag.E6.perm 2 (n / p) fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
          (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) f I₀ θ₀ := by
  have h := (twE6FixOn_isRoot hn hK hp hp2).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  obtain ⟨k, _, _, hk, hconcl⟩ :=
    h (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)
      (largeEvenTwistedH_eq _ K _ n) f hf hord
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  obtain ⟨hs, hna, θ₀, hg⟩ :=
    hconcl (LargeEvenTwistedH TwistTag.E6.tag.cartan k TwistTag.E6.perm (n / p))
      (largeEvenTwistedH_eq _ k _ (n / p))
  refine ⟨hs, hna, θ₀, ?_⟩
  rw [largeEvenChevIDImage_eq, largeEvenChevIDImage_eq]
  exact hg

variable {p : ℕ}

theorem geomBody_twE6 (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    GeomBody p ⟨.twE6, 0, n⟩
      (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) := by
  refine geomBody_of_field (by simp) fun _ _ f hf hord => ?_
  have h := twE6_fixStd hn hK hp hp2 hf hord
  obtain ⟨K₀, _, _, hK₀, -⟩ := h
  have hK₀' : Nat.card K₀ = 2 ^ (n / p * 2) := by rw [hK₀, ← pow_mul]
  have h1 := one_le_of_card_field hK₀'
  have hlab₀ : LargeEvenInLambda2 ⟨.twE6, 0, n / p⟩ := ⟨show 1 ≤ n / p by omega, rfl⟩
  exact fixAlt_of_raw hlab₀ (twE6_fixStd hn hK hp hp2 hf hord)

theorem cAll_geomBody_twE6 (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    MI.CAll ⟨.twE6, 0, n⟩ (GeomBody p ⟨.twE6, 0, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  exact recipeTwisted_and (fun K _ _ hK => geomBody_twE6 hp hp2 hn K hK) hQ

end Core

@[expose] def RestLabel₆ (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∧ p = 3 ∧ Even lab.n) ∨ (lab.tag = .triD4 ∧ p = 3)

@[expose] def T156Rest₆ : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → RestLabel₆ p lab →
    MI.CAll lab (GeomBody p lab)

section Core


theorem t156Rest₅_of_rest₆ (h : T156Rest₆) : T156Rest₅ := by
  intro p hp hp2 lab hlab hr
  unfold RestLabel₅ at hr
  rcases hr with h1 | h1 | h1
  · exact h p hp hp2 lab hlab (Or.inl h1)
  · exact h p hp hp2 lab hlab (Or.inr h1)
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at h1
    subst h1
    have hl : l = 0 := hlab.2
    subst hl
    exact cAll_geomBody_twE6 hp hp2 hlab.1

theorem t156FactOmega_of_rest₆ (h : T156Rest₆) (p : ℕ) : T156FactOmega p :=
  t156FactOmega_of_rest₅ (t156Rest₅_of_rest₆ h) p

end Core

end CFSG.LocalAnalysis.GLTheoremA.T156

end
