module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.PartOne.KE

section Statements


@[expose] noncomputable def e6ScToBar (K₁ : Type) [Field K₁] [Finite K₁] {L : Type} [Field L]
    (ι : K₁ →+* L) : ↥(e6Data_valid.minGroup K₁) →* ModGL Tag.E6 L :=
  (baseChangeGL ι).comp ((adjointGroup Tag.E6 K₁).subtype.comp (e6Isogeny K₁))

@[expose] def E6PlaneToralLang : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ (K₁ : Type) [Field K₁] [Finite K₁] (ι : K₁ →+* AlgebraicClosure K)
      (S : Subgroup ↥(e6Data_valid.minGroup K₁)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
    ∀ A : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)), A ≤ S.map (e6ScToBar K₁ ι) →
      (∀ x ∈ A, x ^ 3 = 1) → Nat.card A = 3 ^ 2 →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
      (∀ x ∈ A, Units.map (entrywiseHom Fr) x = x) →
      ∃ w : WeylGroup Tag.E6, ∃ g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
        Units.map (entrywiseHom Fr) g0 =
          g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w ∧
        ∀ x ∈ A, x ∈ (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
          (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom

@[expose] def TwistedE6PlaneToralLang : Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ (K₁ : Type) [Field K₁] [Finite K₁] (ι : K₁ →+* AlgebraicClosure K)
      (S : Subgroup ↥(e6Data_valid.minGroup K₁)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
    ∀ A : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)), A ≤ S.map (e6ScToBar K₁ ι) →
      (∀ x ∈ A, x ^ 3 = 1) → Nat.card A = 3 ^ 2 →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) →
      (∀ x ∈ A, twistHom TwistTag.E6 (AlgebraicClosure K) Fr x = x) →
      ∃ v : WeylGroup TwistTag.E6.tag, ∃ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v ∧
        ∀ x ∈ A, x ∈ (twistedTorusOf
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
            (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom

end Statements

theorem units_map_entrywiseHom_baseChangeGL
    {K L : Type} [Field K] [Field L]
    {τ : Tag} (ι : K →+* L) (Fr : L →+* L) (σ : K →+* K) (h : Fr.comp ι = ι.comp σ)
    (g : ModGL τ K) :
    Units.map (entrywiseHom Fr) (baseChangeGL ι g) =
      baseChangeGL ι (Units.map (entrywiseHom σ) g) := by
  rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
    CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
    CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL,
    CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, h]

section Reductions


theorem e6IsotropicToral_of_planeToralLang (h : E6PlaneToralLang) : E6IsotropicToral := by
  intro K _ _ h3 E₀ hexp hcard hab
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius _ ℓ (f : ℕ) with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, Nat.card_eq_fintype_card, hf]
  have hcomp : Fr.comp ι = ι := by
    refine RingHom.ext fun c => ?_
    change Fr (ι c) = ι c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set φ : ↥(adjointGroup Tag.E6 K) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    (baseChangeGL ι).comp (adjointGroup Tag.E6 K).subtype with hφ
  have hφinj : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hAS : E₀.map φ ≤ (E₀.comap (e6Isogeny K)).map (e6ScToBar K ι) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := e6Isogeny_surjective K x
    exact ⟨y, hx, rfl⟩
  have hexpA : ∀ x ∈ E₀.map φ, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hcardA : Nat.card (E₀.map φ) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hφinj, hcard]
  have hFix : ∀ x ∈ E₀.map φ, Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨x, -, rfl⟩
    change Units.map (entrywiseHom Fr) (baseChangeGL ι (x : ModGL Tag.E6 K)) =
      baseChangeGL ι (x : ModGL Tag.E6 K)
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  obtain ⟨w, g0, hg0C, hg0, hin⟩ :=
    h K h3 K ι (E₀.comap (e6Isogeny K)) hab (E₀.map φ) hAS hexpA hcardA Fr hFr hFix
  exact ⟨w, Fr, hFr, g0, hg0C, hg0, fun x hx => hin _ ⟨⟨x, x.2⟩, hx, rfl⟩⟩

end Reductions

section TwistedReductions


open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Simplicity in
theorem twistedE6IsotropicToral_of_planeToralLang (h : TwistedE6PlaneToralLang) :
    TwistedE6IsotropicToral := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ E₀ hexp hcard hab
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius _ ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have hcomp : Fr.comp ι = ι.comp σ.toRingHom := by
    refine RingHom.ext fun c => ?_
    change Fr (ι c) = ι (σ c)
    rw [hFr, hσ, map_pow]
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    nlinarith
  have hθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := sigma_sigma_of_card hK hσ
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hder := (CFSG.LieType.Chevalley.finite_fixed_root_group_perfect TwistTag.E6 hℓ hf K hK
    σ.toRingHom hσ').2.2.1
  set ψ : fixedGroup K σ.toRingHom →* twistedE6RootGroup K σ :=
    (MulEquiv.subgroupCongr hder).toMonoidHom.comp (twistedIsogeny σ.toRingHom hθ hK4) with hψ
  have hψsurj : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr hder).surjective.comp (twistedIsogeny_surjective σ.toRingHom hθ hK4)
  set S : Subgroup ↥(e6Data_valid.minGroup K) :=
    ((E₀.map (twistedE6RootGroup K σ).subtype).comap (e6IsogenyFixed σ.toRingHom)).map
      (fixedGroup K σ.toRingHom).subtype with hS
  have hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hab x y hx hy)
  set φ : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    (baseChangeGL ι).comp (twistedE6RootGroup K σ).subtype with hφ
  have hφinj : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hAS : E₀.map φ ≤ S.map (e6ScToBar K ι) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := hψsurj x
    exact ⟨y.1, ⟨y, ⟨ψ y, hx, rfl⟩, rfl⟩, rfl⟩
  have hexpA : ∀ x ∈ E₀.map φ, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hcardA : Nat.card (E₀.map φ) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hφinj, hcard]
  have hFix : ∀ x ∈ E₀.map φ, twistHom TwistTag.E6 (AlgebraicClosure K) Fr x = x := by
    rintro _ ⟨x, -, rfl⟩
    have hxF : twistHom TwistTag.E6 K σ.toRingHom (x : ModGL TwistTag.E6.tag K) = x :=
      ((CFSG.LieType.Chevalley.mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K
        σ.toRingHom).1 (CFSG.LieType.Chevalley.graphFixedRootGroup_le TwistTag.E6 K
          σ.toRingHom x.2)).2
    change twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (baseChangeGL ι (x : ModGL TwistTag.E6.tag K)) = baseChangeGL ι (x : ModGL _ K)
    rw [CFSG.LieType.Chevalley.twistHom_apply, units_map_entrywiseHom_baseChangeGL ι Fr
      σ.toRingHom hcomp, ← CFSG.LieType.Chevalley.baseChangeGL_diagramMap ι, ← map_inv,
      ← map_mul, ← map_mul, ← CFSG.LieType.Chevalley.twistHom_apply, hxF]
  obtain ⟨v, g0, hg0C, hg0, hin⟩ :=
    h ℓ f hℓ hℓ3 hf K hK K ι S hSab (E₀.map φ) hAS hexpA hcardA Fr hFr hFix
  exact ⟨v, Fr, hFr, g0, hg0C, hg0, fun x hx => hin _ ⟨⟨x, x.2⟩, hx, rfl⟩⟩

end TwistedReductions

end CFSG.HardMathSupport.Timmesfeld.CrossChar
