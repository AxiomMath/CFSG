module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Two
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Minuscule

set_option linter.unusedSectionVars false


abbrev twBase (K : Type) [Field K] (σ : K ≃+* K) (E₀ : Subgroup (twistedE6RootGroup K σ)) :
    Subgroup (ModGL Tag.E6 (AlgebraicClosure K)) :=
  E₀.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (twistedE6RootGroup K σ).subtype)

@[expose] def TwIsoLift (K : Type) [Field K] (σ : K ≃+* K) (E₀ : Subgroup (twistedE6RootGroup K σ)) : Prop :=
  ∃ (K₁ : Type) (_ : Field K₁) (_ : Finite K₁) (ι : K₁ →+* AlgebraicClosure K)
    (S : Subgroup ↥(e6Data_valid.minGroup K₁)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
      twBase K σ E₀ ≤ S.map (CFSG.HardMathSupport.Timmesfeld.CrossChar.e6ScToBar K₁ ι)

@[expose] def TwKills (K : Type) [Field K] (σ : K ≃+* K) (E₀ : Subgroup (twistedE6RootGroup K σ))
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (α : Fin TwistTag.E6.tag.rank → ℤ) : Prop :=
  ∀ x ∈ E₀, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
    rootDiagUnit TwistTag.E6.tag a =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g0 ∧
      rootChar a α = 1

theorem twistedE6RootGroup_fix (K : Type) [Field K] (σ : K ≃+* K) (x : ModGL TwistTag.E6.tag K)
    (hx : x ∈ twistedE6RootGroup K σ) : twistHom TwistTag.E6 K σ.toRingHom x = x := by
  have hle : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤
      MonoidHom.eqLocus (twistHom TwistTag.E6 K σ.toRingHom) (MonoidHom.id _) := by
    refine sup_le ?_ ?_
    · exact inf_le_right.trans inf_le_right
    · exact inf_le_right.trans inf_le_right
  have h : twistHom TwistTag.E6 K σ.toRingHom x = MonoidHom.id _ x := hle hx
  simpa using h

theorem twBase_twistHom_fix (K : Type) [Field K] (σ : K ≃+* K) (q : ℕ)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hσ : ∀ c : K, σ c = c ^ q)
    (hFr : ∀ c, Fr c = c ^ q)
    (x : ModGL TwistTag.E6.tag K) (hx : x ∈ twistedE6RootGroup K σ) :
    twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) x) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) x := by
  have hcomp : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
      Fr.comp (algebraMap K (AlgebraicClosure K)) := by
    ext c
    simp [hσ, hFr, map_pow]
  rw [twistHom_baseChangeGL (algebraMap K (AlgebraicClosure K)) hcomp x,
    twistedE6RootGroup_fix K σ x hx]

theorem exists_pow_ringChar_of_card_sq (K : Type) [Field K] [Finite K] (q : ℕ)
    (hK : Nat.card K = q ^ 2)
    (hq : 2 ≤ q) : Nat.Prime (ringChar K) ∧ ∃ f : ℕ, 1 ≤ f ∧ q = ringChar K ^ f := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨m, -, hqm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  refine ⟨hp, m, ?_, hqm⟩
  by_contra h0
  have hm0 : m = 0 := by omega
  rw [hm0, pow_zero] at hqm
  omega

@[expose] def TwHighIsotropic_two : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = q ^ 2 →
    (∀ c : K, σ c = c ^ q) → q % 3 = 2 → 3 ≤ q →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRIn (ringChar K) E₀ → TwIsoLift K σ E₀

@[expose] def TwHighKillNR_two : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = q ^ 2 →
    (∀ c : K, σ c = c ^ q) →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K), (∀ c, Fr c = c ^ q) →
      ∀ (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)),
        g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
        (∀ x ∈ E₀, baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
            (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom) →
        ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → TwKills K σ E₀ g0 α →
          NormalizesRIn (ringChar K) E₀

@[expose] def TwHighRegularContained_two : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (k : Type) [Field k] [Finite k]
    [Algebra k K]
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c),
    Nat.card K = q ^ 2 → (∀ c : K, σ c = c ^ q) → Nat.card k = q → q % 3 = 2 → 3 ≤ q →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRIn (ringChar K) E₀ →
      ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K), (∀ c, Fr c = c ^ q) →
      ∀ (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)),
        g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
        (∀ x ∈ E₀, baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
            (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom) →
        (∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → ¬ TwKills K σ E₀ g0 α) →
        ∃ g : twistedE6RootGroup K σ,
          E₀.map (MulAut.conj g).toMonoidHom ≤
            ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range

theorem twHighPlaneContained_two_of_pieces (hI : TwHighIsotropic_two) (hN : TwHighKillNR_two)
    (hH : TwHighRegularContained_two) : TwHighPlaneContained_two := by
  intro q K _ _ σ k _ _ _ hfix hK hσ hkq hq hq3 E₀ hexp hcard hn
  obtain ⟨hp, f, hf, rfl⟩ := exists_pow_ringChar_of_card_sq K q hK (by omega)
  have hℓ3 : ringChar K ≠ 3 := by
    intro h
    rw [h] at hq
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  obtain ⟨K₁, _, _, ι₁, S, hS, hAS⟩ := hI (ringChar K ^ f) K σ hK hσ hq hq3 E₀ hexp hcard hn
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  haveI : ExpChar (AlgebraicClosure K) (ringChar K) := ExpChar.prime hp
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K :=
    iterateFrobenius (AlgebraicClosure K) (ringChar K) f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ringChar K ^ f) := fun c => by
    rw [hFrdef, iterateFrobenius_def]
  have hFix : ∀ y ∈ twBase K σ E₀,
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr y = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact twBase_twistHom_fix K σ (ringChar K ^ f) Fr hσ hFr x.1 x.2
  have hA_exp : ∀ y ∈ twBase K σ E₀, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hexp x hx, map_one]
  have hA_card : Nat.card (twBase K σ E₀) = 3 ^ 2 := by
    have hinj : Function.Injective
        ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (twistedE6RootGroup K σ).subtype) :=
      (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp Subtype.val_injective
    have hc : Nat.card (twBase K σ E₀) = Nat.card E₀ := Subgroup.card_map_of_injective hinj
    rw [hc, hcard]
  obtain ⟨v, g0, hg0, hF, hmemA⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6PlaneToralLang_proved (ringChar K) f hp hℓ3
      hf K hK
      K₁ ι₁ S hS (twBase K σ E₀) hAS hA_exp hA_card Fr hFr hFix
  have hmem : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom :=
    fun x hx => hmemA _ (Subgroup.mem_map_of_mem _ hx)
  have hreg :
      ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → ¬ TwKills K σ E₀ g0 α :=
    fun α hα hk => hn (hN (ringChar K ^ f) K σ hK hσ E₀ hexp hcard Fr hFr v g0 hg0 hF hmem α hα hk)
  exact hH (ringChar K ^ f) K σ k hfix hK hσ hkq hq hq3 E₀ hexp hcard hn Fr hFr v g0 hg0 hF hmem
    hreg

end CFSG.LieType.SeitzGeneration.ExcHighThree
