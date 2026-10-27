module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjMain
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4AtTwo
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InnerIsoTw
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillsRoot

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Lang.AnisoE6
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)

set_option linter.unusedSectionVars false

section Plane


theorem tw_plane_contained_of_isoLift {q : ℕ} {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) {k : Type} [Field k] [Finite k] [Algebra k K]
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hkq : Nat.card k = q)
    (hq : q % 3 = 2) (E₀ : Subgroup (twistedE6RootGroup K σ)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) (hn : ¬ NormalizesRIn (ringChar K) E₀)
    (hiso : TwIsoLift K σ E₀) :
    ∃ g : twistedE6RootGroup K σ,
      E₀.map (MulAut.conj g).toMonoidHom ≤
        ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range := by
  classical
  obtain ⟨K₁, _, _, ι₁, S, hS, hAS⟩ := hiso
  obtain ⟨hp, f, hf, rfl⟩ := exists_pow_ringChar_of_card_sq K q hK (by omega)
  have hℓ3 : ringChar K ≠ 3 := by
    intro h3
    rw [h3] at hq
    have h3' : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
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
    fun α hα hk => hn (twHighKillNR_two (ringChar K ^ f) K σ hK hσ E₀ hexp hcard Fr hFr v g0 hg0 hF
      hmem α hα hk)
  exact tw_regular_contained_gen σ hfix hK hσ hkq hq E₀ hexp hcard Fr hFr v g0 hg0 hF hmem hreg

@[expose] def TwHighIsotropicAtTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 2 ^ 2 → (∀ c : K, σ c = c ^ 2) →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRIn (ringChar K) E₀ → TwIsoLift K σ E₀

theorem twHighPlaneContainedAtTwo_of_isotropic (hI : TwHighIsotropicAtTwo) :
    TwHighPlaneContainedAtTwo := by
  intro K _ _ σ k _ _ _ hfix hK hσ hkq E₀ hexp hcard hn
  exact tw_plane_contained_of_isoLift σ hfix hK hσ hkq (by norm_num) E₀ hexp hcard hn
    (hI K σ hK hσ E₀ hexp hcard hn)

end Plane

section Iso


theorem tw_isoLift_of_frame (h : TwE6HeisFrameNormalizesR) {q : ℕ} {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hq3 : q % 3 = 2)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) (hnorm : ¬ NormalizesRIn (ringChar K) E₀) :
    TwIsoLiftX K σ E₀ := by
  classical
  have hq2 : 2 ≤ q := by omega
  obtain ⟨hp, f, hf, rfl⟩ := exists_pow_ringChar_of_card_sq K q hK hq2
  have hℓ3 : ringChar K ≠ 3 := by
    intro h3
    have : 3 ∣ ringChar K ^ f := by
      rw [h3]
      exact dvd_pow_self 3 (by omega)
    omega
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  haveI := hK₁
  have hinj := twistedE6InndiagConj_injective hp hf hK σ hσ
  have hcE : ∀ x : twistedE6RootGroup K σ,
      twistedE6InndiagConj K σ ⟨x, le_sup_left (b := twistedE6DiagGL K σ) x.2⟩ =
        MulAut.conj x := fun x => MulEquiv.ext fun y => Subtype.ext rfl
  have hinjc : Function.Injective (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
      MulAut ↥(twistedE6RootGroup K σ)) := by
    intro x y hxy
    rw [← hcE x, ← hcE y] at hxy
    have h2 : (x : ModGL TwistTag.E6.tag K) = y :=
      congrArg (Subtype.val : ↥(twistedE6InndiagGL K σ) → ModGL TwistTag.E6.tag K) (hinj hxy)
    exact Subtype.ext h2
  set E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) :=
    E₀.map (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)) with hE
  have hcardE : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective hinjc]
    exact hcard
  have hd : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rintro _ ⟨x, -, rfl⟩
    exact Subgroup.mem_sup_left ⟨x, rfl⟩
  have hEab : CFSG.IsElementaryAbelian 3 E := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcomm : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardE
    have hexpE : Monoid.exponent E ∣ 3 := by
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow, hexp x hx, map_one]
    exact { toIsMulCommutative := hcomm, exponent_dvd_p := hexpE }
  by_cases hiso : TwistedE6DiagIsotropic K σ K₁ E
  ·
    let ι' : ↥K₁ →+* AlgebraicClosure K := (K₁.val : ↥K₁ →ₐ[K] AlgebraicClosure K).toRingHom
    set P : Subgroup (ModGL Tag.E6 K₁) :=
      (((E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (algebraMap K K₁))) with hP
    let S : Subgroup ↥(e6Data_valid.minGroup K₁) :=
      P.comap ((adjointGroup Tag.E6 K₁).subtype.comp (e6Isogeny K₁))
    refine ⟨↥K₁, inferInstance, inferInstance, ι', S, ?_, ?_⟩
    · intro x hx y hy
      exact hiso x y hx hy
    · rintro _ ⟨x, hx, rfl⟩
      have hxin : (x : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ :=
        le_sup_left (b := twistedE6DiagGL K σ) x.2
      have hxad : baseChangeGL (algebraMap K K₁) (x : ModGL TwistTag.E6.tag K) ∈
          adjointGroup Tag.E6 K₁ :=
        map_twistedE6InndiagGL_le σ (algebraMap K K₁) hroot (Subgroup.mem_map_of_mem _ hxin)
      obtain ⟨s, hs⟩ := e6Isogeny_surjective K₁ ⟨_, hxad⟩
      have hs' : ((e6Isogeny K₁ s : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
          baseChangeGL (algebraMap K K₁) (x : ModGL TwistTag.E6.tag K) := by
        rw [hs]
      refine ⟨s, ?_, ?_⟩
      · show ((e6Isogeny K₁ s : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) ∈ P
        rw [hs']
        refine Subgroup.mem_map_of_mem _ ⟨⟨(x : ModGL TwistTag.E6.tag K), hxin⟩, ?_, rfl⟩
        show twistedE6InndiagConj K σ ⟨(x : ModGL TwistTag.E6.tag K), hxin⟩ ∈ E
        rw [hcE x]
        exact Subgroup.mem_map_of_mem _ hx
      · show baseChangeGL ι' ((e6Isogeny K₁ s : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) = _
        rw [hs']
        show baseChangeGL ι' (baseChangeGL (algebraMap K ↥K₁)
            ((x : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 K)) =
          baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 K)
        rw [baseChangeGL_baseChangeGL]
        rw [show ι'.comp (algebraMap K ↥K₁) = algebraMap K (AlgebraicClosure K) from
          RingHom.ext fun c => rfl]
  · exfalso
    obtain ⟨F⟩ := exists_twE6HeisenbergFrame (ringChar K) f hp hℓ3 hf hK σ hσ K₁ hroot E hEab
      hcardE hd hiso
    obtain ⟨R, hR1, hRp, hRfix⟩ := h (ringChar K) f hp hℓ3 hf K hK σ hσ E hd hEab hcardE F
    exact hnorm ⟨R, hR1, hRp, fun x hx =>
      mem_normalizer_of_map_conj_eq R x (hRfix _ ⟨x, hx, rfl⟩)⟩

theorem twHighIsotropicAtTwo_of_frame (h : TwE6HeisFrameNormalizesR) : TwHighIsotropicAtTwo := by
  intro K _ _ σ hK hσ E₀ hexp hcard hn
  exact tw_isoLift_of_frame h σ hK hσ (by norm_num) E₀ hexp hcard hn

end Iso

section Frame


theorem tw_plane_contained_of_frame (h : TwE6HeisFrameNormalizesR) {q : ℕ} {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) {k : Type} [Field k] [Finite k] [Algebra k K]
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hkq : Nat.card k = q)
    (hq : q % 3 = 2) (E₀ : Subgroup (twistedE6RootGroup K σ)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) (hn : ¬ NormalizesRIn (ringChar K) E₀) :
    ∃ g : twistedE6RootGroup K σ,
      E₀.map (MulAut.conj g).toMonoidHom ≤
        ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range :=
  tw_plane_contained_of_isoLift σ hfix hK hσ hkq hq E₀ hexp hcard hn
    (tw_isoLift_of_frame h σ hK hσ hq E₀ hexp hcard hn)

theorem twHighPlaneContainedAtTwo_of_frame (h : TwE6HeisFrameNormalizesR) :
    TwHighPlaneContainedAtTwo :=
  twHighPlaneContainedAtTwo_of_isotropic (twHighIsotropicAtTwo_of_frame h)

theorem twHighPlaneContained_two_of_frame (h : TwE6HeisFrameNormalizesR) :
    TwHighPlaneContained_two := by
  intro q K _ _ σ k _ _ _ hfix hK hσ hkq hq _hq3 E₀ hexp hcard hn
  exact tw_plane_contained_of_frame h σ hfix hK hσ hkq hq E₀ hexp hcard hn

end Frame

end CFSG.LieType.SeitzGeneration.ExcHighThree
