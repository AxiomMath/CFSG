module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6HeisCore

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] (R : Subgroup G) (x : G)
    (h : R.map (MulAut.conj x).toMonoidHom = R) : x ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨r, hr, hry⟩ := hy
    have : r = y := by
      simpa [MulAut.conj_apply] using hry
    rwa [← this]

@[expose] def TwIsoLiftX (K : Type) [Field K] (σ : K ≃+* K)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) : Prop :=
  ∃ (K₁ : Type) (_ : Field K₁) (_ : Finite K₁) (ι : K₁ →+* AlgebraicClosure K)
    (S : Subgroup ↥(e6Data_valid.minGroup K₁)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
      twBase K σ E₀ ≤ S.map (e6ScToBar K₁ ι)

theorem twHighIsotropic_twoX_of_frame (h : TwE6HeisFrameNormalizesR) :
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = q ^ 2 →
      (∀ c : K, σ c = c ^ q) → q % 3 = 2 → 3 ≤ q →
      ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
        ¬ NormalizesRIn (ringChar K) E₀ → TwIsoLiftX K σ E₀ := by
  intro q K _ _ σ hK hσ hq3 hq3' E₀ hexp hcard hnorm
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

theorem twHighIsotropic_two_of_frame (h : TwE6HeisFrameNormalizesR) : TwHighIsotropic_two :=
  twHighIsotropic_twoX_of_frame h

end CFSG.LieType.SeitzGeneration.ExcHighThree
