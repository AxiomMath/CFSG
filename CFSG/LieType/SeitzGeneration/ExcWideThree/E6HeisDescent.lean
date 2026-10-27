module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6HeisCore
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillsRoot

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


@[expose] def E6HeisFrameFixedElt : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → E ≤ e6Inndiag K → ∀ F : E6HeisenbergFrame K E,
        ∃ v : ModGL Tag.E6 (AlgebraicClosure K),
          v ∈ adjointGroup Tag.E6 (AlgebraicClosure K) ∧ v ≠ 1 ∧ v ^ ringChar K = 1 ∧
          Units.map (entrywiseHom F.Fr) v = v ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K)) (F.g₁ : ModGL Tag.E6 K)) ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K)) (F.g₂ : ModGL Tag.E6 K))

@[expose] def TwE6HeisFrameFixedElt : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ∀ F : TwE6HeisenbergFrame K σ (ℓ ^ f) E,
        ∃ v : ModGL TwistTag.E6.tag (AlgebraicClosure K),
          v ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧ v ≠ 1 ∧ v ^ ℓ = 1 ∧
          twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr v = v ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K))
            (F.g₁ : ModGL TwistTag.E6.tag K)) ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K))
            (F.g₂ : ModGL TwistTag.E6.tag K))

theorem fix_of_closure_pair {G : Type*} [Group G] (E : Subgroup (MulAut G)) (a b : MulAut G)
    (u : G) (hgen : E = Subgroup.closure {a, b}) (ha : a u = u) (hb : b u = u) :
    ∀ ε ∈ E, ε u = u := by
  have hle : E ≤ MulAction.stabilizer (MulAut G) u := by
    rw [hgen, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  intro ε hε
  exact MulAction.mem_stabilizer_iff.1 (hle hε)

theorem map_zpowers_eq_of_fix {G : Type*} [Group G] (ε : MulAut G) (u : G) (h : ε u = u) :
    (Subgroup.zpowers u).map ε.toMonoidHom = Subgroup.zpowers u := by
  rw [MonoidHom.map_zpowers]
  have h' : ε.toMonoidHom u = u := h
  rw [h']

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] (ℓ : ℕ) (u : G) (h : u ^ ℓ = 1) :
    IsPGroup ℓ (Subgroup.zpowers u) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, h, one_zpow]

theorem e6HeisFrameNormalizesR_of_fixedElt (h : E6HeisFrameFixedElt) : E6HeisFrameNormalizesR := by
  intro K _ _ hK3 hK4 E hEab hcard hd F
  classical
  obtain ⟨v, hvC, hv1, hvp, hvF, hc₁, hc₂⟩ := h K hK3 hK4 E hEab hcard hd F
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hcop : ringChar K ≠ 3 → Nat.Coprime 3 (orderOf v) := by
    intro h3
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hvp) ?_
    exact (Nat.coprime_primes Nat.prime_three Fact.out).2 (Ne.symm h3)
  obtain ⟨r₀, hr₀mem, hr₀eq⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E6 F.Fr F.hFr
      hvC hvF hcop)
  have hinj := baseChangeGL_injective (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
  set U : adjointGroup Tag.E6 K := ⟨r₀, hr₀mem⟩ with hU
  have hUord : U ^ ringChar K = 1 := by
    apply Subtype.ext
    apply hinj
    simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
    rw [hU]
    show baseChangeGL _ r₀ ^ ringChar K = 1
    rw [hr₀eq]
    exact hvp
  have hU1 : U ≠ 1 := by
    intro h1
    apply hv1
    have := congrArg Subtype.val h1
    rw [← hr₀eq]
    have h2 : r₀ = 1 := by simpa [hU] using this
    rw [h2, map_one]
  have hcomm : ∀ g : ModGL Tag.E6 K, Commute (baseChangeGL (algebraMap K (AlgebraicClosure K)) g) v →
      g * r₀ * g⁻¹ = r₀ := by
    intro g hg
    apply hinj
    rw [map_mul, map_mul, map_inv, hr₀eq]
    have := hg.eq
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  refine ⟨Subgroup.zpowers U, ?_, isPGroup_zpowers_of_pow_eq_one _ U hUord, ?_⟩
  · intro h0
    exact hU1 (Subgroup.zpowers_eq_bot.1 h0)
  · have hfix : ∀ ε ∈ E, ε U = U := by
      refine fix_of_closure_pair E _ _ U F.hgen ?_ ?_
      · apply Subtype.ext
        rw [e6InndiagConj_apply]
        exact hcomm _ hc₁.symm
      · apply Subtype.ext
        rw [e6InndiagConj_apply]
        exact hcomm _ hc₂.symm
    intro ε hε
    exact map_zpowers_eq_of_fix ε U (hfix ε hε)

theorem twE6HeisFrameNormalizesR_of_fixedElt (h : TwE6HeisFrameFixedElt) :
    TwE6HeisFrameNormalizesR := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ E hE hEab hcard F
  classical
  obtain ⟨v, hvC, hv1, hvp, hvF, hc₁, hc₂⟩ := h ℓ f hℓ hℓ3 hf K hK σ hσ E hE hEab hcard F
  obtain ⟨u, hu, hux⟩ := ExcHighThree.twisted_descent_E6 hℓ hf K hK σ hσ F.Fr F.hFr hℓ hℓ3 hvC
    hvF hvp
  have hinj := baseChangeGL_injective (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K))
  set U : twistedE6RootGroup K σ := ⟨u, hu⟩ with hU
  have hUord : U ^ ℓ = 1 := by
    apply Subtype.ext
    apply hinj
    simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
    rw [hU]
    show baseChangeGL _ u ^ ℓ = 1
    rw [hux]
    exact hvp
  have hU1 : U ≠ 1 := by
    intro h1
    apply hv1
    have := congrArg Subtype.val h1
    rw [← hux]
    have h2 : u = 1 := by simpa [hU] using this
    rw [h2, map_one]
  have hcomm : ∀ g : ModGL TwistTag.E6.tag K,
      Commute (baseChangeGL (algebraMap K (AlgebraicClosure K)) g) v → g * u * g⁻¹ = u := by
    intro g hg
    apply hinj
    rw [map_mul, map_mul, map_inv, hux]
    have := hg.eq
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hrc : ringChar K = ℓ := by
    have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
    exact ringChar_eq_of_card_pow hℓ hf K hK'
  refine ⟨Subgroup.zpowers U, ?_, ?_, ?_⟩
  · intro h0
    exact hU1 (Subgroup.zpowers_eq_bot.1 h0)
  · rw [hrc]
    exact isPGroup_zpowers_of_pow_eq_one _ U hUord
  · have hfix : ∀ ε ∈ E, ε U = U := by
      refine fix_of_closure_pair E _ _ U F.hgen ?_ ?_
      · apply Subtype.ext
        rw [twistedE6InndiagConj_apply]
        exact hcomm _ hc₁.symm
      · apply Subtype.ext
        rw [twistedE6InndiagConj_apply]
        exact hcomm _ hc₂.symm
    intro ε hε
    exact map_zpowers_eq_of_fix ε U (hfix ε hε)

end CFSG.LieType.SeitzGeneration.ExcWideThree
