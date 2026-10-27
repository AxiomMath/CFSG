module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Share
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Export
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedCentral
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Export
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

section Sign

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_signMaskTuple_mul_self (m : ℕ) :
    rootDiagUnit τ (signMaskTuple τ K m) * rootDiagUnit τ (signMaskTuple τ K m) = 1 := by
  rw [← rootDiagUnit_mul]
  have : (signMaskTuple τ K m * signMaskTuple τ K m) = 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.one_apply, signMaskTuple, ← pow_add]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ (i : ℕ)) with h | h <;> rw [h]
    · simp
    · rw [← two_mul, pow_mul]
      simp
  rw [this, rootDiagUnit_one]

end Sign

section Datum

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem d4_eq_one_or_eq_of_isPerfect_le_totalFixedGroup
    (D : OrthogonalSemilinearFixedRootDatum Tag.D4 p k) (hχ : D.χ = signMaskChar Tag.D4 4)
    (hθ : ThetaProperties TwistTag.D4.perm 3 D.χ (wordElt Tag.D4 []))
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (wordElt Tag.D4 []) TwistTag.D4.perm γ))
    {P : Subgroup (adjointGroup Tag.D4 k)} (hP : P ≤ D.totalFixedGroup) (hperf : ⁅P, P⁆ = P)
    {c : adjointGroup Tag.D4 k} (hc : c ∈ P) (hcP : ∀ y ∈ P, c * y = y * c) :
    c = 1 ∨ (c : ModGL Tag.D4 k) = rootDiagUnit Tag.D4 (signMaskTuple Tag.D4 k 4) := by
  classical
  have := D.finite_orbitIndex
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact D.odd
  set x' : adjointGroup Tag.D4 k :=
    ⟨rootDiagUnit Tag.D4 (signMaskTuple Tag.D4 k 4),
      torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup _)⟩ with hx'
  choose O hO using fun J' : ↥(Set.range D.classOrbit) => d4_orbits_eq_singleton D hχ J'
  have hmem : ∀ J', O J' ∈ (D.withOrbit J').orbits := fun J' => by
    rw [hO J']
    exact Set.mem_singleton _
  have hodd : ∀ J' : ↥(Set.range D.classOrbit), ∀ {O' : Set (Fin Tag.D4.rank → ℤ)},
      O' ∈ (D.withOrbit J').orbits → Odd (orbitCard O') := by
    intro J' O' hO'
    rcases orbitCard_eq_of_thetaProperties (D.withOrbit J') hθ hDθ hO' with h | h <;> rw [h]
    · exact odd_one
    · decide
  let φ : ∀ J' : ↥(Set.range D.classOrbit),
      SL(2, ↥((D.withOrbit J').orbitField (O J'))) →* adjointGroup Tag.D4 k := fun J' =>
    ((D.withOrbit J').orbitMapHom (hmem J')).codRestrict _
      (fun A => (D.withOrbit J').orbitMap_mem_adjointGroup (O J') A)
  have hφ : ∀ J' A, ((φ J' A : adjointGroup Tag.D4 k) : ModGL Tag.D4 k) =
      (D.withOrbit J').orbitMap (O J') A := fun J' A => rfl
  have hneg : ∀ J', φ J' (-1) = x' := fun J' => Subtype.ext (by
    rw [hφ]
    exact orbitMap_neg_one_d4 (D.withOrbit J') hχ (hodd J') (hmem J'))
  have hx1 : x' ≠ 1 := by
    intro h
    have h1 : rootDiagUnit Tag.D4 (signMaskTuple Tag.D4 k 4) = rootDiagUnit Tag.D4 1 := by
      rw [rootDiagUnit_one]
      exact congrArg Subtype.val h
    have h2 := congrFun (rootDiagUnit_injective h1) ⟨2, by decide⟩
    simp only [signMaskTuple, Pi.one_apply] at h2
    have h3 : (-1 : kˣ) = 1 := by simpa using h2
    have h4 : (-1 : k) = 1 := congrArg Units.val h3
    have h5 : (2 : k) = 0 := by linear_combination -h4
    exact Ring.two_ne_zero hk2 h5
  have hinj : ∀ J', Function.Injective (φ J') := by
    intro J'
    rw [injective_iff_map_eq_one]
    intro A hA
    have h1 : (D.withOrbit J').orbitMap (O J') A = 1 := congrArg Subtype.val hA
    rcases (D.withOrbit J').eq_one_or_neg_one_of_orbitMap_eq_one (hmem J') h1 with rfl | rfl
    · rfl
    · exact absurd ((hneg J').symm.trans hA) hx1
  have hx2 : x' * x' = 1 := Subtype.ext (rootDiagUnit_signMaskTuple_mul_self 4)
  have hcomm : Pairwise fun J₁ J₂ => ∀ A B, φ J₁ A * φ J₂ B = φ J₂ B * φ J₁ A := by
    intro J₁ J₂ hne A B
    apply Subtype.ext
    exact (D.commute_of_ne hne ((D.withOrbit J₁).orbitMap_mem_rootSpanJ (hmem J₁) A)
      ((D.withOrbit J₂).orbitMap_mem_rootSpanJ (hmem J₂) B)).eq
  have hle : P ≤ ⨆ J', (φ J').range := by
    refine (le_iSup_orbitGroupC_of_isPerfect D hP (Subgroup.isPerfect_iff.2 hperf)).trans
      (iSup_mono fun J' => ?_)
    intro y hy
    have hy' : (y : ModGL Tag.D4 k) ∈ (D.withOrbit J').orbitGroup :=
      (D.withOrbit J').coe_mem_orbitGroup_of_mem_orbitGroupC hy
    have h1 : (y : ModGL Tag.D4 k) ∈ Set.range ((D.withOrbit J').orbitMap (O J')) := by
      rw [(D.withOrbit J').range_orbitMap_eq_of_orbits_eq (hO J')]
      exact hy'
    obtain ⟨A, hA⟩ := h1
    exact ⟨A, Subtype.ext hA⟩
  rcases CFSG.ClassicalInvolution.Balance.Bootstrap.eq_one_or_eq_of_isPerfect_of_le_iSup_range φ
    hinj x' hneg hx2 hcomm hle hperf hc hcP with h | h
  · exact Or.inl h
  · exact Or.inr (congrArg Subtype.val h)

end Datum

section Model

open CFSG.LieType.Steinberg.TwistedD4

variable (p e : ℕ) [Fact p.Prime]

theorem trialityD4_eq_of_central_in_perfect (hp2 : p ≠ 2) (he : 1 ≤ e)
    {R₂ : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hperf : ⁅R₂, R₂⁆ = R₂) {c₁ c₂ : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)}
    (hc₁sq : c₁ * c₁ = 1) (hc₁ : c₁ ≠ 1) (hc₂ : c₂ ≠ 1) (hc₂R : c₂ ∈ R₂)
    (hc₂cent : ∀ r ∈ R₂, c₂ * r = r * c₂) (hc₁cent : ∀ r ∈ R₂, c₁ * r = r * c₁) : c₂ = c₁ := by
  classical
  set K0 := GaloisField p (3 * e) with hK0
  set k := AlgebraicClosure K0 with hk
  have hCharK : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  set Φ := trialityD4Phi p e k with hΦ
  have hinj : Function.Injective Φ := trialityD4Phi_injective p e k
  have hΦR : ∀ y, Φ y ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) :=
    trialityD4Phi_mem_fixedPointsIn p e hp2 he
  set x : ModGL TwistTag.D4.tag k := Φ c₁ with hx
  have hx2 : x ^ 2 = 1 := by rw [hx, pow_two, ← map_mul, hc₁sq, map_one]
  obtain ⟨r, hr, D, w, h, hw, hh, hwx, hDχ, hDe, hDθ, hDF, hPmap⟩ :=
    d4_exists_datum_conj_perfect p hp2 (isAlgebraic_zmod_of_isAlgClosure p K0 k) he (hΦR c₁) hx2
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  have hrm : r.mask = 4 := by
    rcases List.mem_cons.1 (hr : r ∈ ⟨0, 1, 1, d4OmegaWords0⟩ :: [⟨4, 3, 4, d4OmegaWords4⟩]) with
      rfl | hr'
    · exfalso
      apply hc₁
      have h0 : signMaskTuple TwistTag.D4.tag k 0 = 1 := by
        funext j
        simp [signMaskTuple]
      have e0 : w * x * w⁻¹ = 1 := by
        rw [hwx]
        change rootDiagUnit TwistTag.D4.tag
          (signCharTuple (signMaskChar TwistTag.D4.tag 0)) = 1
        rw [signCharTuple_signMaskChar, h0, rootDiagUnit_one]
      apply hinj
      rw [map_one]
      have h1 : x = 1 := by
        have := mul_left_cancel ((mul_inv_eq_one.1 e0).trans (mul_one w).symm)
        exact this
      exact h1
    · obtain rfl := List.mem_singleton.1 hr'
      rfl
  have hDχ4 : D.χ = signMaskChar Tag.D4 4 := by rw [hDχ, hrm]; rfl
  have hθ : ThetaProperties TwistTag.D4.perm 3 D.χ (wordElt Tag.D4 []) := by
    have := h4.theta r hr [] (nil_mem_omegaWords_d4 hr)
    rw [hDχ]
    exact this
  have hDθ' : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (wordElt Tag.D4 []) TwistTag.D4.perm γ) := by
    intro γ
    have e : thetaMap (wordElt Tag.D4 []) TwistTag.D4.perm γ = permLattice TwistTag.D4.perm γ := by
      simp only [wordElt_nil]
      exact thetaMap_one _ γ
    rw [hDθ γ, e]
    rfl
  set P : Subgroup (ModGL TwistTag.D4.tag k) := R₂.map Φ with hP
  have hPle : P ≤ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) ⊓
        Subgroup.centralizer {x} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hΦR y, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc Φ y * x = Φ (y * c₁) := (map_mul Φ y c₁).symm
      _ = Φ (c₁ * y) := by rw [(hc₁cent y hy).symm]
      _ = x * Φ y := map_mul Φ c₁ y
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, ← Subgroup.map_commutator, hperf]
  have hmap := hPmap P hPle hPperf
  let Φ' : twistedGroup (iterateFrobenius K0 p e) →* adjointGroup TwistTag.D4.tag k :=
    Φ.codRestrict _ (fun y => (mem_fixedPointsIn.1 (hΦR y)).1)
  let ψ : twistedGroup (iterateFrobenius K0 p e) →* adjointGroup TwistTag.D4.tag k :=
    (MulAut.conj (⟨w, hw⟩ : adjointGroup TwistTag.D4.tag k)).toMonoidHom.comp Φ'
  have hψ : ∀ y, ((ψ y : adjointGroup TwistTag.D4.tag k) : ModGL TwistTag.D4.tag k) =
      w * Φ y * w⁻¹ := fun y => rfl
  have hψinj : Function.Injective ψ := by
    intro y z hyz
    have h1 := congrArg Subtype.val hyz
    rw [hψ, hψ] at h1
    exact hinj (mul_right_cancel (mul_left_cancel h1 : Φ y * w⁻¹ = Φ z * w⁻¹))
  have hP'' : R₂.map ψ ≤ D.totalFixedGroup := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : w * Φ y * w⁻¹ ∈ P.map (MulAut.conj w).toMonoidHom :=
      ⟨Φ y, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨x₀, hx₀, hx₀e⟩ := hmap h1
    have : x₀ = ψ y := Subtype.ext (hx₀e.trans (hψ y).symm)
    rw [← this]
    exact hx₀
  have hperf'' : ⁅R₂.map ψ, R₂.map ψ⁆ = R₂.map ψ := by
    rw [← Subgroup.map_commutator, hperf]
  have hmem : ψ c₂ ∈ R₂.map ψ := ⟨c₂, hc₂R, rfl⟩
  have hcP : ∀ y ∈ R₂.map ψ, ψ c₂ * y = y * ψ c₂ := by
    rintro _ ⟨y, hy, rfl⟩
    calc ψ c₂ * ψ y = ψ (c₂ * y) := (map_mul ψ c₂ y).symm
      _ = ψ (y * c₂) := by rw [hc₂cent y hy]
      _ = ψ y * ψ c₂ := map_mul ψ y c₂
  rcases d4_eq_one_or_eq_of_isPerfect_le_totalFixedGroup D hDχ4 hθ hDθ' hP'' hperf'' hmem hcP with
    h1 | h1
  · exact absurd (hψinj (h1.trans (map_one ψ).symm)) hc₂
  · apply hψinj
    apply Subtype.ext
    rw [h1, hψ, ← hx, hwx, hrm, signCharTuple_signMaskChar]
    rfl

end Model

end CFSG.ClassicalInvolution.ModelFacts
