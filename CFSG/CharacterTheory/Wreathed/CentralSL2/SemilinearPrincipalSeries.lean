module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalSum

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Small

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem mem_parameterStabilizer_iff' (P : PrincipalSeriesParameter F b m) (σ : Sigma) :
    σ ∈ parameterStabilizer hSigma P ↔
      P.1.1.comp (Units.map ((σ⁻¹ : Sigma) : F ≃+* F).toRingHom.toMonoidHom) = P.1.1 := by
  rw [mem_parameterStabilizer_iff]
  constructor
  · intro h
    exact congrArg (fun Q : PrincipalSeriesParameter F b m => Q.1.1) h
  · intro h
    apply Subtype.ext
    exact Prod.ext h rfl

theorem ringEquiv_eq_one_of_card_prime [Fintype F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (h : Fintype.card F = p) (σ : F ≃+* F) : σ = 1 := by
  have hbij := ZMod.castHom_bijective F h
  refine RingEquiv.ext fun x => ?_
  obtain ⟨a, rfl⟩ := hbij.2 x
  have h1 := RingHom.ext_zmod (σ.toRingHom.comp (ZMod.castHom (dvd_refl p) F))
    (ZMod.castHom (dvd_refl p) F)
  exact DFunLike.congr_fun h1 a

theorem card_sigma_of_card_three [Fintype F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (h3 : Nat.card F = 3) : Nat.card Sigma = 1 := by
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := by
      rw [← h3, hcard]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP F 3 :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  have h3' : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, h3]
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun σ τ => Subtype.ext ?_⟩, ⟨1⟩⟩
  rw [ringEquiv_eq_one_of_card_prime h3' (σ : F ≃+* F),
    ringEquiv_eq_one_of_card_prime h3' (τ : F ≃+* F)]

end Small

theorem semilinear_principal_series_character_family {F : Type} [Field F] [Fintype F]
    {p f : ℕ} (hp : p.Prime) (_hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (b : Fˣ) (hb : ¬ IsSquare b) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (hd : Odd (Nat.card Sigma)) :
    let G := CentralExtension F b m hm heven
    let H := SemilinearExtension F b m hm heven Sigma hSigma
    let ι : G →* H := SemidirectProduct.inl
    let N : Subgroup H := baseLayer F b m hm heven Sigma hSigma
    let q := Nat.card F
    let d := Nat.card Sigma
    let u := cyclicGenerator F b m hm heven
    let x := u ^ m
    let hc := torusDiag F b m hm heven
    let w := weylElement F b m hm heven
    let v := torusGenerator F b m hm heven
    let U := unipotentSubgroup F b m hm heven
    let B := borelSubgroup F b m hm heven
    let T := splitTorus F b m hm heven
    let Par := PrincipalSeriesParameter F b m
    let lam : Par → T →* ℂˣ := fun P => torusCharacter F b m hm heven P
    let Ψ : Par → G → ℂ := fun P => principalSeries F b m hm heven (lam P)
    let act : Sigma → Par → Par := fieldParameter hSigma
    let wP : Par → Par := weylParameter F b m heven
    let Stab : Par → Subgroup Sigma := parameterStabilizer hSigma
    let I : Par → Subgroup H := fun P => semilinearInertia (Stab P)
    let BS : Par → Subgroup H := fun P => semilinearBorel hSigma (Stab P)
    let lamTilde : (P : Par) → (Stab P →* ℂˣ) → BS P →* ℂˣ :=
      fun P ρ => borelTwist hSigma P (Stab P) le_rfl ρ
    let Θ : (P : Par) → (Stab P →* ℂˣ) → H → ℂ :=
      fun P ρ => inducedFunction (BS P) fun y => (lamTilde P ρ y : ℂ)
    let Fam : Set (H → ℂ) := {χ | ∃ (P : Par) (ρ : Stab P →* ℂˣ), P.1.1 ≠ 1 ∧ χ = Θ P ρ}
    x = specialInclusion F b m hm heven (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) ∧
    (∀ c : Fˣ, hc c = specialInclusion F b m hm heven (diagSL F c) ∧
      (diagSL F c : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)]) ∧
    w = specialInclusion F b m hm heven (weyl F) ∧
    (weyl F : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] ∧ v = w⁻¹ * u ∧
    (∀ g, g ∈ U ↔ ∃ t : F, g = specialInclusion F b m hm heven (upperSL F t)) ∧
    B = MulAction.stabilizer G (none : Omega F) ∧
    T = B ⊓ MulAction.stabilizer G (some 0 : Omega F) ∧
    torusConstant F b m = -((-b⁻¹) ^ (m / 2)) ∧
    (∀ P : Par, (∀ c, lam P ⟨hc c, torusDiag_mem_splitTorus F b m hm heven c⟩ = P.1.1 c) ∧
      lam P ⟨v, torusGenerator_mem_splitTorus F b m hm heven⟩ = P.1.2) ∧
    (∀ P : Par, Ψ P = inducedFunction B fun g =>
      (lam P (borelProjection F b m hm heven g) : ℂ)) ∧
    Function.Surjective (borelProjection F b m hm heven) ∧
    (∀ g : B, borelProjection F b m hm heven g = 1 ↔ (g : G) ∈ U) ∧
    (∀ σ P, (act σ P).1 =
      (P.1.1.comp (Units.map ((σ⁻¹ : Sigma) : F ≃+* F).toRingHom.toMonoidHom), P.1.2)) ∧
    (∀ P, (wP P).1 = (P.1.1⁻¹, P.1.1 b * P.1.2)) ∧
    (∀ σ τ P, act (σ * τ) P = act σ (act τ P)) ∧ (∀ P, act 1 P = P) ∧
    (∀ σ P, act σ (wP P) = wP (act σ P)) ∧
    (∀ P σ, σ ∈ Stab P ↔
      P.1.1.comp (Units.map ((σ⁻¹ : Sigma) : F ≃+* F).toRingHom.toMonoidHom) = P.1.1) ∧
    (∀ σ P, Stab (act σ P) = Stab P) ∧ (∀ P, Stab (wP P) = Stab P) ∧
    (∀ σ P g, Ψ P (fieldAction F b m hm heven Sigma hSigma σ⁻¹ g) = Ψ (act σ P) g) ∧
    N = ι.range ∧ (∀ P (n : N), layerFunction (Ψ P) n = Ψ P (n : H).left) ∧
    (∀ P, P.1.1 ≠ 1 → characterInertiaSubgroup N (layerFunction (Ψ P)) = I P) ∧
    (∀ P h, h ∈ I P ↔ h.right ∈ Stab P) ∧
    (∀ P h, h ∈ BS P ↔ h.left ∈ B ∧ h.right ∈ Stab P) ∧
    (∀ P ρ (y : BS P), lamTilde P ρ y =
      lam P (borelProjection F b m hm heven ⟨(y : H).left, y.2.1⟩) * ρ ⟨(y : H).right, y.2.2⟩) ∧
    (∀ P ρ, P.1.1 ≠ 1 → Θ P ρ ∈ BlocksIrr H ∧ Θ P ρ 1 = ((Stab P).index : ℂ) * (q + 1)) ∧
    (∀ P, P.1.1 ≠ 1 → Function.Injective (Θ P)) ∧
    (∀ P, Nat.card (Stab P →* ℂˣ) = Nat.card (Stab P)) ∧
    (∀ χ ∈ BlocksIrr H, (∃ P : Par, P.1.1 ≠ 1 ∧
      0 < BlocksInnerProduct (fun g => χ (ι g)) (Ψ P)) ↔ χ ∈ Fam) ∧
    (∀ P, P.1.1 ≠ 1 → ∀ χ ∈ BlocksIrr H,
      0 < BlocksInnerProduct (fun g => χ (ι g)) (Ψ P) ↔ ∃ ρ, χ = Θ P ρ) ∧
    (∀ P P' ρ ρ', P.1.1 ≠ 1 → P'.1.1 ≠ 1 → (Θ P ρ = Θ P' ρ' ↔
      (∃ σ, P' = act σ P ∨ P' = act σ (wP P)) ∧
        ∀ τ (h₁ : τ ∈ Stab P) (h₂ : τ ∈ Stab P'), ρ ⟨τ, h₁⟩ = ρ' ⟨τ, h₂⟩)) ∧
    (∀ P ρ, P.1.1 ≠ 1 → ∀ C : Finset Sigma,
      (∀ q' : Sigma ⧸ Stab P, ∃! σ, σ ∈ C ∧ (σ : Sigma ⧸ Stab P) = q') →
      (fun g => Θ P ρ (ι g)) = ∑ σ ∈ C, Ψ (act σ P) ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' → Ψ (act σ P) ≠ Ψ (act σ' P)) ∧
      (∀ σ ∈ C, BlocksInnerProduct (fun g => Θ P ρ (ι g)) (Ψ (act σ P)) = 1)) ∧
    (∀ P ρ (g : G) (τ : Sigma), P.1.1 ≠ 1 → τ ∉ Stab P → Θ P ρ ⟨g, τ⟩ = 0) ∧
    (∀ P ρ, P.1.1 ≠ 1 → Θ P ρ (ι x) = ((Stab P).index : ℂ) * (q + 1) * (P.1.1 (-1) : ℂ)) ∧
    (∃ hfin : Fam.Finite,
      ∑ χ ∈ hfin.toFinset, χ 1 ^ 2 = ((d * m * (q - 2) * (q + 1) ^ 2 / 2 : ℕ) : ℂ)) ∧
    (q = 3 → m = 4 → Fam.ncard = 2 ∧ ∀ χ ∈ Fam, χ 1 = 4) := by
  intro G H ι N q d u x hc w v U B T Par lam Ψ act wP Stab I BS lamTilde Θ Fam
  have hΘ : ∀ P ρ, Θ P ρ = principalInduced (hm := hm) (heven := heven) hSigma P ρ :=
    fun _ _ => rfl
  have hFam : Fam = principalFamilyH (hm := hm) (heven := heven) hSigma := rfl
  have hfin : Fam.Finite := principalFamilyH_finite hSigma hb hd
  have hsum := sum_sq_principalFamilyH (hm := hm) (heven := heven) hSigma hb hd
  refine ⟨cyclicGenerator_pow_m F b m hm heven, fun c => ⟨rfl, rfl⟩, rfl, rfl, rfl, ?_, rfl, rfl,
    rfl, fun P => ⟨torusCharacter_torusDiag F b m hm heven P,
      torusCharacter_torusGenerator F b m hm heven P⟩, fun P => rfl,
    borelProjection_surjective F b m hm heven, ?_, fun σ P => rfl,
    weylParameter_fst F b m heven, fieldParameter_mul hSigma, fieldParameter_one hSigma,
    fieldParameter_weylParameter hSigma heven, mem_parameterStabilizer_iff' hSigma,
    parameterStabilizer_fieldParameter hSigma, parameterStabilizer_weylParameter hSigma heven,
    fun σ P g => congrFun (principalSeries_fieldTwist hSigma σ P) g, rfl, fun P n => rfl,
    fun P hP => inertia_principalSeries hSigma hb hd hP, fun P h => Iff.rfl,
    fun P h => Iff.rfl, fun P ρ y => rfl,
    fun P ρ hP => (principal_clifford hSigma hb hd hP).1 ρ,
    fun P hP => (principal_clifford hSigma hb hd hP).2.1, ?_,
    fun χ hχ => mem_principalFamilyH_iff hSigma hb hd hχ,
    fun P hP => (principal_clifford hSigma hb hd hP).2.2.1,
    fun P P' ρ ρ' hP hP' => principalInduced_eq_iff hSigma hb hd hP hP' ρ ρ',
    fun P ρ hP C hC => ⟨((principal_clifford hSigma hb hd hP).2.2.2.1 C hC).1 ρ,
      ((principal_clifford hSigma hb hd hP).2.2.2.1 C hC).2.1,
      ((principal_clifford hSigma hb hd hP).2.2.2.1 C hC).2.2 ρ⟩,
    fun P ρ g τ hP hτ => (principal_clifford hSigma hb hd hP).2.2.2.2 ρ g τ hτ,
    fun P ρ hP => principalInduced_x hSigma hb hd hP ρ, ⟨hfin, hsum⟩, ?_⟩
  · intro g
    rw [mem_unipotentSubgroup_iff]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
  · intro g
    constructor
    · intro hg1
      have h1 : borelProjectionFun F b m hm heven g = 1 := congrArg Subtype.val hg1
      rw [← unipotentElement_mul_borelProjectionFun F b m hm heven g, h1, mul_one]
      exact (mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨_, rfl⟩
    · intro hg
      exact borelProjection_of_mem_unipotent F b m hm heven g hg
  · intro P
    have hcyc : IsCyclic (Stab P) := by
      have : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
      infer_instance
    let _ : CommGroup (Stab P) := IsCyclic.commGroup
    exact card_hom_units_of_isCyclic (Stab P)
  · intro hq hm4
    have hd1 : d = 1 := card_sigma_of_card_three hp hf hcard hq
    have hdeg : ∀ χ ∈ Fam, χ 1 = 4 := by
      rintro χ ⟨P, ρ, hP, rfl⟩
      rw [hΘ, ((principal_clifford hSigma hb hd hP).1 ρ).2]
      have hidx : (Stab P).index = 1 := by
        have h1 := Subgroup.card_mul_index (Stab P)
        rw [show Nat.card Sigma = 1 from hd1] at h1
        exact Nat.eq_one_of_mul_eq_one_left h1
      rw [hidx, show Nat.card F = 3 from hq]
      norm_num
    refine ⟨?_, hdeg⟩
    have h1 : ∑ χ ∈ hfin.toFinset, χ 1 ^ 2 = (Fam.ncard : ℂ) * 16 := by
      rw [Finset.sum_congr rfl fun χ hχ => by rw [hdeg χ ((Set.Finite.mem_toFinset hfin).mp hχ)],
        Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin]
      norm_num
    have h2 : ∑ χ ∈ hfin.toFinset, χ 1 ^ 2 =
        ((Nat.card Sigma * m * (Nat.card F - 2) * (Nat.card F + 1) ^ 2 / 2 : ℕ) : ℂ) := hsum
    rw [h1, show Nat.card Sigma = 1 from hd1, show Nat.card F = 3 from hq, hm4] at h2
    norm_num at h2
    exact_mod_cast (by linear_combination h2 / 16 : (Fam.ncard : ℂ) = 2)

end CFSG.Wreathed.CentralSL2
