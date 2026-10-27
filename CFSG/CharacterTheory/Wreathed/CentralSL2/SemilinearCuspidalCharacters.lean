module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearCuspidalFamily

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

theorem semilinear_cuspidal_characters_and_complete_family {F : Type} [Field F] [Fintype F]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (_hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
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
    let h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
    let C : Set (G → ℂ) := {θ | θ ∈ BlocksIrr G ∧ θ 1 = (q : ℂ) - 1}
    let act : Sigma → (G → ℂ) → G → ℂ := fun σ θ g =>
      θ (fieldAction F b m hm heven Sigma hSigma σ⁻¹ g)
    let Stab : (G → ℂ) → Subgroup Sigma := fun θ => twistStabilizer hSigma θ
    let I : (G → ℂ) → Subgroup H := fun θ => semilinearInertia (Stab θ)
    let IsExt : (θ : G → ℂ) → (I θ → ℂ) → Prop := fun θ χ =>
      χ ∈ BlocksIrr (I θ) ∧ ∀ (g : G) (hg : ι g ∈ I θ), χ ⟨ι g, hg⟩ = θ g
    let Θ : (θ : G → ℂ) → (I θ → ℂ) → (Stab θ →* ℂˣ) → H → ℂ := fun θ χ ρ =>
      inducedFunction (I θ) fun y => χ y * (ρ ⟨(y : H).right, y.2⟩ : ℂ)
    let ε : (G → ℂ) → ℂ := fun θ => θ x / ((q : ℂ) - 1)
    let Cusp : Set (H → ℂ) :=
      {ξ | ξ ∈ BlocksIrr H ∧ ∃ θ ∈ C, 0 < BlocksInnerProduct (fun g => ξ (ι g)) θ}
    let IsReps : Set (G → ℂ) → Prop := fun R =>
      R ⊆ C ∧ ∀ θ ∈ C, ∃! θ', θ' ∈ R ∧ ∃ σ, θ = act σ θ'
    let Fam : Set (G → ℂ) → ((θ : G → ℂ) → I θ → ℂ) → Set (H → ℂ) := fun R ext =>
      {ξ | ∃ θ ∈ R, ∃ ρ, ξ = Θ θ (ext θ) ρ}
    let Par := PrincipalSeriesParameter F b m
    let ΘP : (P : Par) → (parameterStabilizer hSigma P →* ℂˣ) → H → ℂ := fun P ρ =>
      inducedFunction (semilinearBorel hSigma (parameterStabilizer hSigma P)) fun y =>
        (borelTwist hSigma P (parameterStabilizer hSigma P) le_rfl ρ y : ℂ)
    let PH : Set (H → ℂ) :=
      {χ | ∃ (P : Par) (ρ : parameterStabilizer hSigma P →* ℂˣ), P.1.1 ≠ 1 ∧ χ = ΘP P ρ}
    x = specialInclusion F b m hm heven (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) ∧
    (∀ (σ : Sigma) (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)),
      fieldAction F b m hm heven Sigma hSigma σ (quotientClass F b m hm heven X j) =
        quotientClass F b m hm heven (fieldSL F σ X) j) ∧
    (∀ (σ : F ≃+* F) (X : SpecialLinearGroup (Fin 2) F) (i k : Fin 2),
      (fieldSL F σ X : Matrix (Fin 2) (Fin 2) F) i k = σ (X i k)) ∧
    (∀ σ : Sigma, fieldAction F b m hm heven Sigma hSigma σ x = x) ∧
    (∀ (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E) (y : Eˣ)
        (hy : (y : E) * (y : E) ^ q = -1) (ψ : AddChar F ℂ), ψ ≠ 1 →
      C = (fun lam => cuspidalCharacter hb ψ lam) ''
        {lam : nonsplitTorus F b m hm heven E basis →* ℂˣ |
          lam.comp (minusWeylConj h2 y hy) ≠ lam}) ∧
    C.ncard = m * q / 2 ∧
    (∀ σ τ θ, act (σ * τ) θ = act σ (act τ θ)) ∧ (∀ θ, act 1 θ = θ) ∧
    (∀ θ ∈ C, ∀ σ, act σ θ ∈ C) ∧
    (∀ θ σ, σ ∈ Stab θ ↔ act σ θ = θ) ∧
    (∀ θ (h : H), h ∈ I θ ↔ h.right ∈ Stab θ) ∧
    (∀ θ ∈ C, characterInertiaSubgroup N (layerFunction θ) = I θ) ∧
    (∀ θ, Nat.card (Stab θ →* ℂˣ) = Nat.card (Stab θ)) ∧
    (∀ θ, Nat.card (Stab θ) * (Stab θ).index = d) ∧
    (∀ θ ∈ C, ∃ χ, IsExt θ χ) ∧
    (∀ θ ∈ C, ∀ χ, IsExt θ χ → ∀ ρ,
      Θ θ χ ρ ∈ BlocksIrr H ∧ Θ θ χ ρ 1 = ((Stab θ).index : ℂ) * ((q : ℂ) - 1)) ∧
    (∀ θ ∈ C, ∀ χ, IsExt θ χ → Function.Injective (Θ θ χ)) ∧
    (∀ θ ∈ C, ∀ χ, IsExt θ χ → ∀ ξ ∈ BlocksIrr H,
      0 < BlocksInnerProduct (fun g => ξ (ι g)) θ ↔ ∃ ρ, ξ = Θ θ χ ρ) ∧
    (∃ (R : Set (G → ℂ)) (ext : (θ : G → ℂ) → I θ → ℂ),
      IsReps R ∧ ∀ θ ∈ R, IsExt θ (ext θ)) ∧
    (∀ (R : Set (G → ℂ)) (ext : (θ : G → ℂ) → I θ → ℂ),
      IsReps R → (∀ θ ∈ R, IsExt θ (ext θ)) →
      Fam R ext = Cusp ∧
        ∀ θ ∈ R, ∀ θ' ∈ R, ∀ ρ ρ', Θ θ (ext θ) ρ = Θ θ' (ext θ') ρ' → θ = θ') ∧
    (∀ θ ∈ C, ∀ χ, IsExt θ χ → ∀ T : Finset Sigma,
      (∀ q' : Sigma ⧸ Stab θ, ∃! σ, σ ∈ T ∧ (σ : Sigma ⧸ Stab θ) = q') →
      (∀ ρ, (fun g => Θ θ χ ρ (ι g)) = ∑ σ ∈ T, act σ θ) ∧
      (∀ σ ∈ T, ∀ σ' ∈ T, σ ≠ σ' → act σ θ ≠ act σ' θ) ∧
      (∀ σ : Sigma, ∃ σ' ∈ T, act σ θ = act σ' θ) ∧
      (∀ ρ, ∀ σ ∈ T, BlocksInnerProduct (fun g => Θ θ χ ρ (ι g)) (act σ θ) = 1)) ∧
    (∀ θ ∈ C, ∀ χ, IsExt θ χ → ∀ ρ (g : G) (τ : Sigma), τ ∉ Stab θ →
      Θ θ χ ρ ⟨g, τ⟩ = 0) ∧
    (∀ θ ∈ C, ε θ = 1 ∨ ε θ = -1) ∧
    (∀ θ ∈ C, ∀ σ, ε (act σ θ) = ε θ) ∧
    (∀ θ ∈ C, ∀ χ, IsExt θ χ → ∀ ρ,
      Θ θ χ ρ (ι x) = ((Stab θ).index : ℂ) * ((q : ℂ) - 1) * ε θ) ∧
    (∃ θ ∈ C, ε θ = -1) ∧
    (∃ hfin : Cusp.Finite,
      ∑ ξ ∈ hfin.toFinset, ξ 1 ^ 2 = ((d * m * q * (q - 1) ^ 2 / 2 : ℕ) : ℂ)) ∧
    Nat.card H = m * d * q * (q ^ 2 - 1) ∧
    (nonsquareMatrix F b : Matrix (Fin 2) (Fin 2) F) = !![0, -(b : F); 1, 0] ∧
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (σ : Sigma) (v w : Fin 2 → F)
        (hv : v ≠ 0) (hw : w ≠ 0),
      w = (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
        GeneralLinearGroup (Fin 2) F).val *ᵥ (fun i => (σ : F ≃+* F) (v i)) →
      coordinateEquiv F ((⟨quotientClass F b m hm heven X j, σ⟩ : H) •
        (coordinateEquiv F).symm (Projectivization.mk F v hv)) = Projectivization.mk F w hw) ∧
    (∀ Rp : Set Par, (∀ P ∈ Rp, P.1.1 ≠ 1) →
      (∀ P : Par, P.1.1 ≠ 1 → ∃ P' ∈ Rp, ∃ σ : Sigma,
        P = fieldParameter hSigma σ P' ∨
          P = fieldParameter hSigma σ (weylParameter F b m heven P')) →
      {χ | ∃ P ∈ Rp, ∃ ρ, χ = ΘP P ρ} = PH) ∧
    ∀ (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ)
      (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd d),
      let lam : Fin m → Fin d → H → ℂ := fun r s h =>
        (CentralSL2Abelianization.linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm
          hζd r s h : ℂ)
      let St : H → ℂ := fun h => fixedPointCount H (Omega F) h - 1
      let Ξ : Fin m → Fin d → H → ℂ := fun r s h => lam r s h * St h
      let Lin : Set (H → ℂ) := Set.range fun rs : Fin m × Fin d => lam rs.1 rs.2
      let Xi : Set (H → ℂ) := Set.range fun rs : Fin m × Fin d => Ξ rs.1 rs.2
      (∀ (r : Fin m) (s : Fin d) (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ),
        lam r s ⟨quotientClass F b m hm heven X (j : ZMod (2 * m)), σ₀ ^ k⟩ =
          ζm ^ (r.val * j) * ζd ^ (s.val * k)) ∧
      BlocksIrr H = Lin ∪ Xi ∪ PH ∪ Cusp ∧
      Disjoint Lin Xi ∧ Disjoint Lin PH ∧ Disjoint Lin Cusp ∧ Disjoint Xi PH ∧
      Disjoint Xi Cusp ∧ Disjoint PH Cusp ∧
      {h : H | (∀ r s, Ξ r s h = Ξ r s 1) ∧ ∀ ξ ∈ Cusp, ξ h = ξ 1} = {1} := by
  intro G H ι N q d u x h2 C act Stab I IsExt Θ ε Cusp IsReps Fam Par ΘP PH
  have hchar : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  have hq3 : 3 ≤ q := three_le_card hb
  have hq1 : (q : ℂ) - 1 ≠ 0 := by
    intro h0
    have h' : ((q : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      rw [Nat.cast_one]
      linear_combination h0
    have := Nat.cast_injective h'
    omega
  refine ⟨cyclicGenerator_pow_m F b m hm heven,
    fun σ X j => fieldAction_quotientClass F b m hm heven Sigma hSigma σ X j,
    fun σ X i k => rfl, fun σ => fieldAction_cyclicGenerator_pow_m σ,
    fun E _ _ basis y hy ψ hψ => cuspBase_eq basis hpodd hb y hy h2 hψ,
    cuspBase_ncard hpodd hb, fun σ τ θ => fieldTwist_mul hSigma σ τ θ,
    fun θ => fieldTwist_one hSigma θ, fun θ hθ σ => fieldTwist_mem_cuspBase hSigma hθ σ,
    fun θ σ => Iff.rfl, fun θ h => Iff.rfl, ?_, ?_, fun θ => Subgroup.card_mul_index _,
    fun θ hθ => exists_inertia_extension hSigma hθ.1, ?_,
    fun θ hθ χ hχ => (twist_clifford (hm := hm) (heven := heven) hSigma hθ.1 hχ.1 hχ.2).2.1,
    fun θ hθ χ hχ => (twist_clifford (hm := hm) (heven := heven) hSigma hθ.1 hχ.1 hχ.2).2.2.1,
    ?_, ?_, ?_,
    fun θ hθ χ hχ => (twist_clifford (hm := hm) (heven := heven) hSigma hθ.1 hχ.1
      hχ.2).2.2.2.2, ?_, ?_, ?_, ?_,
    ⟨aboveFamily_finite hSigma cuspBase, sum_sq_cuspFamily hSigma hpodd hb⟩, ?_,
    nonsquareMatrix_val F b,
    fun X j σ v w hv hw hwv => semilinearAction_projective F b m hm heven Sigma hSigma X j σ v w
      hv hw hwv,
    fun Rp hRp1 hRp => principalFamilyH_eq_of_reps hSigma hb hd Rp hRp1 hRp, ?_⟩
  ·
    intro θ hθ
    rw [characterInertiaSubgroup_layer hSigma (classFunction_of_blocksIrr hθ.1)]
    rfl
  ·
    intro θ
    have hcyc : IsCyclic (Stab θ) := by
      have : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
      infer_instance
    let _ : CommGroup (Stab θ) := IsCyclic.commGroup
    exact card_hom_units_of_isCyclic (Stab θ)
  ·
    intro θ hθ χ hχ ρ
    obtain ⟨h1, h1'⟩ := (twist_clifford (hm := hm) (heven := heven) hSigma hθ.1 hχ.1 hχ.2).1 ρ
    exact ⟨h1, h1'.trans (by rw [hθ.2])⟩
  ·
    obtain ⟨R, hRC, hR⟩ := exists_twist_reps hSigma
      (fun θ hθ σ => fieldTwist_mem_cuspBase (hm := hm) (heven := heven) hSigma hθ σ)
    choose! ext hext using fun θ (hθ : θ ∈ C) => exists_inertia_extension hSigma hθ.1
    exact ⟨R, ext, ⟨hRC, hR⟩, fun θ hθR => hext θ (hRC hθR)⟩
  ·
    intro R ext hR hext
    exact ⟨repFamily_eq_aboveFamily hSigma (fun θ hθ => hθ.1) hR.1
        (fun θ hθ => (hR.2 θ hθ).exists) ext hext,
      fun θ hθ θ' hθ' ρ ρ' h => repFamily_rep_eq hSigma (fun θ hθ => hθ.1) hR.1 hR.2 ext hext
        hθ hθ' ρ ρ' h⟩
  ·
    intro θ hθ χ hχ T hT
    obtain ⟨hsum, hdist, hmult⟩ :=
      (twist_clifford (hm := hm) (heven := heven) hSigma hθ.1 hχ.1 hχ.2).2.2.2.1 T hT
    refine ⟨hsum, hdist, fun σ => ?_, hmult⟩
    obtain ⟨σ', ⟨hσ'T, hσ'⟩, -⟩ := hT (σ : Sigma ⧸ Stab θ)
    refine ⟨σ', hσ'T, ?_⟩
    have hmem : fieldTwist hSigma (σ'⁻¹ * σ) θ = θ := QuotientGroup.eq.mp hσ'
    show fieldTwist hSigma σ θ = fieldTwist hSigma σ' θ
    calc fieldTwist hSigma σ θ = fieldTwist hSigma (σ' * (σ'⁻¹ * σ)) θ := by
          rw [mul_inv_cancel_left]
      _ = fieldTwist hSigma σ' (fieldTwist hSigma (σ'⁻¹ * σ) θ) := fieldTwist_mul hSigma _ _ θ
      _ = fieldTwist hSigma σ' θ := by rw [hmem]
  ·
    intro θ hθ
    rcases cuspBase_x (hm := hm) (heven := heven) hpodd hb hθ with h | h
    · left
      show θ (cyclicGenerator F b m hm heven ^ m) / ((Nat.card F : ℂ) - 1) = 1
      rw [h, div_self hq1]
    · right
      show θ (cyclicGenerator F b m hm heven ^ m) / ((Nat.card F : ℂ) - 1) = -1
      rw [h, neg_div, div_self hq1]
  ·
    intro θ hθ σ
    show fieldTwist hSigma σ θ (cyclicGenerator F b m hm heven ^ m) / ((Nat.card F : ℂ) - 1) =
      θ (cyclicGenerator F b m hm heven ^ m) / ((Nat.card F : ℂ) - 1)
    rw [fieldTwist_apply, fieldAction_cyclicGenerator_pow_m]
  ·
    intro θ hθ χ hχ ρ
    show twistInduced hSigma θ χ ρ (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m)) =
      ((twistStabilizer hSigma θ).index : ℂ) * ((Nat.card F : ℂ) - 1) *
        (θ (cyclicGenerator F b m hm heven ^ m) / ((Nat.card F : ℂ) - 1))
    rw [twistInduced_x hSigma hθ.1 hχ.1 hχ.2, mul_assoc, mul_div_cancel₀ _ hq1]
  ·
    obtain ⟨θ, hθ, hx⟩ := exists_cuspBase_x_neg (hm := hm) (heven := heven) hpodd hb
    refine ⟨θ, hθ, ?_⟩
    show θ (cyclicGenerator F b m hm heven ^ m) / ((Nat.card F : ℂ) - 1) = -1
    rw [hx, neg_div, div_self hq1]
  ·
    have h1 : Nat.card H = Nat.card G * d := SemidirectProduct.card
    have hG : Nat.card G = m * q * (q ^ 2 - 1) := card_centralExtension_eq
    rw [h1, hG]
    ring
  ·
    intro σ₀ hgen ζm ζd hζm hζd lam St Ξ Lin Xi
    obtain ⟨hall, D12, D13, D14, D23, D24, D34⟩ :=
      semilinear_complete_family hSigma σ₀ hgen ζm ζd hζm hζd hpodd hb hd
    exact ⟨fun r s X j k => linearCharacter_formula F b m hm heven Sigma hSigma σ₀ hgen ζm ζd
        hζm hζd r s X j k, hall, D12, D13, D14, D23, D24, D34,
      semilinear_common_kernel hSigma σ₀ hgen ζm ζd hζm hζd hpodd hb⟩

end CFSG.Wreathed.CentralSL2
