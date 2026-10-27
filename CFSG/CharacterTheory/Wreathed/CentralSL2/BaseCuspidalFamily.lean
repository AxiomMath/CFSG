module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.CompleteFamily

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Fixed

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

omit [Fintype F] in
theorem eq_linearRestrict_iff (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) (r : ℕ) :
    lam = linearRestrict hm ζ hζ r ↔ ∀ t : nonsplitTorus F b m hm heven E basis,
      (lam t : ℂ) = (rootCharacter m hm ζ hζ r (baseResidue F b m hm heven t) : ℂ) := by
  constructor
  · rintro rfl t
    rfl
  · intro h
    exact MonoidHom.ext fun t => Units.ext (h t)

theorem minusWeyl_fixed_iff_existsUnique (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ m) (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    lam.comp (minusWeylConj h2 y hy) = lam ↔ ∃! r : Fin m,
      ∀ t : nonsplitTorus F b m hm heven E basis,
        (lam t : ℂ) = (rootCharacter m hm ζ hζ r.val (baseResidue F b m hm heven t) : ℂ) := by
  rw [minusWeyl_fixed_iff_linear hb y hy h2 ζ hζ lam]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, (eq_linearRestrict_iff ζ hζ lam r.val).mp hr, fun s hs => ?_⟩
    have hs' := (eq_linearRestrict_iff ζ hζ lam s.val).mpr hs
    exact linearRestrict_injective (basis := basis) (heven := heven) ζ hζ (hs'.symm.trans hr)
  · rintro ⟨r, hr, -⟩
    exact ⟨r, (eq_linearRestrict_iff ζ hζ lam r.val).mpr hr⟩

end Fixed

theorem base_cuspidal_characters_and_complete_family {F : Type} [Field F] [Fintype F]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (_hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (b : Fˣ) (hb : ¬ IsSquare b) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E)
    (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    let h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
    let G := CentralExtension F b m hm heven
    let u := cyclicGenerator F b m hm heven
    let a := u ^ 2
    let x := u ^ m
    let A := Subgroup.zpowers a
    let q := Nat.card F
    let κ := projectiveMap F b m hm heven
    let U := unipotentElement F b m hm heven
    let Usub := unipotentSubgroup F b m hm heven
    let Tplus := splitTorus F b m hm heven
    let Tminus := nonsplitTorus F b m hm heven E basis
    let wplus := weylElement F b m hm heven
    let wminus := nonsplitWeyl F b m hm heven E basis h2 y hy
    let B := borelSubgroup F b m hm heven
    let C : E → Matrix (Fin 2) (Fin 2) F := fun t => Algebra.leftMulMatrix basis t
    let S₀ := LinearMap.toMatrix basis basis (FiniteField.frobeniusAlgHom F E).toLinearMap
    let AU := auSubgroup F b m hm heven
    let wm : (Tminus →* ℂˣ) → (Tminus →* ℂˣ) := fun lam => lam.comp (minusWeylConj h2 y hy)
    let wp : (Tplus →* ℂˣ) → (Tplus →* ℂˣ) := fun θ => θ.comp (weylConj F b m hm heven)
    let Γ : AddChar F ℂ → (A →* ℂˣ) → G → ℂ := fun ψ' ξ =>
      inducedFunction AU fun g => auCharacter hb ξ ψ' g
    let Λ' : AddChar F ℂ → (Tminus →* ℂˣ) → G → ℂ := fun ψ' lam =>
      Γ ψ' (restrictA hb lam) - inducedFunction Tminus fun t => (lam t : ℂ)
    let Λ := Λ' ψ
    let St : G → ℂ := fun g => fixedPointCount G (Omega F) g - 1
    let χ : ℕ → G → ℂ := fun r g =>
      (rootCharacter m hm ζ hζ r (baseResidue F b m hm heven g) : ℂ)
    let Ψ : (Tplus →* ℂˣ) → G → ℂ := fun θ =>
      inducedFunction B fun g => (θ (borelProjection F b m hm heven g) : ℂ)
    let xT : Tminus := ⟨x, cyclicGenerator_pow_m_mem_nonsplitTorus h2⟩
    let Fam1 : Set (G → ℂ) := Set.range fun r : Fin m => χ r
    let Fam2 : Set (G → ℂ) := Set.range fun (r : Fin m) (g : G) => χ r g * St g
    let Fam3 : Set (G → ℂ) := Ψ '' {θ | wp θ ≠ θ}
    let Fam4 : Set (G → ℂ) := Λ '' {lam | wm lam ≠ lam}
    x = specialInclusion F b m hm heven (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) ∧
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)),
      κ (quotientClass F b m hm heven X j) =
        ProjGenLinGroup.mk (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val)) ∧
    (∀ (g : G) (M : GL (Fin 2) F), κ g = ProjGenLinGroup.mk M →
      ∀ p : Omega F, g • p = coordinateGLAction F M p) ∧
    (∀ t : F, U t = specialInclusion F b m hm heven (upperSL F t) ∧
      (upperSL F t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) ∧
    (∀ g : G, g ∈ Usub ↔ ∃ t : F, g = U t) ∧
    (∀ t : E, FiniteField.frobeniusAlgHom F E t = t ^ q) ∧
    (∀ s : Eˣ, ((mulGL F E basis s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = C s) ∧
    (∀ g : G, g ∈ Tminus ↔ ∃ s : Eˣ, ProjGenLinGroup.mk (mulGL F E basis s) = κ g) ∧
    wminus = specialInclusion F b m hm heven (wMatrix F E basis h2 y hy) ∧
    ((wMatrix F E basis h2 y hy : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = C y * S₀ ∧
    (∀ c d : Fˣ, ((diagGL F (c, d) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      diagonal ![(c : F), (d : F)]) ∧
    (∀ g : G, g ∈ Tplus ↔ ∃ c d : Fˣ, ProjGenLinGroup.mk (diagGL F (c, d)) = κ g) ∧
    wplus = specialInclusion F b m hm heven (weyl F) ∧
    (weyl F : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] ∧
    (∀ g : G, g ∈ B ↔ ∃ M : GL (Fin 2) F, (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ProjGenLinGroup.mk M = κ g) ∧
    (∀ t : Tminus, (minusWeylConj h2 y hy t : G) = wminus⁻¹ * t * wminus) ∧
    (∀ t : Tplus, (weylConj F b m hm heven t : G) = wplus⁻¹ * t * wplus) ∧
    Function.Surjective (borelProjection F b m hm heven) ∧
    (∀ g : B, borelProjection F b m hm heven g = 1 ↔ (g : G) ∈ Usub) ∧
    (∀ (g : B) (t : Tplus), (g : G) * (t : G)⁻¹ ∈ Usub → borelProjection F b m hm heven g = t) ∧
    (∃ ψ' : AddChar F ℂ, ψ' ≠ 1) ∧
    AU = A ⊔ Usub ∧ A ⊓ Usub = ⊥ ∧ (∀ α ∈ A, ∀ n ∈ Usub, α * n = n * α) ∧
    (∃ e : A × Usub ≃* AU, ∀ pr, (e pr : G) = pr.1 * pr.2) ∧
    (∀ g : G, g ∈ AU ↔ ∃ α ∈ A, ∃ t : F, g = α * U t) ∧
    (∀ (ψ' : AddChar F ℂ) (ξ : A →* ℂˣ) (α : A) (t : F),
      auCharacter hb ξ ψ' ⟨α * U t, alpha_mul_unipotent_mem_au α.2 t⟩ = (ξ α : ℂ) * ψ' t) ∧
    (∀ (lam : Tminus →* ℂˣ) (α : A),
      restrictA hb lam α = lam ⟨α, zpowers_le_nonsplitTorus hb α.2⟩) ∧
    (∀ lam, Λ lam ∈ BlocksVChar G) ∧
    (∀ ψ' : AddChar F ℂ, ψ' ≠ 1 → Λ' ψ' = Λ) ∧
    (∀ lam (α : A), Λ lam α = ((q : ℂ) - 1) * (restrictA hb lam α : ℂ)) ∧
    (∀ lam (α : A) (t : F), t ≠ 0 → Λ lam (α * U t) = -(restrictA hb lam α : ℂ)) ∧
    (∀ lam (t : G), t ∈ Tplus → t ∉ A → Λ lam t = 0) ∧
    (∀ lam (t : Tminus), (t : G) ∉ A → Λ lam t = -(lam t : ℂ) - (wm lam t : ℂ)) ∧
    (∀ lam μ, BlocksInnerProduct (Λ lam) (Λ μ) =
      (if lam = μ then 1 else 0) + (if lam = wm μ then 1 else 0)) ∧
    (∀ lam, wm lam ≠ lam → Λ lam ∈ BlocksIrr G ∧ Λ lam 1 = (q : ℂ) - 1) ∧
    (∀ lam μ, wm lam ≠ lam → wm μ ≠ μ → (Λ lam = Λ μ ↔ μ = lam ∨ μ = wm lam)) ∧
    Set.ncard Fam4 = m * q / 2 ∧
    (∀ lam, Λ lam x = ((q : ℂ) - 1) * (lam xT : ℂ)) ∧
    (∃ lam, wm lam ≠ lam ∧ (lam xT : ℂ) = -1) ∧
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (r : ℕ),
      χ r (quotientClass F b m hm heven X j) = ζ ^ (r * j.val)) ∧
    (∀ lam, wm lam = lam ↔ ∃! r : Fin m, ∀ t : Tminus, (lam t : ℂ) = χ r t) ∧
    (∀ lam (r : Fin m), (∀ t : Tminus, (lam t : ℂ) = χ r t) →
      Λ lam = fun g => χ r g * (St g - 1)) ∧
    (∀ r : Fin m, χ r ∈ BlocksIrr G ∧ χ r 1 = 1) ∧
    (∀ r : Fin m, (fun g => χ r g * St g) ∈ BlocksIrr G ∧ χ r 1 * St 1 = q) ∧
    (∀ θ, wp θ ≠ θ → Ψ θ ∈ BlocksIrr G ∧ Ψ θ 1 = (q : ℂ) + 1) ∧
    Function.Injective (fun r : Fin m => χ r) ∧
    Function.Injective (fun (r : Fin m) (g : G) => χ r g * St g) ∧
    (∀ θ θ', wp θ ≠ θ → wp θ' ≠ θ' → (Ψ θ = Ψ θ' ↔ θ' = θ ∨ θ' = wp θ)) ∧
    Set.ncard Fam1 = m ∧ Set.ncard Fam2 = m ∧ Set.ncard Fam3 = m * (q - 2) / 2 ∧
    BlocksIrr G = Fam1 ∪ Fam2 ∪ Fam3 ∪ Fam4 ∧
    Disjoint Fam1 Fam2 ∧ Disjoint Fam1 Fam3 ∧ Disjoint Fam1 Fam4 ∧ Disjoint Fam2 Fam3 ∧
    Disjoint Fam2 Fam4 ∧ Disjoint Fam3 Fam4 ∧
    m * 1 ^ 2 + m * q ^ 2 + m * (q - 2) / 2 * (q + 1) ^ 2 + m * q / 2 * (q - 1) ^ 2 =
      m * q * (q ^ 2 - 1) ∧
    Nat.card G = m * q * (q ^ 2 - 1) := by
  intro h2 G u a x A q κ U Usub Tplus Tminus wplus wminus B C S₀ AU wm wp Γ Λ' Λ St χ Ψ xT
    Fam1 Fam2 Fam3 Fam4
  have hchar : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  have hq3 : 3 ≤ q := three_le_card hb
  have hfam := blocksIrr_eq_families (basis := basis) (hm := hm) (heven := heven) hpodd hb y hy
    h2 hψ ζ hζ
  refine ⟨cyclicGenerator_pow_m F b m hm heven, projectiveMap_quotientClass F b m hm heven,
    fun g M hM p => smul_eq_coordinateGLAction hM p, fun t => ⟨rfl, rfl⟩, ?_,
    frobeniusAlgHom_apply' F E, fun s => rfl, mem_nonsplitTorus_iff, rfl, rfl, fun c d => rfl,
    ?_, rfl, rfl, mem_borelSubgroup_iff_upper, minusWeylConj_apply h2 y hy,
    weylConj_apply F b m hm heven, borelProjection_surjective F b m hm heven, ?_, ?_,
    exists_addChar_ne_one, rfl, zpowers_inf_unipotentSubgroup,
    fun α hα n _ => cyclicGenerator_sq_zpowers_comm hα n,
    ⟨MulEquiv.ofBijective auProductHom (auProductHom_bijective hb), fun pr => rfl⟩,
    mem_auSubgroup_iff hb, fun ψ' ξ α t => auCharacter_apply hb ξ ψ' α t,
    fun lam α => restrictA_apply hb lam α,
    fun lam => cuspidalCharacter_mem_blocksVChar hb ψ lam,
    fun ψ' hψ' => funext fun lam => (cuspidalCharacter_indep hpodd hb hψ hψ' lam).symm,
    fun lam α => cuspidalCharacter_central hb ψ lam α,
    fun lam α t ht => cuspidalCharacter_unipotent hpodd hb hψ lam α ht,
    fun lam t ht htA => cuspidalCharacter_split hb ψ lam ht htA,
    fun lam t htA => cuspidalCharacter_nonsplit hb y hy h2 ψ lam htA,
    fun lam μ => inner_cuspidal hpodd hb y hy h2 hψ lam μ,
    fun lam hlam => ⟨cuspidalCharacter_mem_blocksIrr hpodd hb y hy h2 hψ lam hlam,
      cuspidalCharacter_one hb ψ lam⟩,
    fun lam μ hlam _ => cuspidalCharacter_eq_iff hpodd hb y hy h2 hψ hlam,
    cuspidalCharacter_ncard hpodd hb y hy h2 hψ, fun lam => cuspidalCharacter_x hb ψ lam,
    exists_nonfixed_x_eq_neg_one hb y hy h2,
    fun X j r => rootCharacter_baseResidue_quotientClass F b m hm heven ζ hζ r X j,
    fun lam => minusWeyl_fixed_iff_existsUnique hb y hy h2 ζ hζ lam, ?_, ?_, ?_,
    fun θ hθ => ⟨principalSeries_mem_blocksIrr' θ hθ, principalSeries_one F b m hm heven θ⟩,
    linearCharacter_injective ζ hζ, linearSteinberg_injective hb ζ hζ,
    fun θ θ' hθ _ => principalSeries_eq_iff' hθ, linearFamily_ncard ζ hζ,
    steinbergFamily_ncard hb ζ hζ, principalSeries_ncard' hb, hfam.1, hfam.2.1, hfam.2.2.1,
    hfam.2.2.2.1, hfam.2.2.2.2.1, hfam.2.2.2.2.2.1, hfam.2.2.2.2.2.2,
    degree_square_sum_identity m q heven hq3, card_centralExtension_eq⟩
  · intro g
    rw [mem_unipotentSubgroup_iff]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
  · intro g
    show g ∈ splitTorus F b m hm heven ↔ _
    rw [splitTorus_eq_comap, Subgroup.mem_comap, projectiveDiagonal, MonoidHom.mem_range]
    constructor
    · rintro ⟨⟨c, d⟩, h⟩
      exact ⟨c, d, h⟩
    · rintro ⟨c, d, h⟩
      exact ⟨(c, d), h⟩
  · intro g
    constructor
    · intro hg1
      have h1 : borelProjectionFun F b m hm heven g = 1 := congrArg Subtype.val hg1
      rw [← unipotentElement_mul_borelProjectionFun F b m hm heven g, h1, mul_one]
      exact (mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨_, rfl⟩
    · intro hg
      exact borelProjection_of_mem_unipotent F b m hm heven g hg
  · intro g t hgt
    exact borelProjection_eq F b m hm heven g hgt t.2 (inv_mul_cancel_right _ _).symm
  · intro lam r hr
    have hlam := (eq_linearRestrict_iff ζ hζ lam r.val).mpr hr
    rw [hlam]
    exact cuspidalCharacter_linearRestrict hb ζ hζ hpodd hψ r.val
  · intro r
    exact ⟨monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp (linearCharacter hm ζ hζ r.val)),
      by simp [χ]⟩
  · intro r
    refine ⟨linearTwist_mem_blocksIrr (linearCharacter hm ζ hζ r.val)
      (steinberg_mem_blocksIrr F b m hm heven), ?_⟩
    have h1 : χ r 1 = 1 := by simp [χ]
    rw [h1, one_mul]
    change fixedPointCount G (Omega F) 1 - 1 = _
    rw [fixedPointCount_one]
    ring

end CFSG.Wreathed.CentralSL2
