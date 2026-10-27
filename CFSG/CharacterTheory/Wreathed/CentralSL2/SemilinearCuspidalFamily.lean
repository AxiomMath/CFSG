module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearTwistSum

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Arithmetic

theorem degree_square_sum_identity_H (m q d : ℕ) (heven : Even m) (hq : 3 ≤ q) :
    m * d * 1 ^ 2 + m * d * q ^ 2 + d * m * (q - 2) * (q + 1) ^ 2 / 2 +
      d * m * q * (q - 1) ^ 2 / 2 = m * q * (q ^ 2 - 1) * d := by
  obtain ⟨k, rfl⟩ := heven
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
  have e1 : d * (k + k) * (r + 3 - 2) * (r + 3 + 1) ^ 2 / 2 =
      d * k * (r + 1) * (r + 4) ^ 2 := by
    rw [show d * (k + k) * (r + 3 - 2) * (r + 3 + 1) ^ 2 =
      2 * (d * k * (r + 1) * (r + 4) ^ 2) by
        rw [show r + 3 - 2 = r + 1 by omega]
        ring]
    exact Nat.mul_div_cancel_left _ two_pos
  have e2 : d * (k + k) * (r + 3) * (r + 3 - 1) ^ 2 / 2 = d * k * (r + 3) * (r + 2) ^ 2 := by
    rw [show d * (k + k) * (r + 3) * (r + 3 - 1) ^ 2 = 2 * (d * k * (r + 3) * (r + 2) ^ 2) by
        rw [show r + 3 - 1 = r + 2 by omega]
        ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [e1, e2, show (r + 3) ^ 2 - 1 = r ^ 2 + 6 * r + 8 from Nat.sub_eq_of_eq_add (by ring)]
  ring

theorem degree_separation {q s : ℕ} (hq : 3 ≤ q) (hs : 0 < s) :
    1 ≠ s * (q + 1) ∧ q ≠ s * (q + 1) ∧ 1 ≠ s * (q - 1) ∧ q ≠ s * (q - 1) := by
  have h1 := Nat.le_mul_of_pos_left (q + 1) hs
  have h2 := Nat.le_mul_of_pos_left (q - 1) hs
  refine ⟨by omega, by omega, by omega, fun h => ?_⟩
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · obtain rfl : s = 1 := by omega
    omega
  · have h3 := Nat.mul_le_mul_right (q - 1) hs2
    omega

theorem natCast_mul_sub_one {q s : ℕ} (hq : 1 ≤ q) :
    ((s * (q - 1) : ℕ) : ℂ) = (s : ℂ) * ((q : ℂ) - 1) := by
  push_cast [Nat.cast_sub hq]
  ring

end Arithmetic

section Base

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

@[expose] noncomputable def cuspBase : Set (CentralExtension F b m hm heven → ℂ) :=
  {θ | θ ∈ BlocksIrr (CentralExtension F b m hm heven) ∧ θ 1 = (Nat.card F : ℂ) - 1}

theorem cuspBase_finite : (cuspBase (F := F) (b := b) (hm := hm) (heven := heven)).Finite :=
  (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite _).subset fun _ h => h.1

theorem exists_cuspidal_data (hb : ¬ IsSquare b) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : Module.Basis (Fin 2) F E) (y : Eˣ),
      (y : E) * (y : E) ^ Nat.card F = -1 := by
  obtain ⟨E, _, _, ⟨basis⟩⟩ := exists_quadratic_extension F b hb
  obtain ⟨y, hy⟩ := exists_norm_eq F E basis (-1)
  exact ⟨E, inferInstance, inferInstance, basis, y, by rw [hy]; simp⟩

theorem cuspBase_eq {E : Type} [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E)
    {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) :
    cuspBase (F := F) (b := b) (hm := hm) (heven := heven) =
      (fun lam => cuspidalCharacter hb ψ lam) ''
        {lam : nonsplitTorus F b m hm heven E basis →* ℂˣ |
          lam.comp (minusWeylConj h2 y hy) ≠ lam} := by
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  obtain ⟨hall, -⟩ := blocksIrr_eq_families (basis := basis) (hm := hm) (heven := heven) hpodd
    hb y hy h2 hψ _ hζ
  have hq3 := three_le_card (F := F) hb
  ext θ
  constructor
  · rintro ⟨hθ, hdeg⟩
    rw [hall] at hθ
    rcases hθ with ((hθ | hθ) | hθ) | hθ
    · rw [linearFamily_degree _ hζ θ hθ] at hdeg
      have h : ((2 : ℕ) : ℂ) = ((Nat.card F : ℕ) : ℂ) := by
        push_cast
        linear_combination hdeg
      have := Nat.cast_injective h
      omega
    · rw [steinbergFamily_degree _ hζ θ hθ] at hdeg
      have h : (1 : ℂ) = 0 := by linear_combination hdeg
      exact absurd h one_ne_zero
    · rw [principalFamily_degree θ hθ] at hdeg
      have h : (2 : ℂ) = 0 := by linear_combination hdeg
      exact absurd h two_ne_zero
    · exact hθ
  · rintro ⟨lam, hlam, rfl⟩
    exact ⟨cuspidalCharacter_mem_blocksIrr hpodd hb y hy h2 hψ lam hlam,
      cuspidalCharacter_one hb ψ lam⟩

theorem cuspBase_ncard {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b) :
    (cuspBase (F := F) (b := b) (hm := hm) (heven := heven)).ncard = m * Nat.card F / 2 := by
  obtain ⟨E, _, _, basis, y, hy⟩ := exists_cuspidal_data (F := F) hb
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one (F := F)
  have h2 := two_ne_zero_of_not_isSquare hb
  rw [cuspBase_eq basis hpodd hb y hy h2 hψ]
  exact cuspidalCharacter_ncard hpodd hb y hy h2 hψ

theorem cuspBase_x {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b)
    {θ : CentralExtension F b m hm heven → ℂ} (hθ : θ ∈ cuspBase) :
    θ (cyclicGenerator F b m hm heven ^ m) = (Nat.card F : ℂ) - 1 ∨
      θ (cyclicGenerator F b m hm heven ^ m) = -((Nat.card F : ℂ) - 1) := by
  obtain ⟨E, _, _, basis, y, hy⟩ := exists_cuspidal_data (F := F) hb
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one (F := F)
  have h2 := two_ne_zero_of_not_isSquare hb
  rw [cuspBase_eq basis hpodd hb y hy h2 hψ] at hθ
  obtain ⟨lam, -, rfl⟩ := hθ
  beta_reduce
  rw [cuspidalCharacter_x hb ψ lam]
  have key : ∀ t : nonsplitTorus F b m hm heven E basis,
      (t : CentralExtension F b m hm heven) ^ 2 = 1 → ((lam t : ℂˣ) : ℂ) ^ 2 = 1 := by
    intro t ht
    have ht' : t ^ 2 = 1 := Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact ht)
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ht', map_one, Units.val_one]
  have hx2 : (cyclicGenerator F b m hm heven ^ m) ^ 2 = 1 := by
    rw [sq]
    exact cyclicGenerator_pow_m_mul_self
  have hsq := key ⟨cyclicGenerator F b m hm heven ^ m,
    zpowers_le_nonsplitTorus hb cyclicGenerator_pow_m_mem_zpowers⟩ hx2
  rcases sq_eq_one_iff.mp hsq with h | h
  · left
    rw [h, mul_one]
  · right
    rw [h]
    ring

theorem exists_cuspBase_x_neg {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b) :
    ∃ θ ∈ cuspBase (F := F) (b := b) (hm := hm) (heven := heven),
      θ (cyclicGenerator F b m hm heven ^ m) = -((Nat.card F : ℂ) - 1) := by
  obtain ⟨E, _, _, basis, y, hy⟩ := exists_cuspidal_data (F := F) hb
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one (F := F)
  have h2 := two_ne_zero_of_not_isSquare hb
  obtain ⟨lam, hlam, hx⟩ := exists_nonfixed_x_eq_neg_one (hm := hm) (heven := heven)
    (basis := basis) hb y hy h2
  refine ⟨cuspidalCharacter hb ψ lam, ?_, ?_⟩
  · rw [cuspBase_eq basis hpodd hb y hy h2 hψ]
    exact ⟨lam, hlam, rfl⟩
  · rw [cuspidalCharacter_x hb ψ lam, hx]
    ring

variable {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

omit [Fintype F] in
theorem fieldTwist_mem_cuspBase {θ : CentralExtension F b m hm heven → ℂ} (hθ : θ ∈ cuspBase)
    (σ : Sigma) : fieldTwist hSigma σ θ ∈ cuspBase :=
  ⟨fieldTwist_mem_blocksIrr hSigma hθ.1 σ, by rw [fieldTwist_apply_one]; exact hθ.2⟩

theorem sum_sq_cuspFamily {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b) :
    ∑ ξ ∈ (aboveFamily_finite (hm := hm) (heven := heven) hSigma cuspBase).toFinset, ξ 1 ^ 2 =
      ((Nat.card Sigma * m * Nat.card F * (Nat.card F - 1) ^ 2 / 2 : ℕ) : ℂ) := by
  set Pf := (cuspBase_finite (F := F) (b := b) (hm := hm) (heven := heven)).toFinset with hPf
  have hset : (↑Pf : Set (CentralExtension F b m hm heven → ℂ)) = cuspBase :=
    Set.Finite.coe_toFinset _
  have hirr : ∀ θ ∈ Pf, θ ∈ BlocksIrr (CentralExtension F b m hm heven) :=
    fun θ hθ => ((Set.Finite.mem_toFinset _).mp hθ).1
  have hdeg : ∀ θ ∈ Pf, θ 1 = (Nat.card F : ℂ) - 1 :=
    fun θ hθ => ((Set.Finite.mem_toFinset _).mp hθ).2
  have hstable : ∀ θ ∈ Pf, ∀ σ : Sigma, fieldTwist hSigma σ θ ∈ Pf :=
    fun θ hθ σ => (Set.Finite.mem_toFinset _).mpr
      (fieldTwist_mem_cuspBase hSigma ((Set.Finite.mem_toFinset _).mp hθ) σ)
  have h := sum_sq_aboveFamily hSigma Pf _ hirr hdeg hstable
  have hfs : (aboveFamily_finite (hm := hm) (heven := heven) hSigma cuspBase).toFinset =
      (aboveFamily_finite (hm := hm) (heven := heven) hSigma ↑Pf).toFinset := by
    ext ξ
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, hset]
  rw [hfs, h]
  have hcard : Pf.card = m * Nat.card F / 2 := by
    rw [hPf, ← Set.ncard_eq_toFinset_card _ cuspBase_finite]
    exact cuspBase_ncard hpodd hb
  rw [hcard]
  have hq : 1 ≤ Nat.card F := by
    have := two_le_card F
    omega
  obtain ⟨k, hk⟩ := heven
  have e1 : m * Nat.card F / 2 = k * Nat.card F := by
    rw [hk, show (k + k) * Nat.card F = 2 * (k * Nat.card F) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  have e2 : Nat.card Sigma * m * Nat.card F * (Nat.card F - 1) ^ 2 / 2 =
      Nat.card Sigma * k * Nat.card F * (Nat.card F - 1) ^ 2 := by
    rw [hk, show Nat.card Sigma * (k + k) * Nat.card F * (Nat.card F - 1) ^ 2 =
      2 * (Nat.card Sigma * k * Nat.card F * (Nat.card F - 1) ^ 2) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [e1, e2]
  push_cast [Nat.cast_sub hq]
  ring

end Base

section Choices

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

omit [Fintype F] in
theorem exists_twist_reps {Pf : Set (CentralExtension F b m hm heven → ℂ)}
    (hstable : ∀ θ ∈ Pf, ∀ σ : Sigma, fieldTwist hSigma σ θ ∈ Pf) :
    ∃ R ⊆ Pf, ∀ θ ∈ Pf, ∃! θ', θ' ∈ R ∧ ∃ σ : Sigma, θ = fieldTwist hSigma σ θ' := by
  let s : Setoid (CentralExtension F b m hm heven → ℂ) :=
    { r := fun θ θ' => ∃ σ : Sigma, θ' = fieldTwist hSigma σ θ
      iseqv := ⟨fun θ => ⟨1, (fieldTwist_one hSigma θ).symm⟩,
        fun {θ θ'} ⟨σ, h⟩ => ⟨σ⁻¹, by rw [h, ← fieldTwist_mul, inv_mul_cancel, fieldTwist_one]⟩,
        fun {θ θ' θ''} ⟨σ, h⟩ ⟨τ, h'⟩ => ⟨τ * σ, by rw [h', h, fieldTwist_mul]⟩⟩ }
  have hout : ∀ θ, ∃ σ : Sigma, θ = fieldTwist hSigma σ (Quotient.mk s θ).out :=
    fun θ => Quotient.mk_out (s := s) θ
  refine ⟨(fun θ => (Quotient.mk s θ).out) '' Pf, ?_, fun θ hθ => ?_⟩
  · rintro _ ⟨θ, hθ, rfl⟩
    obtain ⟨σ, hσ⟩ := hout θ
    have h1 : (Quotient.mk s θ).out = fieldTwist hSigma σ⁻¹ θ := by
      rw [hσ, ← fieldTwist_mul, inv_mul_cancel, fieldTwist_one, ← hσ]
    show (Quotient.mk s θ).out ∈ Pf
    rw [h1]
    exact hstable θ hθ σ⁻¹
  · refine ⟨(Quotient.mk s θ).out, ⟨⟨θ, hθ, rfl⟩, hout θ⟩, ?_⟩
    rintro _ ⟨⟨θ₂, -, rfl⟩, τ, hτ⟩
    have hq : Quotient.mk s θ₂ = Quotient.mk s θ := by
      apply Quotient.sound
      obtain ⟨σ, hσ⟩ := hout θ₂
      exact ⟨τ * σ⁻¹, by rw [hτ, fieldTwist_mul, hσ, ← fieldTwist_mul hSigma σ⁻¹,
        inv_mul_cancel, fieldTwist_one, ← hσ]⟩
    show (Quotient.mk s θ₂).out = _
    rw [hq]

theorem principalFamilyH_eq_of_reps (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    (Rp : Set (PrincipalSeriesParameter F b m)) (hRp1 : ∀ P ∈ Rp, P.1.1 ≠ 1)
    (hRp : ∀ P : PrincipalSeriesParameter F b m, P.1.1 ≠ 1 → ∃ P' ∈ Rp, ∃ σ : Sigma,
      P = fieldParameter hSigma σ P' ∨
        P = fieldParameter hSigma σ (weylParameter F b m heven P')) :
    {χ | ∃ P ∈ Rp, ∃ ρ : parameterStabilizer hSigma P →* ℂˣ,
      χ = principalInduced (hm := hm) (heven := heven) hSigma P ρ} = principalFamilyH hSigma := by
  ext χ
  constructor
  · rintro ⟨P, hP, ρ, rfl⟩
    exact ⟨P, ρ, hRp1 P hP, rfl⟩
  · rintro ⟨P, ρ, hP, rfl⟩
    obtain ⟨P', hP', σ, hσ⟩ := hRp P hP
    have hP'1 := hRp1 P' hP'
    rcases hσ with rfl | rfl
    · have hstab : parameterStabilizer hSigma P' =
          parameterStabilizer hSigma (fieldParameter hSigma σ P') :=
        (parameterStabilizer_fieldParameter hSigma σ P').symm
      refine ⟨P', hP', ρ.comp (MulEquiv.subgroupCongr hstab).toMonoidHom, ?_⟩
      refine (principalInduced_eq_iff hSigma hb hd hP hP'1 ρ _).mpr
        ⟨⟨σ⁻¹, Or.inl ?_⟩, fun τ h₁ h₂ => rfl⟩
      rw [← fieldParameter_mul, inv_mul_cancel, fieldParameter_one]
    · have hstab : parameterStabilizer hSigma P' = parameterStabilizer hSigma
          (fieldParameter hSigma σ (weylParameter F b m heven P')) := by
        rw [parameterStabilizer_fieldParameter, parameterStabilizer_weylParameter]
      refine ⟨P', hP', ρ.comp (MulEquiv.subgroupCongr hstab).toMonoidHom, ?_⟩
      refine (principalInduced_eq_iff hSigma hb hd hP hP'1 ρ _).mpr
        ⟨⟨σ⁻¹, Or.inr ?_⟩, fun τ h₁ h₂ => rfl⟩
      rw [← fieldParameter_weylParameter, ← fieldParameter_mul, inv_mul_cancel,
        fieldParameter_one, weylParameter_involutive]

end Choices

section Complete

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
  (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ)
  (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd (Nat.card Sigma))

@[expose] noncomputable def linearFamilyH :
    Set (SemilinearExtension F b m hm heven Sigma hSigma → ℂ) :=
  Set.range fun rs : Fin m × Fin (Nat.card Sigma) => fun h =>
    (CentralSL2Abelianization.linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd
      rs.1 rs.2 h : ℂ)

@[expose] noncomputable def steinbergFamilyH :
    Set (SemilinearExtension F b m hm heven Sigma hSigma → ℂ) :=
  Set.range fun rs : Fin m × Fin (Nat.card Sigma) => fun h =>
    (CentralSL2Abelianization.linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd
      rs.1 rs.2 h : ℂ) *
      (fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h - 1)

theorem linearFamilyH_ncard :
    (linearFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd).ncard =
      m * Nat.card Sigma := by
  rw [linearFamilyH, Set.ncard_range_of_injective (linearCharacter_values_injective F b m hm
    heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd), Nat.card_prod, Nat.card_fin, Nat.card_fin]

theorem steinbergFamilyH_spec (hb : ¬ IsSquare b) :
    (∀ ξ ∈ steinbergFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd,
      ξ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) ∧
        ξ 1 = Nat.card F) ∧
    (steinbergFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd).ncard =
      m * Nat.card Sigma := by
  obtain ⟨hirr, hinj, -, -⟩ := augmentation_twists F b m hm heven Sigma hSigma
    (nonsquare_ne_one F b hb) σ₀ hgen ζm ζd hζm hζd
  refine ⟨?_, ?_⟩
  · rintro ξ ⟨rs, rfl⟩
    exact hirr rs.1 rs.2
  · rw [steinbergFamilyH, Set.ncard_range_of_injective hinj, Nat.card_prod, Nat.card_fin,
      Nat.card_fin]

theorem semilinear_complete_family {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b)
    (hd : Odd (Nat.card Sigma)) :
    BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) =
      linearFamilyH hSigma σ₀ hgen ζm ζd hζm hζd ∪
        steinbergFamilyH hSigma σ₀ hgen ζm ζd hζm hζd ∪ principalFamilyH hSigma ∪
        aboveFamily hSigma cuspBase ∧
    Disjoint (linearFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd)
      (steinbergFamilyH hSigma σ₀ hgen ζm ζd hζm hζd) ∧
    Disjoint (linearFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd)
      (principalFamilyH hSigma) ∧
    Disjoint (linearFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd)
      (aboveFamily hSigma cuspBase) ∧
    Disjoint (steinbergFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd)
      (principalFamilyH hSigma) ∧
    Disjoint (steinbergFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd)
      (aboveFamily hSigma cuspBase) ∧
    Disjoint (principalFamilyH (hm := hm) (heven := heven) hSigma)
      (aboveFamily hSigma cuspBase) := by
  set F1 := linearFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd with hF1
  set F2 := steinbergFamilyH (hm := hm) (heven := heven) hSigma σ₀ hgen ζm ζd hζm hζd with hF2
  set F3 := principalFamilyH (hm := hm) (heven := heven) hSigma with hF3
  set F4 := aboveFamily (hm := hm) (heven := heven) hSigma cuspBase with hF4
  have hq3 := three_le_card (F := F) hb
  have h1q : 1 ≤ Nat.card F := by omega
  obtain ⟨hirr2, hcard2⟩ := steinbergFamilyH_spec (hm := hm) (heven := heven) hSigma σ₀ hgen ζm
    ζd hζm hζd hb
  have d1 : ∀ ξ ∈ F1, ξ 1 = 1 := by
    rintro ξ ⟨rs, rfl⟩
    simp only [map_one, Units.val_one]
  have d2 : ∀ ξ ∈ F2, ξ 1 = Nat.card F := fun ξ hξ => (hirr2 ξ hξ).2
  have d3 : ∀ ξ ∈ F3, ∃ s : ℕ, 0 < s ∧ ξ 1 = (s : ℂ) * ((Nat.card F : ℂ) + 1) := by
    rintro ξ ⟨P, ρ, hP, rfl⟩
    exact ⟨_, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite,
      ((principal_clifford hSigma hb hd hP).1 ρ).2⟩
  have d4 : ∀ ξ ∈ F4, ∃ s : ℕ, 0 < s ∧ ξ 1 = (s : ℂ) * ((Nat.card F : ℂ) - 1) := by
    intro ξ hξ
    obtain ⟨θ, hθ, hξ1⟩ := exists_degree_of_mem_aboveFamily hSigma (fun θ hθ => hθ.1) hξ
    exact ⟨_, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, by rw [hξ1, hθ.2]⟩
  have D12 : Disjoint F1 F2 := disjoint_of_degree d1 d2 (by
    intro h
    have h' : ((1 : ℕ) : ℂ) = ((Nat.card F : ℕ) : ℂ) := by rw [Nat.cast_one]; exact h
    have := Nat.cast_injective h'
    omega)
  have D13 : Disjoint F1 F3 := Set.disjoint_left.mpr fun ξ h1 h3 => by
    obtain ⟨s, hs, hξ⟩ := d3 ξ h3
    rw [d1 ξ h1] at hξ
    exact (degree_separation hq3 hs).1 (by exact_mod_cast hξ)
  have D14 : Disjoint F1 F4 := Set.disjoint_left.mpr fun ξ h1 h4 => by
    obtain ⟨s, hs, hξ⟩ := d4 ξ h4
    rw [d1 ξ h1] at hξ
    have h' : ((1 : ℕ) : ℂ) = ((s * (Nat.card F - 1) : ℕ) : ℂ) := by
      rw [natCast_mul_sub_one h1q, Nat.cast_one]
      exact hξ
    exact (degree_separation hq3 hs).2.2.1 (Nat.cast_injective h')
  have D23 : Disjoint F2 F3 := Set.disjoint_left.mpr fun ξ h2 h3 => by
    obtain ⟨s, hs, hξ⟩ := d3 ξ h3
    rw [d2 ξ h2] at hξ
    exact (degree_separation hq3 hs).2.1 (by exact_mod_cast hξ)
  have D24 : Disjoint F2 F4 := Set.disjoint_left.mpr fun ξ h2 h4 => by
    obtain ⟨s, hs, hξ⟩ := d4 ξ h4
    rw [d2 ξ h2] at hξ
    have h' : ((Nat.card F : ℕ) : ℂ) = ((s * (Nat.card F - 1) : ℕ) : ℂ) := by
      rw [natCast_mul_sub_one h1q]
      exact hξ
    exact (degree_separation hq3 hs).2.2.2 (Nat.cast_injective h')
  have D34 : Disjoint F3 F4 := Set.disjoint_left.mpr fun ξ h3 h4 => by
    obtain ⟨P, ρ, hP, rfl⟩ := h3
    have hcl := principal_clifford (hm := hm) (heven := heven) hSigma hb hd hP
    have hirr := (hcl.1 ρ).1
    have habove : liesAbove hSigma (principalInduced hSigma P ρ)
        (principalSeries F b m hm heven (torusCharacter F b m hm heven P)) :=
      (hcl.2.2.1 _ hirr).mpr ⟨ρ, rfl⟩
    refine not_liesAbove_of_degree_ne hSigma (fun θ hθ => hθ.1) (fun θ hθ => hθ.2) h4
      (principalSeries_mem_blocksIrr F b m hm heven hb P hP) ?_ habove
    rw [principalSeries_one]
    intro h
    have : (2 : ℂ) = 0 := by linear_combination h
    exact two_ne_zero this
  refine ⟨?_, D12, D13, D14, D23, D24, D34⟩
  have hfin1 : F1.Finite := Set.finite_range _
  have hfin2 : F2.Finite := Set.finite_range _
  have hfin3 : F3.Finite := principalFamilyH_finite hSigma hb hd
  have hfin4 : F4.Finite := aboveFamily_finite hSigma cuspBase
  set hfin := ((hfin1.union hfin2).union hfin3).union hfin4 with hfindef
  have hcoe : (hfin.toFinset : Set (SemilinearExtension F b m hm heven Sigma hSigma → ℂ)) =
      F1 ∪ F2 ∪ F3 ∪ F4 :=
    Set.Finite.coe_toFinset hfin
  rw [← hcoe]
  apply blocksIrr_eq_of_sum_sq
  · intro ξ hξ
    rw [Set.Finite.mem_toFinset] at hξ
    rcases hξ with ((hξ | hξ) | hξ) | hξ
    · obtain ⟨rs, rfl⟩ := hξ
      exact monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp
        (CentralSL2Abelianization.linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm
          hζd rs.1 rs.2))
    · exact (hirr2 ξ hξ).1
    · exact principalFamilyH_subset hSigma hb hd hξ
    · exact hξ.1
  · rw [sum_sq_union ((hfin1.union hfin2).union hfin3) hfin4 (Set.disjoint_union_left.mpr
        ⟨Set.disjoint_union_left.mpr ⟨D14, D24⟩, D34⟩),
      sum_sq_union (hfin1.union hfin2) hfin3 (Set.disjoint_union_left.mpr ⟨D13, D23⟩),
      sum_sq_union hfin1 hfin2 D12, sum_sq_of_const hfin1 d1, sum_sq_of_const hfin2 d2,
      linearFamilyH_ncard, hcard2, sum_sq_principalFamilyH hSigma hb hd,
      sum_sq_cuspFamily hSigma hpodd hb]
    have hH : Nat.card (SemilinearExtension F b m hm heven Sigma hSigma) =
        Nat.card (CentralExtension F b m hm heven) * Nat.card Sigma := SemidirectProduct.card
    rw [hH, card_centralExtension_eq,
      ← degree_square_sum_identity_H m (Nat.card F) (Nat.card Sigma) heven hq3]
    push_cast
    ring

theorem semilinear_common_kernel {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b) :
    {h : SemilinearExtension F b m hm heven Sigma hSigma |
      (∀ r s, (CentralSL2Abelianization.linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd
          hζm hζd r s h : ℂ) *
          (fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h - 1) =
        (CentralSL2Abelianization.linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm
          hζd r s 1 : ℂ) *
          (fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) 1 - 1)) ∧
      ∀ ξ ∈ aboveFamily hSigma cuspBase, ξ h = ξ 1} = {1} := by
  have h2 := two_ne_zero_of_not_isSquare hb
  have hker : {h : SemilinearExtension F b m hm heven Sigma hSigma |
      ∀ r s, (CentralSL2Abelianization.linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd
          hζm hζd r s h : ℂ) *
          (fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h - 1) =
        (CentralSL2Abelianization.linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm
          hζd r s 1 : ℂ) *
          (fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) 1 - 1)} =
      (Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) :
        SemilinearExtension F b m hm heven Sigma hSigma) : Set _) :=
    augmentation_common_kernel F b m hm heven Sigma hSigma h2 hb σ₀ hgen ζm ζd hζm hζd
  have hq3 := three_le_card (F := F) hb
  ext h
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hΞ, hcusp⟩
    have hmem : h ∈ (Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) :
        SemilinearExtension F b m hm heven Sigma hSigma) : Set _) := by
      rw [← hker]
      exact hΞ
    rcases (mem_zpowers_of_orderOf_two (orderOf_inl_cyclicGenerator_pow_m F b m hm heven Sigma
      hSigma h2) h).mp hmem with rfl | rfl
    · rfl
    · exfalso
      obtain ⟨θ, hθ, hθx⟩ := exists_cuspBase_x_neg (hm := hm) (heven := heven) hpodd hb
      obtain ⟨χ, hχ, hres⟩ := exists_inertia_extension (hm := hm) (heven := heven) hSigma hθ.1
      obtain ⟨hdeg, -, hiff, -, -⟩ := twist_clifford hSigma hθ.1 hχ hres
      have hmemξ : twistInduced hSigma θ χ 1 ∈ aboveFamily hSigma cuspBase :=
        ⟨(hdeg 1).1, θ, hθ, (hiff _ (hdeg 1).1).mpr ⟨1, rfl⟩⟩
      have hv := hcusp _ hmemξ
      rw [twistInduced_x hSigma hθ.1 hχ hres, (hdeg 1).2, hθx, hθ.2] at hv
      have hidx : ((twistStabilizer hSigma θ).index : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
      have hq1 : (Nat.card F : ℂ) - 1 ≠ 0 := by
        intro h0
        have h' : ((Nat.card F : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
          rw [Nat.cast_one]
          linear_combination h0
        have := Nat.cast_injective h'
        omega
      have h0 : (2 : ℂ) * (((twistStabilizer hSigma θ).index : ℂ) * ((Nat.card F : ℂ) - 1)) =
          0 := by linear_combination -hv
      exact mul_ne_zero two_ne_zero (mul_ne_zero hidx hq1) h0
  · rintro rfl
    exact ⟨fun r s => rfl, fun ξ _ => rfl⟩

end Complete

end CFSG.Wreathed.CentralSL2
