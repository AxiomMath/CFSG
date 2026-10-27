module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.AugmentationValues
public import CFSG.CharacterTheory.Wreathed.AbelianInertiaInduction
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SumZero

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Augmentation

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

omit [Field F] [Finite F] in
theorem card_omega [Finite F] : Nat.card (Omega F) = Nat.card F + 1 := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Nat.card_eq_fintype_card]

theorem fixedPointCount_eq_card_iff (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h =
        (Nat.card F + 1 : ℂ) ↔ h ∈ (semilinearAction F b m hm heven Sigma hSigma).ker := by
  rw [fixedPointCount_semilinear, MonoidHom.mem_ker]
  constructor
  · intro hcount
    refine Equiv.ext fun x => ?_
    by_contra hx
    have hlt := Finite.card_subtype_lt (p := fun y => semilinearAction F b m hm heven Sigma hSigma
      h y = y) hx
    rw [card_omega] at hlt
    have hc : (Nat.card {x // semilinearAction F b m hm heven Sigma hSigma h x = x} : ℂ) =
        ((Nat.card F + 1 : ℕ) : ℂ) := by push_cast; exact hcount
    exact absurd (Nat.cast_injective hc) hlt.ne
  · intro h1
    simp only [h1, Equiv.Perm.one_apply]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), card_omega]
    push_cast
    rfl

theorem two_le_card_omega : 2 ≤ Nat.card (Omega F) := by
  rw [card_omega]
  have := Finite.one_lt_card (α := F)
  omega

theorem augmentation_mem_blocksIrr :
    (fun h => fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h - 1) ∈
      BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) := by
  have h2 := semilinearExtension_isMultiplyPretransitive F b m hm heven Sigma hSigma
  have ht : MulAction.IsPretransitive (SemilinearExtension F b m hm heven Sigma hSigma)
      (Omega F) := MulAction.isPretransitive_of_is_two_pretransitive
  have : Fintype F := Fintype.ofFinite F
  exact ((permutation_character_orbit_count (SemilinearExtension F b m hm heven Sigma hSigma)
    (Omega F)).2.2.2 ht (two_le_card_omega F)).mp h2

theorem augmentation_restrict_mem_blocksIrr :
    (fun g : matrixLayer F b m hm heven Sigma hSigma =>
      fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) g - 1) ∈
      BlocksIrr (matrixLayer F b m hm heven Sigma hSigma) := by
  have h2 := matrixLayer_isMultiplyPretransitive F b m hm heven Sigma hSigma
  have ht : MulAction.IsPretransitive (matrixLayer F b m hm heven Sigma hSigma)
      (Omega F) := MulAction.isPretransitive_of_is_two_pretransitive
  have : Fintype F := Fintype.ofFinite F
  have h := ((permutation_character_orbit_count (matrixLayer F b m hm heven Sigma hSigma)
    (Omega F)).2.2.2 ht (two_le_card_omega F)).mp h2
  convert h using 2
  rfl

theorem augmentation_one :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) 1 - 1 =
      (Nat.card F : ℂ) := by
  rw [(fixedPointCount_eq_card_iff F b m hm heven Sigma hSigma 1).mpr (Subgroup.one_mem _)]
  ring

end Augmentation

section Twists

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem linearCharacter_matrixLayer (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀)
    (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd (Nat.card Sigma))
    (r : Fin m) (s : Fin (Nat.card Sigma)) {g : SemilinearExtension F b m hm heven Sigma hSigma}
    (hg : g ∈ matrixLayer F b m hm heven Sigma hSigma) :
    linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s g = 1 := by
  rw [← psi_ker] at hg
  rw [linearCharacter, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hg, map_one]

@[expose] noncomputable def quotientLinearTwist (σ₀ : Sigma)
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m)
    (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)) (r : Fin m) (s : Fin (Nat.card Sigma)) :
    SemilinearExtension F b m hm heven Sigma hSigma ⧸ matrixLayer F b m hm heven Sigma hSigma →*
      ℂˣ :=
  QuotientGroup.lift _ (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s)
    (fun _ hg => linearCharacter_matrixLayer F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd
      r s hg)

theorem quotientLinearTwist_mk (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀)
    (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd (Nat.card Sigma))
    (r : Fin m) (s : Fin (Nat.card Sigma)) (g : SemilinearExtension F b m hm heven Sigma hSigma) :
    quotientLinearTwist F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s
        (g : SemilinearExtension F b m hm heven Sigma hSigma ⧸
          matrixLayer F b m hm heven Sigma hSigma) =
      linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s g :=
  QuotientGroup.lift_mk _ _ _

theorem quotient_isMulCommutative :
    IsMulCommutative (SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma) := by
  have hcyc : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
  have hcommS : ∀ x y : Sigma, x * y = y * x := fun x y => IsCyclic.commGroup.mul_comm x y
  have hprod : IsMulCommutative (Multiplicative (ZMod m) × Sigma) :=
    ⟨⟨fun x y => Prod.ext (mul_comm _ _) (hcommS _ _)⟩⟩
  exact Function.Surjective.isMulCommutative
    (f := (matrixQuotientEquiv F b m hm heven Sigma hSigma).symm.toMonoidHom)
    (matrixQuotientEquiv F b m hm heven Sigma hSigma).symm.surjective hprod

end Twists


section TwistFamily

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem augmentation_twists (hb1 : b ≠ 1) (σ₀ : Sigma)
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m)
    (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)) :
    let St : SemilinearExtension F b m hm heven Sigma hSigma → ℂ := fun h =>
      fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h - 1
    let Ξ : Fin m → Fin (Nat.card Sigma) → SemilinearExtension F b m hm heven Sigma hSigma → ℂ :=
      fun r s h =>
        (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s h : ℂ) * St h
    (∀ r s, Ξ r s ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) ∧
      Ξ r s 1 = Nat.card F) ∧
    Function.Injective (fun rs : Fin m × Fin (Nat.card Sigma) => Ξ rs.1 rs.2) ∧
    (∀ η ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma),
      0 < BlocksInnerProduct (fun g : matrixLayer F b m hm heven Sigma hSigma => η g)
        (fun g : matrixLayer F b m hm heven Sigma hSigma => St g) ↔ ∃ r s, η = Ξ r s) ∧
    (∀ r s, (fun g : matrixLayer F b m hm heven Sigma hSigma => Ξ r s g) =
      fun g : matrixLayer F b m hm heven Sigma hSigma => St g) := by
  intro St Ξ
  obtain ⟨V, i₁, i₂, i₃, ρ, hirr, hρ⟩ := augmentation_mem_blocksIrr F b m hm heven Sigma hSigma
  have hρSt : ρ.character = St := hρ
  have hρM : Representation.IsIrreducible
      (ρ.comp (matrixLayer F b m hm heven Sigma hSigma).subtype) := by
    apply Wreathed.isIrreducible_of_character_mem_blocksIrr
    have hc : Representation.character
        (ρ.comp (matrixLayer F b m hm heven Sigma hSigma).subtype) =
        fun g : matrixLayer F b m hm heven Sigma hSigma => St g := by
      funext g
      exact congrFun hρSt g
    rw [hc]
    exact augmentation_restrict_mem_blocksIrr F b m hm heven Sigma hSigma
  have : IsMulCommutative (SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma) :=
    quotient_isMulCommutative F b m hm heven Sigma hSigma
  obtain ⟨hmem, hinj, hiff, -⟩ :=
    Wreathed.irreducible_extension_abelian_quotient_character_twists _ ρ hρM
  set lamt := quotientLinearTwist F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd with hlamt
  have hΞ : ∀ r s, Ξ r s = Wreathed.quotientTwist (matrixLayer F b m hm heven Sigma hSigma)
      ρ.character (lamt r s) := by
    intro r s
    funext h
    change _ * St h = ρ.character h * (lamt r s (h : SemilinearExtension F b m hm heven Sigma
      hSigma ⧸ matrixLayer F b m hm heven Sigma hSigma) : ℂ)
    rw [hlamt, quotientLinearTwist_mk, hρSt, mul_comm]
  have hexh : ∀ lam : SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma →* ℂˣ, ∃ r s, lamt r s = lam := by
    intro lam
    obtain ⟨r, s, hrs⟩ := linearCharacter_exhaustive F b m hm heven Sigma hSigma σ₀ hgen ζm ζd
      hζm hζd hb1 (lam.comp (QuotientGroup.mk' _))
    refine ⟨r, s, QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun h => ?_)⟩
    change lamt r s (h : SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma) = _
    rw [hlamt, quotientLinearTwist_mk, hrs]
  refine ⟨fun r s => ⟨by rw [hΞ]; exact hmem _, ?_⟩, ?_, ?_, ?_⟩
  · change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s 1 : ℂ) * St 1 = _
    rw [map_one, Units.val_one, one_mul]
    exact augmentation_one F b m hm heven Sigma hSigma
  · rintro ⟨r, s⟩ ⟨r', s'⟩ h
    have h' : lamt r s = lamt r' s' := by
      apply hinj
      rw [← hΞ, ← hΞ]
      exact h
    apply linearCharacter_values_injective F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd
    funext g
    have := congrArg (fun lam : SemilinearExtension F b m hm heven Sigma hSigma ⧸
      matrixLayer F b m hm heven Sigma hSigma →* ℂˣ =>
        (lam (g : SemilinearExtension F b m hm heven Sigma hSigma ⧸
          matrixLayer F b m hm heven Sigma hSigma) : ℂ)) h'
    simp only [hlamt, quotientLinearTwist_mk] at this
    exact this
  · intro η hη
    have hcoe : (fun g : matrixLayer F b m hm heven Sigma hSigma => St g) =
        fun g : matrixLayer F b m hm heven Sigma hSigma => ρ.character g := by
      rw [hρSt]
    rw [hcoe, hiff η hη]
    constructor
    · rintro ⟨lam, rfl⟩
      obtain ⟨r, s, rfl⟩ := hexh lam
      exact ⟨r, s, (hΞ r s).symm⟩
    · rintro ⟨r, s, rfl⟩
      exact ⟨lamt r s, hΞ r s⟩
  · intro r s
    funext g
    change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s g : ℂ) * St g =
      St g
    rw [linearCharacter_matrixLayer F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s g.2,
      Units.val_one, one_mul]

end TwistFamily


section CommonKernel

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem mem_zpowers_of_orderOf_two {K : Type*} [Group K] {g : K} (hg : orderOf g = 2) (x : K) :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rw [← zpow_mod_orderOf, hg]
    have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hk with hk | hk
    · left; rw [hk, zpow_zero]
    · right; rw [hk, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

omit [Finite F] in
theorem orderOf_inl_cyclicGenerator_pow_m (h2 : (2 : F) ≠ 0) :
    orderOf (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) :
      SemilinearExtension F b m hm heven Sigma hSigma) = 2 := by
  rw [orderOf_injective _ SemidirectProduct.inl_injective]
  apply orderOf_eq_prime
  · rw [← pow_mul]
    exact (cyclicGenerator_pow_eq_one_iff F b m hm heven h2 _).mpr ⟨1, by ring⟩
  · rw [Ne, cyclicGenerator_pow_eq_one_iff F b m hm heven h2]
    intro h
    have := Nat.le_of_dvd hm h
    omega

omit [Finite F] in
theorem inl_cyclicGenerator_pow_m_eq :
    (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) :
      SemilinearExtension F b m hm heven Sigma hSigma) =
      matrixInclusion F b m hm heven Sigma hSigma
        (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) := by
  rw [cyclicGenerator_pow_m]
  rfl

theorem linearCharacter_inl_cyclicGenerator_pow (σ₀ : Sigma)
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m)
    (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)) (r : Fin m) (s : Fin (Nat.card Sigma)) (k : ℕ) :
    (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s
      (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ k)) : ℂ) = ζm ^ (r.val * k) := by
  have h := linearCharacter_formula F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s 1 k 0
  rw [pow_zero, mul_zero, pow_zero, mul_one] at h
  rw [← h, cyclicGenerator_pow]
  rfl

theorem augmentation_common_kernel (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b) (σ₀ : Sigma)
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ) (hζm : IsPrimitiveRoot ζm m)
    (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)) :
    let St : SemilinearExtension F b m hm heven Sigma hSigma → ℂ := fun h =>
      fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h - 1
    let Ξ : Fin m → Fin (Nat.card Sigma) → SemilinearExtension F b m hm heven Sigma hSigma → ℂ :=
      fun r s h =>
        (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s h : ℂ) * St h
    {h : SemilinearExtension F b m hm heven Sigma hSigma | ∀ r s, Ξ r s h = Ξ r s 1} =
      (Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) :
        SemilinearExtension F b m hm heven Sigma hSigma) : Set _) := by
  intro St Ξ
  have hq0 : (Nat.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hSt1 : St 1 = Nat.card F := augmentation_one F b m hm heven Sigma hSigma
  have hΞ1 : ∀ r s, Ξ r s 1 = Nat.card F := by
    intro r s
    change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s 1 : ℂ) *
      St 1 = _
    rw [map_one, Units.val_one, one_mul, hSt1]
  have hStA : ∀ h, St h = Nat.card F ↔
      h ∈ Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2)) := by
    intro h
    rw [← semilinearAction_ker F b m hm heven Sigma hSigma hb,
      ← fixedPointCount_eq_card_iff F b m hm heven Sigma hSigma h]
    change fixedPointCount _ _ h - 1 = _ ↔ _
    constructor
    · intro hh
      linear_combination hh
    · intro hh
      rw [hh]
      ring
  have hm2 : 1 < m := by
    obtain ⟨l, hl⟩ := heven
    omega
  ext h
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · intro hK
    have h00 := hK ⟨0, hm⟩ ⟨0, Nat.card_pos⟩
    rw [hΞ1] at h00
    have hlin00 : (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd
        ⟨0, hm⟩ ⟨0, Nat.card_pos⟩ h : ℂ) = 1 := by
      obtain ⟨g, σ⟩ := h
      obtain ⟨X, j, rfl⟩ := quotientClass_surjective F b m hm heven g
      have hmem : σ ∈ (Submonoid.powers σ₀ : Set Sigma) := by
        rw [powers_eq_zpowers]
        exact hgen σ
      obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff σ σ₀).mp hmem
      have : NeZero (2 * m) := ⟨by omega⟩
      have h := linearCharacter_formula F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd
        ⟨0, hm⟩ ⟨0, Nat.card_pos⟩ X j.val k
      rw [ZMod.natCast_zmod_val] at h
      rw [h]
      simp
    have hSth : St h = Nat.card F := by
      have : Ξ ⟨0, hm⟩ ⟨0, Nat.card_pos⟩ h = St h := by
        change _ * St h = St h
        rw [hlin00, one_mul]
      rw [← this, h00]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ((hStA h).mp hSth)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
        SemilinearExtension F b m hm heven Sigma hSigma) ^ n =
        SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ k) := by
      refine ⟨2 * (n % (m : ℤ)).toNat, ?_⟩
      have hord : orderOf (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
          SemilinearExtension F b m hm heven Sigma hSigma) = m := by
        rw [orderOf_injective _ SemidirectProduct.inl_injective,
          orderOf_cyclicGenerator_sq F b m hm heven h2]
      calc (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
            SemilinearExtension F b m hm heven Sigma hSigma) ^ n
          = (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
            SemilinearExtension F b m hm heven Sigma hSigma) ^
              (n % (orderOf (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
                SemilinearExtension F b m hm heven Sigma hSigma) : ℤ)) :=
            (zpow_mod_orderOf _ n).symm
        _ = (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
            SemilinearExtension F b m hm heven Sigma hSigma) ^
              (((n % (m : ℤ)).toNat : ℕ) : ℤ) := by
            rw [hord, Int.toNat_of_nonneg (Int.emod_nonneg n (by exact_mod_cast hm.ne'))]
        _ = _ := by rw [zpow_natCast, ← map_pow, ← pow_mul]
    rw [hk]
    have hk1 := hK ⟨1, hm2⟩ ⟨0, Nat.card_pos⟩
    rw [hΞ1, hk] at hk1
    change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd ⟨1, hm2⟩
      ⟨0, Nat.card_pos⟩ _ : ℂ) * St _ = _ at hk1
    have hSt' : St (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ k)) = Nat.card F := by
      rw [← hk]
      exact hSth
    rw [hSt', linearCharacter_inl_cyclicGenerator_pow] at hk1
    have hζk : ζm ^ k = 1 := by
      have := mul_right_cancel₀ hq0 (hk1.trans (one_mul _).symm)
      simpa using this
    obtain ⟨c, rfl⟩ := (hζm.pow_eq_one_iff_dvd k).mp hζk
    refine Subgroup.mem_zpowers_iff.mpr ⟨c, ?_⟩
    rw [zpow_natCast, ← map_pow, ← pow_mul]
  · intro hmem
    rcases (mem_zpowers_of_orderOf_two (orderOf_inl_cyclicGenerator_pow_m F b m hm heven Sigma
      hSigma h2) h).mp hmem with rfl | rfl
    · intro r s
      rfl
    · intro r s
      rw [hΞ1]
      change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s _ : ℂ) *
        St _ = _
      have hA : (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) :
          SemilinearExtension F b m hm heven Sigma hSigma) ∈
          Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2)) := by
        obtain ⟨l, hl⟩ := id heven
        refine Subgroup.mem_zpowers_iff.mpr ⟨l, ?_⟩
        rw [zpow_natCast, ← map_pow, ← pow_mul, show 2 * l = m by omega]
      rw [(hStA _).mpr hA, inl_cyclicGenerator_pow_m_eq,
        linearCharacter_matrixLayer F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s
          (MonoidHom.mem_range.mpr ⟨_, rfl⟩), Units.val_one, one_mul]

end CommonKernel

theorem model_projective_augmentation_character_family {F : Type} [Field F] [Fintype F]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (_hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (b : Fˣ) (hb : ¬ IsSquare b) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (hd : Odd (Nat.card Sigma)) :
    let H := SemilinearExtension F b m hm heven Sigma hSigma
    let M := matrixLayer F b m hm heven Sigma hSigma
    let A : Subgroup H :=
      Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2))
    let St : H → ℂ := fun h => fixedPointCount H (Omega F) h - 1
    let xH : H := matrixInclusion F b m hm heven Sigma hSigma
      (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F)
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (σ : Sigma) (v w : Fin 2 → F)
        (hv : v ≠ 0) (hw : w ≠ 0),
      w = (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
        GeneralLinearGroup (Fin 2) F).val *ᵥ (fun i => (σ : F ≃+* F) (v i)) →
      coordinateEquiv F ((⟨quotientClass F b m hm heven X j, σ⟩ : H) •
        (coordinateEquiv F).symm (Projectivization.mk F v hv)) = Projectivization.mk F w hw) ∧
    (semilinearAction F b m hm heven Sigma hSigma).ker = A ∧ Nat.card A = m ∧
    MulAction.IsMultiplyPretransitive M (Omega F) 2 ∧
    MulAction.IsMultiplyPretransitive H (Omega F) 2 ∧
    (sumZeroSubrep H (Omega F)).toRepresentation.character = St ∧
    St ∈ BlocksIrr H ∧ (fun g : M => St g) ∈ BlocksIrr M ∧ St 1 = Nat.card F ∧
    {h : H | St h = St 1} = A ∧
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)),
      ((∃ c : Fˣ, SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val =
          GeneralLinearGroup.scalar (Fin 2) c) →
        St ⟨quotientClass F b m hm heven X j, 1⟩ = Nat.card F) ∧
      (¬ (∃ c : Fˣ, SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val =
          GeneralLinearGroup.scalar (Fin 2) c) →
        ((Matrix.trace (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val ^ 2 -
            4 * Matrix.det (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val ≠ 0 →
          IsSquare (Matrix.trace (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val ^ 2 -
            4 * Matrix.det (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val) →
          St ⟨quotientClass F b m hm heven X j, 1⟩ = 1) ∧
        (Matrix.trace (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val ^ 2 -
            4 * Matrix.det (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val = 0 →
          St ⟨quotientClass F b m hm heven X j, 1⟩ = 0) ∧
        (¬ IsSquare (Matrix.trace (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val ^ 2 -
            4 * Matrix.det (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val) →
          St ⟨quotientClass F b m hm heven X j, 1⟩ = -1)))) ∧
    (∀ σ : Sigma, St ⟨1, σ⟩ = (p : ℂ) ^ (f / orderOf σ)) ∧
    (∀ σ : Sigma, St ⟨cyclicGenerator F b m hm heven, σ⟩ =
      -(if Nat.card F % 4 = 1 then 1 else -1)) ∧
    ∀ (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ)
      (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)),
      let Ξ : Fin m → Fin (Nat.card Sigma) → H → ℂ := fun r s h =>
        (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s h : ℂ) * St h
      (∀ (r : Fin m) (s : Fin (Nat.card Sigma)) (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ),
        Ξ r s ⟨quotientClass F b m hm heven X (j : ZMod (2 * m)), σ₀ ^ k⟩ =
          ζm ^ (r.val * j) * ζd ^ (s.val * k) *
            St ⟨quotientClass F b m hm heven X (j : ZMod (2 * m)), σ₀ ^ k⟩) ∧
      (∀ r s, Ξ r s ∈ BlocksIrr H ∧ Ξ r s 1 = Nat.card F) ∧
      Function.Injective (fun rs : Fin m × Fin (Nat.card Sigma) => Ξ rs.1 rs.2) ∧
      (∀ η ∈ BlocksIrr H, 0 < BlocksInnerProduct (fun g : M => η g) (fun g : M => St g) ↔
        ∃ r s, η = Ξ r s) ∧
      (∀ r s, (fun g : M => Ξ r s g) = fun g : M => St g) ∧
      {h : H | ∀ r s, Ξ r s h = Ξ r s 1} =
        (Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) : H) :
          Set H) ∧
      (Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) : H) :
          Set H) = {1, xH} := by
  intro H M A St xH
  have : Finite F := inferInstance
  have hchar : CharP F p := CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp
    hcard
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := by
      have := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h)
      exact this
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd
    rw [hp2] at hpodd
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  have hb1 : b ≠ 1 := nonsquare_ne_one F b hb
  have hq : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    have hodd : Odd (Nat.card F) := by
      rw [hcard]
      exact hpodd.pow
    obtain ⟨k, hk⟩ := hodd
    omega
  have hSt1 : St 1 = Nat.card F := augmentation_one F b m hm heven Sigma hSigma
  refine ⟨fun X j σ v w hv hw hwv => semilinearAction_projective F b m hm heven Sigma hSigma
      X j σ v w hv hw hwv,
    semilinearAction_ker F b m hm heven Sigma hSigma hb,
    card_zpowers_inl_sq F b m hm heven Sigma hSigma h2,
    matrixLayer_isMultiplyPretransitive F b m hm heven Sigma hSigma,
    semilinearExtension_isMultiplyPretransitive F b m hm heven Sigma hSigma,
    funext fun h => sumZeroSubrep_character H (Omega F) h,
    augmentation_mem_blocksIrr F b m hm heven Sigma hSigma,
    augmentation_restrict_mem_blocksIrr F b m hm heven Sigma hSigma, hSt1, ?_, ?_, ?_, ?_, ?_⟩
  ·
    ext h
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, hSt1]
    change fixedPointCount H (Omega F) h - 1 = (Nat.card F : ℂ) ↔
      h ∈ Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2))
    rw [← semilinearAction_ker F b m hm heven Sigma hSigma hb,
      ← fixedPointCount_eq_card_iff F b m hm heven Sigma hSigma h]
    constructor
    · intro hh
      linear_combination hh
    · intro hh
      rw [hh]
      ring
  ·
    intro X j
    have hlin := fixedPointCount_linear F b m hm heven Sigma hSigma h2 X j
    simp only at hlin
    refine ⟨fun hC => ?_, fun hC => ?_⟩
    · change fixedPointCount H (Omega F) _ - 1 = _
      rw [hlin, ite_eq_left hC]
      ring
    · have hval : St ⟨quotientClass F b m hm heven X j, 1⟩ =
          (sqrtCount (Matrix.trace (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val ^ 2 -
            4 * Matrix.det (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val) : ℂ) - 1 := by
        change fixedPointCount H (Omega F) _ - 1 = _
        rw [hlin, ite_eq_right hC]
      rw [hval, sqrtCount_eq h2]
      refine ⟨fun hΔ hsq => ?_, fun hΔ => ?_, fun hsq => ?_⟩
      · rw [ite_eq_right hΔ, ite_eq_left hsq]
        norm_num
      · rw [ite_eq_left hΔ]
        norm_num
      · have hΔ : Matrix.trace (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val ^ 2 -
            4 * Matrix.det (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
              GeneralLinearGroup (Fin 2) F).val ≠ 0 := by
          intro h0
          apply hsq
          rw [h0]
          exact ⟨0, by ring⟩
        rw [ite_eq_right hΔ, ite_eq_right hsq]
        norm_num
  ·
    intro σ
    change fixedPointCount H (Omega F) _ - 1 = _
    rw [fixedPointCount_field F b m hm heven Sigma hSigma hp hcard σ]
    ring
  ·
    intro σ
    have hσodd : Odd (orderOf σ) := Odd.of_dvd_nat hd (orderOf_dvd_natCard σ)
    change fixedPointCount H (Omega F) _ - 1 = _
    rw [fixedPointCount_cyclic_field F b m hm heven Sigma hSigma h2 hb σ hσodd]
    rcases hq with hq | hq
    · rw [ite_eq_right (by omega), ite_eq_left hq]
      norm_num
    · rw [ite_eq_left hq, ite_eq_right (by omega)]
      norm_num
  ·
    intro σ₀ hgen ζm ζd hζm hζd Ξ
    obtain ⟨hirrΞ, hinjΞ, hiffΞ, hresΞ⟩ :=
      augmentation_twists F b m hm heven Sigma hSigma hb1 σ₀ hgen ζm ζd hζm hζd
    refine ⟨fun r s X j k => ?_, hirrΞ, hinjΞ, hiffΞ, hresΞ,
      augmentation_common_kernel F b m hm heven Sigma hSigma h2 hb σ₀ hgen ζm ζd hζm hζd, ?_⟩
    · change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s _ : ℂ) *
        St _ = _
      rw [linearCharacter_formula]
    · ext h
      rw [SetLike.mem_coe, mem_zpowers_of_orderOf_two (orderOf_inl_cyclicGenerator_pow_m F b m hm
        heven Sigma hSigma h2), inl_cyclicGenerator_pow_m_eq]
      simp [xH]

end CFSG.Wreathed.CentralSL2
