module

public import CFSG.CharacterTheory.Semidihedral.LocalPrincipalCompatibility

public section

namespace CFSG.Semidihedral.SameParameterSections

open CFSG.Open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open scoped BigOperators

variable {G : Type*} [Group G]

@[expose] def twoSection (t : G) : Set G :=
  {x | ∃ (a c : G) (k : ℕ), a * c = x ∧ Commute a c ∧
    orderOf a = 2 ^ k ∧ Odd (orderOf c) ∧ IsConj a t}

@[expose] def rotationSections {n : ℕ} {S : Sylow 2 G}
    (e : SemidihedralGroup n ≃* S) : Set G :=
  {x | ∃ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] ∧
    ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] ∧
    x ∈ twoSection ((e (r n) : G) ^ v)}

theorem exists_rotation_or_exterior (n : ℕ) (hn : 3 ≤ n) (x : SemidihedralGroup n) :
    (∃ v : ℤ, x = r n ^ v) ∨ ∃ v : ℤ, x = r n ^ v * s n := by
  obtain ⟨⟨i, b⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective x
  rcases exponent_cases b with rfl | rfl
  · left
    refine ⟨(i.val : ℤ), ?_⟩
    change element n hn i 0 = _
    simp only [element_eq, ZMod.val_zero, pow_zero, mul_one, zpow_natCast]
  · right
    refine ⟨(i.val : ℤ), ?_⟩
    change element n hn i 1 = _
    simp only [element_eq, ZMod.val_one_eq_one_mod, show 1 % 2 = 1 by decide,
      pow_one, zpow_natCast]

theorem exterior_fusion [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (e : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (v : ℤ) :
    IsConj (e (r n ^ v * s n) : G) (e (z n) : G) ∨
      IsConj (e (r n ^ v * s n) : G) ((e (r n) : G) ^ (modulus n / 4)) := by
  have hfusion :=
    (FocalFusion.semidihedral_focal_subgroup_four_cases n hn S e).2.2.2.2.mp hG
  let iota := FocalFusion.ambientHom n (S : Subgroup G) e
  rcases Int.even_or_odd v with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    have hv : v = 2 * j := by omega
    rw [hv]
    exact (iota.map_isConj (even_outside_conjugate n hn j).symm).trans
      (InvolutionFusion.supplied_s_isConj_z n hn S e hG)
  · right
    have hv : v = 2 * j + 1 := by omega
    rw [hv]
    have h := iota.map_isConj (odd_outside_conjugate n hn j).symm
    have htarget : IsConj (e (r n * s n) : G)
        ((e (r n) : G) ^ (modulus n / 4)) := by
      simpa only [map_mul, Subgroup.coe_mul, Subgroup.coe_pow, modulus] using hfusion.2
    exact h.trans htarget

theorem quarter_noncentral (n : ℕ) (hn : 4 ≤ n) :
    ¬ ((modulus n / 4 : ℕ) : ℤ) ≡ 0 [ZMOD modulus n] ∧
      ¬ ((modulus n / 4 : ℕ) : ℤ) ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
  have hm : modulus n = 4 * 2 ^ (n - 3) := by
    rw [modulus, show n - 1 = (n - 3) + 2 by omega, pow_add]
    norm_num
    omega
  have hk : 0 < 2 ^ (n - 3) := pow_pos (by decide) _
  constructor <;> intro h <;> have hh := h.eq
  · norm_cast at hh
    rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at hh
    omega
  · norm_cast at hh
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hh
    omega

theorem two_element_fusion [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (e : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G)
    (hcent : (e (z n) : G) = t) (a : G) (ha : a ≠ 1)
    (k : ℕ) (hak : orderOf a = 2 ^ k) :
    IsConj a t ∨ ∃ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] ∧
      ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] ∧
      IsConj a ((e (r n) : G) ^ v) := by
  have hpa : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hak])
  obtain ⟨y, hay⟩ := InvolutionFusion.exists_ambient_conjugate_mem_sylow S a hpa
  obtain ⟨x, hx⟩ := e.surjective y
  have hax : IsConj a (e x : G) := by simpa only [hx] using hay
  have hxne : (e x : G) ≠ 1 := by
    intro hxone
    have hh := conjugate_orderOf_eq hax
    rw [hxone, orderOf_one] at hh
    exact ha (orderOf_eq_one_iff.mp hh)
  rcases exists_rotation_or_exterior n (by omega) x with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · have hrot : IsConj a ((e (r n) : G) ^ v) := by
      simpa only [map_zpow, Subgroup.coe_zpow] using hax
    by_cases hvhalf : v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]
    · left
      have hh := (suppliedRotation_zpow_eq_iff (by omega) e v
        ((modulus n / 2 : ℕ) : ℤ)).mpr hvhalf
      have ht : (e (r n) : G) ^ ((modulus n / 2 : ℕ) : ℤ) = t := by
        rw [zpow_natCast, modulus_div_two n (by omega)]
        simpa only [z, map_pow, Subgroup.coe_pow] using hcent
      rw [hh, ht] at hrot
      exact hrot
    · right
      refine ⟨v, ?_, hvhalf, hrot⟩
      intro hvzero
      have hh := (suppliedRotation_zpow_eq_iff (by omega) e v 0).mpr hvzero
      apply hxne
      simpa only [map_zpow, Subgroup.coe_zpow, zpow_zero] using hh
  · rcases exterior_fusion n hn S e hG v with hz | hquarter
    · left
      exact hcent ▸ hax.trans hz
    · right
      exact ⟨((modulus n / 4 : ℕ) : ℤ), (quarter_noncentral n hn).1,
        (quarter_noncentral n hn).2, by simpa only [zpow_natCast] using hax.trans hquarter⟩

theorem even_order_section_cover [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (e : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (hcent : (e (z n) : G) = t)
    (x : G) (hx : 2 ∣ orderOf x) :
    x ∈ twoSection t ∨ x ∈ rotationSections e := by
  obtain ⟨a, c, k, -, -, hac, hprod, hak, hc⟩ :=
    finite_prime_primary_factorization x 2 Nat.prime_two
  obtain ⟨l, -, hal⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hak
  have hane : a ≠ 1 := by
    intro ha
    rw [ha, one_mul] at hprod
    have hodd : Odd (orderOf x) := hprod ▸ Nat.coprime_two_left.mp hc
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hx)
  rcases two_element_fusion n hn S e hG t hcent a hane l hal with hat | ⟨v, hv0, hv1, hav⟩
  · exact Or.inl ⟨a, c, l, hprod, hac, hal, Nat.coprime_two_left.mp hc, hat⟩
  · exact Or.inr ⟨v, hv0, hv1, a, c, l, hprod, hac, hal, Nat.coprime_two_left.mp hc, hav⟩

theorem twoSection_inv {t x : G} (hx : x ∈ twoSection t) :
    x⁻¹ ∈ twoSection t⁻¹ := by
  obtain ⟨a, c, k, hprod, hac, ha, hc, hconj⟩ := hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  refine ⟨a⁻¹, c⁻¹, k, ?_, hac.inv_inv, ?_, ?_, ?_⟩
  · rw [← hprod, hac.inv]
  · simpa only [orderOf_inv] using ha
  · simpa only [orderOf_inv] using hc
  · apply isConj_iff.mpr
    exact ⟨g, by rw [← hg, conj_inv]⟩

theorem involution_twoSection_inv {t x : G} (ht : orderOf t = 2)
    (hx : x ∈ twoSection t) : x⁻¹ ∈ twoSection t := by
  simpa only [inv_eq_self_of_orderOf_eq_two ht] using twoSection_inv hx

theorem rotationSections_inv {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (e : SemidihedralGroup n ≃* S) {x : G} (hx : x ∈ rotationSections e) :
    x⁻¹ ∈ rotationSections e := by
  obtain ⟨v, hv0, hv1, hx⟩ := hx
  obtain ⟨hneg0, hneg1⟩ := noncentral_neg hn hv0 hv1
  refine ⟨-v, hneg0, hneg1, ?_⟩
  simpa only [zpow_neg] using twoSection_inv hx

theorem twoSection_normal_form {t x : G} (hx : x ∈ twoSection t) :
    ∃ (g : G) (y : C t), Odd (orderOf y) ∧ g * x * g⁻¹ = t * (y : G) := by
  obtain ⟨a, c, _, hprod, hac, _, hc, hconj⟩ := hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hy : g * c * g⁻¹ ∈ C t := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    calc
      g * c * g⁻¹ * (g * a * g⁻¹) = g * (c * a) * g⁻¹ := by group
      _ = g * (a * c) * g⁻¹ := by rw [hac.eq]
      _ = g * a * g⁻¹ * (g * c * g⁻¹) := by group
  refine ⟨g, ⟨g * c * g⁻¹, hy⟩, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    have hord : orderOf (g * c * g⁻¹) = orderOf c :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
    rw [hord]
    exact hc
  · change g * x * g⁻¹ = t * (g * c * g⁻¹)
    rw [← hprod, ← hg]
    group

theorem character_eq_of_isConj (V : FiniteComplexRepresentation G) {a b : G}
    (hab : IsConj a b) : V.character a = V.character b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  exact (Representation.char_conj V.representation a g).symm

theorem pairing_of_section_agreement [Fintype G] (A : Set G)
    (hA : ∀ x ∈ A, x⁻¹ ∈ A) (f g W : G → ℂ) (c : ℂ)
    (hfg : ∀ x ∈ A, f x = c * g x) (hW : ∀ x ∉ A, W x = 0) :
    characterPairing f W = c * characterPairing g W := by
  have hterm : ∀ x : G, f x * W x⁻¹ = c * (g x * W x⁻¹) := by
    intro x
    by_cases hx : x ∈ A
    · rw [hfg x hx]
      ring
    · have hinv : x⁻¹ ∉ A := by
        intro h
        exact hx (by simpa only [inv_inv] using hA x⁻¹ h)
      rw [hW x⁻¹ hinv]
      ring
  unfold characterPairing
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
  ring

theorem pairing_of_involution_section [Fintype G] (t : G) (ht : orderOf t = 2)
    (f g W : G → ℂ) (c : ℂ)
    (hfg : ∀ x ∈ twoSection t, f x = c * g x)
    (hW : ∀ x ∉ twoSection t, W x = 0) :
    characterPairing f W = c * characterPairing g W :=
  pairing_of_section_agreement (twoSection t)
    (fun _ hx => involution_twoSection_inv ht hx) f g W c hfg hW

theorem pairing_of_rotation_sections [Fintype G] {n : ℕ} (hn : 4 ≤ n)
    {S : Sylow 2 G} (e : SemidihedralGroup n ≃* S) (f g W : G → ℂ) (c : ℂ)
    (hfg : ∀ x ∈ rotationSections e, f x = c * g x)
    (hW : ∀ x ∉ rotationSections e, W x = 0) :
    characterPairing f W = c * characterPairing g W :=
  pairing_of_section_agreement (rotationSections e)
    (fun _ hx => rotationSections_inv hn e hx) f g W c hfg hW

theorem even_order_agreement [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (e : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (hcent : (e (z n) : G) = t)
    (f g : G → ℂ) (ht : ∀ x ∈ twoSection t, f x = g x)
    (hr : ∀ x ∈ rotationSections e, f x = g x) :
    ∀ x : G, 2 ∣ orderOf x → f x = g x := by
  intro x hx
  rcases even_order_section_cover n hn S e hG t hcent x hx with hxt | hxr
  · exact ht x hxt
  · exact hr x hxr

@[expose] def restrictRepresentation (U : Subgroup G)
    (V : FiniteComplexRepresentation G) : FiniteComplexRepresentation U :=
  { vector := V.vector
    representation := V.representation.comp U.subtype }

theorem restrictRepresentation_character (U : Subgroup G)
    (V : FiniteComplexRepresentation G) (x : U) :
    (restrictRepresentation U V).character x = V.character (x : G) := rfl

theorem restrictRepresentation_degree (U : Subgroup G)
    (V : FiniteComplexRepresentation G) :
    Module.finrank ℂ (restrictRepresentation U V).vector = Module.finrank ℂ V.vector := rfl

theorem restriction_on_involution_section (U : Subgroup G) (t : U)
    (V : FiniteComplexRepresentation G) (W : FiniteComplexRepresentation U) (lambda : ℂ)
    (hvalues : ∀ y : C t, Odd (orderOf y) →
      V.character ((t : G) * ((y : U) : G)) = lambda * W.character (t * (y : U))) :
    ∀ x ∈ twoSection t, V.character (x : G) = lambda * W.character x := by
  intro x hx
  obtain ⟨g, y, hy, hconj⟩ := twoSection_normal_form hx
  have hGconj : (g : G) * (x : G) * (g : G)⁻¹ =
      (t : G) * ((y : U) : G) := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      congrArg (fun z : U => (z : G)) hconj
  calc
    V.character (x : G) = V.character ((t : G) * ((y : U) : G)) :=
      character_eq_of_isConj V (isConj_iff.mpr ⟨(g : G), hGconj⟩)
    _ = lambda * W.character (t * (y : U)) := hvalues y hy
    _ = lambda * W.character x := by
      rw [← character_eq_of_isConj W (isConj_iff.mpr ⟨g, hconj⟩)]

open scoped Classical in
theorem actual_family_involution_section_restrictions {G : Type} [Group G] [Fintype G]
    (U : Subgroup G) (t : U)
    (basis : FiniteIrreducibleCharacterBasis G)
    (basisU : FiniteIrreducibleCharacterBasis U) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (principalU : basisU.index)
    (localBasis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (localBasisU : FiniteIrreducibleCharacterBasis (C t))
    (localPrincipal : localBasis.index) (localPrincipalU : localBasisU.index)
    (q k : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1)
    (φ : C (t : G) → ℂ) (φU : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (α₁ α₂ α₃ α₄ : basisU.index)
    (ψ ν : ℕ → basis.index) (ψU νU : ℕ → basisU.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal (t : G) localBasis
      localPrincipal q e k φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hfamilyU : ActualPrincipalBlockFamily basisU ideal principalU t localBasisU
      localPrincipalU q e k φU e (-1) (-e) 1 α₁ α₂ α₃ α₄ ψU νU)
    (hφ : ∀ y : C t, Odd (orderOf y) →
      φ (LocalPrincipalCompatibility.centralizerInclusion U t y) = φU y) :
    ∀ x ∈ twoSection t,
      (basis.representation χ₁).character (x : G) =
        (δ₁ * e : ℤ) * (basisU.representation α₁).character x ∧
      (basis.representation χ₂).character (x : G) =
        (-δ₂ : ℤ) * (basisU.representation α₂).character x ∧
      (basis.representation χ₃).character (x : G) =
        (-δ₃ * e : ℤ) * (basisU.representation α₃).character x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hty, -⟩ := hfamily
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, htyU, -⟩ := hfamilyU
  have hodd (y : C t) (hy : Odd (orderOf y)) :
      Odd (orderOf (LocalPrincipalCompatibility.centralizerInclusion U t y)) := by
    rw [orderOf_injective (LocalPrincipalCompatibility.centralizerInclusion U t)
      (LocalPrincipalCompatibility.centralizerInclusion_injective U t)]
    exact hy
  have h₁ := restriction_on_involution_section U t
    (basis.representation χ₁) (basisU.representation α₁) ((δ₁ * e : ℤ) : ℂ) (by
      intro y hy
      have h := hty _ (hodd y hy)
      simp only [LocalPrincipalCompatibility.centralizerInclusion_coe] at h
      rw [h.1, (htyU y hy).1, hφ y hy]
      push_cast
      rcases he with rfl | rfl <;> ring)
  have h₂ := restriction_on_involution_section U t
    (basis.representation χ₂) (basisU.representation α₂) ((-δ₂ : ℤ) : ℂ) (by
      intro y hy
      have h := hty _ (hodd y hy)
      simp only [LocalPrincipalCompatibility.centralizerInclusion_coe] at h
      rw [h.2.1, (htyU y hy).2.1, hφ y hy]
      push_cast
      ring)
  have h₃ := restriction_on_involution_section U t
    (basis.representation χ₃) (basisU.representation α₃) ((-δ₃ * e : ℤ) : ℂ) (by
      intro y hy
      have h := hty _ (hodd y hy)
      simp only [LocalPrincipalCompatibility.centralizerInclusion_coe] at h
      rw [h.2.2.1, (htyU y hy).2.2.1]
      push_cast
      rcases he with rfl | rfl <;> ring)
  exact fun x hx => ⟨h₁ x hx, h₂ x hx, h₃ x hx⟩

theorem subgroup_sylow_of_odd_index [Finite G] (U : Subgroup G) (hodd : Odd U.index)
    (S : Sylow 2 U) : ∃ S' : Sylow 2 G,
      (S' : Subgroup G) = S.toSubgroup.map U.subtype := by
  have hnot2 : ¬ 2 ∣ U.index := fun h =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  refine ⟨Sylow.ofCard _ ?_, Sylow.coe_ofCard _ _⟩
  rw [Subgroup.card_map_of_injective U.subtype_injective, Sylow.card_eq_multiplicity,
    ← U.card_mul_index, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnot2, add_zero]

theorem subgroup_sylow_presentation [Finite G] (U : Subgroup G) (hodd : Odd U.index)
    (n : ℕ) (S : Sylow 2 U) (e : SemidihedralGroup n ≃* S) :
    ∃ (S' : Sylow 2 G) (e' : SemidihedralGroup n ≃* S'),
      (S' : Subgroup G) = S.toSubgroup.map U.subtype ∧
        ∀ x, (e' x : G) = ((e x : U) : G) := by
  obtain ⟨S', hS⟩ := subgroup_sylow_of_odd_index U hodd S
  let e' := e.trans ((S.toSubgroup.equivMapOfInjective U.subtype U.subtype_injective).trans
    (MulEquiv.subgroupCongr hS.symm))
  exact ⟨S', e', hS, fun _ => rfl⟩

open scoped Classical in
theorem restriction_on_rotation_sections {G : Type*} [Group G] [Fintype G]
    (U : Subgroup G) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (e : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eU : SemidihedralGroup n ≃* SU)
    (hcoe : ∀ x, (e x : G) = ((eU x : U) : G))
    (basis : FiniteIrreducibleCharacterBasis G)
    (basisU : FiniteIrreducibleCharacterBasis U) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (principalU : basisU.index)
    (hprincipal : (basis.representation principal).character = 1)
    (hprincipalU : (basisU.representation principalU).character = 1)
    (χ : basis.index) (α : basisU.index) (lambda : ℂ)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hα : α ∈ coefficientBlock basisU (localizedComplexIntegerRing ideal) principalU)
    (hvalues : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] →
      ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      (basis.representation χ).character ((e (r n) : G) ^ v) =
        lambda * (basisU.representation α).character ((eU (r n) : U) ^ v)) :
    ∀ x ∈ rotationSections eU,
      (basis.representation χ).character (x : G) =
        lambda * (basisU.representation α).character x := by
  rintro x ⟨v, hv0, hv1, a, c, _, hprod, hac, _, hc, hconj⟩
  have hprodG : (a : G) * (c : G) = (x : G) :=
    congrArg (fun z : U => (z : G)) hprod
  have hcG : Odd (orderOf (c : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hc
  have hconjG : IsConj (a : G) ((e (r n) : G) ^ v) := by
    simpa only [Subgroup.coe_subtype, Subgroup.coe_zpow, hcoe] using
      U.subtype.map_isConj hconj
  rw [principal_value_of_section hn e basis ideal principal hprincipal hv0 hv1
    hprodG (hac.map U.subtype) hcG hconjG hχ, hvalues v hv0 hv1,
    principal_value_of_section hn eU basisU ideal principalU hprincipalU hv0 hv1
      hprod hac hc hconj hα]

open scoped Classical in
theorem actual_family_rotation_section_restrictions {G : Type} [Group G] [Fintype G]
    (U : Subgroup G) (t : U) (ht : orderOf t = 2) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (eS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eSU : SemidihedralGroup n ≃* SU)
    (hcoe : ∀ x, (eS x : G) = ((eSU x : U) : G))
    (hcent : (eSU (r n) : U) ^ (modulus n / 2) = t)
    (hG : ∀ V : Subgroup G, V.index ≠ 2) (hU : ∀ V : Subgroup U, V.index ≠ 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hnonabU : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G)
    (basisU : FiniteIrreducibleCharacterBasis U) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (principalU : basisU.index)
    (hprincipal : (basis.representation principal).character = 1)
    (hprincipalU : (basisU.representation principalU).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (localBasisU : FiniteIrreducibleCharacterBasis (C t))
    (localPrincipal : localBasis.index) (localPrincipalU : localBasisU.index)
    (q : ℕ) (hq : 3 ≤ q) (hqodd : Odd q) (e : ℤ)
    (he1 : q % 4 = 1 → e = 1) (he3 : q % 4 = 3 → e = -1)
    (φ : C (t : G) → ℂ) (φU : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (α₁ α₂ α₃ α₄ : basisU.index)
    (ψ ν : ℕ → basis.index) (ψU νU : ℕ → basisU.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal (t : G) localBasis
      localPrincipal q e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hfamilyU : ActualPrincipalBlockFamily basisU ideal principalU t localBasisU
      localPrincipalU q e (2 ^ (n - 3)) φU e (-1) (-e) 1 α₁ α₂ α₃ α₄ ψU νU)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hdegU : ActualPrincipalDegreeRelations basisU q e (-1) (-e) 1 α₁ α₂ α₃ α₄) :
    ∀ x ∈ rotationSections eSU,
      (basis.representation χ₁).character (x : G) =
        (δ₁ * e : ℤ) * (basisU.representation α₁).character x ∧
      (basis.representation χ₂).character (x : G) =
        (-δ₂ : ℤ) * (basisU.representation α₂).character x ∧
      (basis.representation χ₃).character (x : G) =
        (-δ₃ * e : ℤ) * (basisU.representation α₃).character x := by
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hcentG : (eS (r n) : G) ^ (modulus n / 2) = (t : G) := by
    rw [hcoe, ← Subgroup.coe_pow, hcent]
  have hrotG := (actual_principal_rotation_values_and_congruences hG hn htG hnonab
    basis ideal principal hprincipal localBasis localPrincipal q hq hqodd e he1 he3 φ
    δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfamily hdeg eS hcentG).1
  have hrotU := (actual_principal_rotation_values_and_congruences hU hn ht hnonabU
    basisU ideal principalU hprincipalU localBasisU localPrincipalU q hq hqodd e he1 he3 φU
    e (-1) (-e) 1 α₁ α₂ α₃ α₄ ψU νU hfamilyU hdegU eSU hcent).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hB, -⟩ := hfamily
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hBU, -⟩ := hfamilyU
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index),
      c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hmemU : ∀ c ∈ ({principalU, α₁, α₂, α₃, α₄} : Finset basisU.index),
      c ∈ coefficientBlock basisU (localizedComplexIntegerRing ideal) principalU := by
    intro c hc
    rw [hBU]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have he : e = 1 ∨ e = -1 := by
    obtain ⟨a, ha⟩ := hqodd
    rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact Or.inl (he1 (by omega))
    · exact Or.inr (he3 (by omega))
  have h₁ := restriction_on_rotation_sections U n hn S eS SU eSU hcoe basis basisU ideal
    principal principalU hprincipal hprincipalU χ₁ α₁ ((δ₁ * e : ℤ) : ℂ)
    (hmem χ₁ (by simp)) (hmemU α₁ (by simp)) (by
      intro v hv0 hv1
      rw [(hrotG v hv0 hv1).1, (hrotU v hv0 hv1).1]
      push_cast
      rcases he with rfl | rfl <;> ring)
  have h₂ := restriction_on_rotation_sections U n hn S eS SU eSU hcoe basis basisU ideal
    principal principalU hprincipal hprincipalU χ₂ α₂ ((-δ₂ : ℤ) : ℂ)
    (hmem χ₂ (by simp)) (hmemU α₂ (by simp)) (by
      intro v hv0 hv1
      rw [(hrotG v hv0 hv1).2.1, (hrotU v hv0 hv1).2.1]
      push_cast
      ring)
  have h₃ := restriction_on_rotation_sections U n hn S eS SU eSU hcoe basis basisU ideal
    principal principalU hprincipal hprincipalU χ₃ α₃ ((-δ₃ * e : ℤ) : ℂ)
    (hmem χ₃ (by simp)) (hmemU α₃ (by simp)) (by
      intro v hv0 hv1
      rw [(hrotG v hv0 hv1).2.2, (hrotU v hv0 hv1).2.2]
      push_cast
      rcases he with rfl | rfl <;> ring)
  exact fun x hx => ⟨h₁ x hx, h₂ x hx, h₃ x hx⟩

end CFSG.Semidihedral.SameParameterSections
