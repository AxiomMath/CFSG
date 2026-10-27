module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearInvolutions
public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacyClasses

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Semidirect

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem fieldSL_weyl (σ : F ≃+* F) : fieldSL F σ (weyl F) = weyl F := by
  apply SL_eq_of_val
  ext i j
  change σ ((weyl F : SpecialLinearGroup (Fin 2) F) i j) =
    (weyl F : SpecialLinearGroup (Fin 2) F) i j
  rw [weyl_val]
  fin_cases i <;> fin_cases j <;> simp

theorem fieldAction_involutionY (σ : Sigma) :
    fieldAction F b m hm heven Sigma hSigma σ (involutionY F b m hm heven) =
      involutionY F b m hm heven := by
  rw [involutionY, map_mul, map_pow, map_pow, fieldAction_cyclicGenerator,
    fieldAction_specialInclusion, fieldSL_weyl]

theorem fieldAction_cyclicGenerator_pow_m (σ : Sigma) :
    fieldAction F b m hm heven Sigma hSigma σ (cyclicGenerator F b m hm heven ^ m) =
      cyclicGenerator F b m hm heven ^ m := by
  rw [map_pow, fieldAction_cyclicGenerator]

theorem mem_centralizer_inl_iff {y : CentralExtension F b m hm heven}
    (hy : ∀ σ : Sigma, fieldAction F b m hm heven Sigma hSigma σ y = y)
    (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h ∈ Subgroup.centralizer {(SemidirectProduct.inl y : SemilinearExtension F b m hm heven
      Sigma hSigma)} ↔ h.left ∈ Subgroup.centralizer {y} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hh
    have h1 := congrArg SemidirectProduct.left hh
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, hy] at h1
    exact h1
  · intro hh
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply, hy]
      exact hh
    · simp

theorem card_centralizer_inl [Finite F] {y : CentralExtension F b m hm heven}
    (hy : ∀ σ : Sigma, fieldAction F b m hm heven Sigma hSigma σ y = y) :
    Nat.card (Subgroup.centralizer {(SemidirectProduct.inl y :
      SemilinearExtension F b m hm heven Sigma hSigma)}) =
        Nat.card (Subgroup.centralizer {y}) * Nat.card Sigma := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun h => (⟨h.1.left, (mem_centralizer_inl_iff hy h.1).mp h.2⟩, h.1.right)
      invFun := fun p => ⟨⟨p.1.1, p.2⟩, (mem_centralizer_inl_iff hy _).mpr p.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem eq_inl_of_mul_self [Finite F] (hd : Odd (Nat.card Sigma))
    {h : SemilinearExtension F b m hm heven Sigma hSigma} (hh : h * h = 1) :
    h = SemidirectProduct.inl h.left := by
  have hr : h.right * h.right = 1 := by
    have := congrArg SemidirectProduct.right hh
    simpa using this
  have hr1 : h.right = 1 := by
    have hord : orderOf h.right ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hr)
    have hodd : Odd (orderOf h.right) := Odd.of_dvd_nat hd (orderOf_dvd_natCard _)
    have h1 : orderOf h.right = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h1
  apply SemidirectProduct.ext
  · rfl
  · rw [hr1]
    rfl

theorem isConj_inl {y w : CentralExtension F b m hm heven} (h : IsConj y w) :
    IsConj (SemidirectProduct.inl y : SemilinearExtension F b m hm heven Sigma hSigma)
      (SemidirectProduct.inl w) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨SemidirectProduct.inl c, by rw [map_mul, map_mul, map_inv]⟩

theorem inl_cyclicGenerator_pow_m_comm (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h * SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) =
      SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m) * h := by
  have hmem := (mem_centralizer_inl_iff (Sigma := Sigma) (hSigma := hSigma)
    (y := cyclicGenerator F b m hm heven ^ m) fieldAction_cyclicGenerator_pow_m h).mpr
    (Subgroup.mem_centralizer_singleton_iff.mpr (cyclicGenerator_pow_m_comm F b m hm heven _).symm)
  exact Subgroup.mem_centralizer_singleton_iff.mp hmem

theorem fixedPointCount_inl [Finite F] (g : CentralExtension F b m hm heven) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F)
        (SemidirectProduct.inl g) = (Nat.card {p : Omega F // g • p = p} : ℂ) := by
  rw [fixedPointCount_semilinear]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by
    rw [semilinearAction_inl, centralExtension_smul_def])

end Semidirect

theorem semilinear_involution_classes_and_augmentation_values {F : Type} [Field F] [Fintype F]
    {p f : ℕ} (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hcard : Nat.card F = p ^ f)
    (b : Fˣ) (hb : ¬ IsSquare b) (m : ℕ) (hm : 0 < m) (heven : Even m) (h4 : 4 ∣ m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (hd : Odd (Nat.card Sigma)) :
    let W := CentralExtension F b m hm heven
    let H := SemilinearExtension F b m hm heven Sigma hSigma
    let ι : W →* H := SemidirectProduct.inl
    let u := cyclicGenerator F b m hm heven
    let a := u ^ 2
    let x₀ := u ^ m
    let J : SpecialLinearGroup (Fin 2) F := weyl F
    let y₀ : W := a ^ (m / 4) * specialInclusion F b m hm heven J
    let q := Nat.card F
    let d := Nat.card Sigma
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    let St : H → ℂ := fun h => fixedPointCount H (Omega F) h - 1
    (J : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] ∧
    x₀ = specialInclusion F b m hm heven (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) ∧
    orderOf y₀ = 2 ∧ orderOf (ι y₀) = 2 ∧
    (∀ h : H, orderOf h = 2 ↔ h = ι x₀ ∨ IsConj (ι y₀) h) ∧
    (∀ h : H, IsConj (ι x₀) h ↔ h = ι x₀) ∧ ¬ IsConj (ι x₀) (ι y₀) ∧
    Nat.card H = m * d * q * (q ^ 2 - 1) ∧
    (Nat.card (Subgroup.centralizer {ι y₀}) : ℤ) = m * d * (q - ε) ∧
    (Nat.card {h : H // IsConj (ι y₀) h} : ℤ) = q * (q + ε) ∧
    IsConj y₀ (x₀ * y₀) ∧
    (∀ σ : Sigma, fieldAction F b m hm heven Sigma hSigma σ y₀ = y₀) ∧
    (nonsquareMatrix F b : Matrix (Fin 2) (Fin 2) F) = !![0, -(b : F); 1, 0] ∧
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (σ : Sigma) (v w : Fin 2 → F)
        (hv : v ≠ 0) (hw : w ≠ 0),
      w = (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
        GeneralLinearGroup (Fin 2) F).val *ᵥ (fun i => (σ : F ≃+* F) (v i)) →
      coordinateEquiv F ((⟨quotientClass F b m hm heven X j, σ⟩ : H) •
        (coordinateEquiv F).symm (Projectivization.mk F v hv)) = Projectivization.mk F w hw) ∧
    ∀ (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ)
      (hζm : IsPrimitiveRoot ζm m) (hζd : IsPrimitiveRoot ζd d),
      let lam : Fin m → Fin d → H → ℂ := fun r s h =>
        (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s h : ℂ)
      let Ξ : Fin m → Fin d → H → ℂ := fun r s h => lam r s h * St h
      (∀ (r : Fin m) (s : Fin d) (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ),
        lam r s ⟨quotientClass F b m hm heven X (j : ZMod (2 * m)), σ₀ ^ k⟩ =
          ζm ^ (r.val * j) * ζd ^ (s.val * k)) ∧
      (∀ r s, lam r s ∈ BlocksIrr H ∧ lam r s 1 = 1) ∧
      (∀ r s, Ξ r s ∈ BlocksIrr H ∧ Ξ r s 1 = q) ∧
      (∀ r s, lam r s (ι x₀) = 1 ∧ lam r s (ι y₀) = (-1) ^ r.val ∧ Ξ r s (ι x₀) = q ∧
        Ξ r s (ι y₀) = ε * (-1) ^ r.val) ∧
      Function.Injective (fun rs : Fin m × Fin d => Ξ rs.1 rs.2) := by
  intro W H ι u a x₀ J y₀ q d ε St
  have h2 := two_ne_zero_of_not_isSquare hb
  have hb1 : b ≠ 1 := nonsquare_ne_one F b hb
  have hq : 2 ≤ q := two_le_card F
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
    obtain ⟨k, hk⟩ := odd_card F h2
    omega
  have hsq : IsSquare (-1 : F) ↔ q % 4 = 1 := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  have hε1 : IsSquare (-1 : F) → ε = 1 := fun hs => ite_eq_left (hsq.mp hs)
  have hε2 : ¬ IsSquare (-1 : F) → ε = -1 := fun hs => ite_eq_right (fun h => hs (hsq.mpr h))
  have hy₀ : y₀ = involutionY F b m hm heven := rfl
  have hyy : y₀ * y₀ = 1 := involutionY_mul_self h4
  have hyA : y₀ ∉ Subgroup.zpowers (u ^ 2) := involutionY_not_mem hb
  have hy1 : y₀ ≠ 1 := fun h => hyA (by rw [h]; exact Subgroup.one_mem _)
  have hxA : x₀ ∈ Subgroup.zpowers (u ^ 2) := by
    obtain ⟨k, hk⟩ := id heven
    refine ⟨k, ?_⟩
    change (u ^ 2) ^ (k : ℤ) = u ^ m
    rw [zpow_natCast, ← pow_mul]
    congr 1
    omega
  have hyx : y₀ ≠ x₀ := fun h => hyA (by rw [h]; exact hxA)
  have hxx : x₀ * x₀ = 1 := cyclicGenerator_pow_m_mul_self
  have hx1 : x₀ ≠ 1 := by
    intro h
    have h' : cyclicGenerator F b m hm heven ^ m = 1 := h
    rw [cyclicGenerator_pow_eq_one_iff F b m hm heven h2] at h'
    have := Nat.le_of_dvd hm h'
    omega
  have hord2 : ∀ {K : Type} [Group K] (g : K), orderOf g = 2 ↔ g * g = 1 ∧ g ≠ 1 := by
    intro K _ g
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [orderOf_eq_prime_iff, pow_two]
  have hιinj : Function.Injective ι := SemidirectProduct.inl_injective
  have hιyy : ι y₀ * ι y₀ = 1 := by rw [← map_mul, hyy, map_one]
  have hιxx : ι x₀ * ι x₀ = 1 := by rw [← map_mul, hxx, map_one]
  have hιy1 : ι y₀ ≠ 1 := fun h => hy1 (hιinj (h.trans (map_one ι).symm))
  have hιx1 : ι x₀ ≠ 1 := fun h => hx1 (hιinj (h.trans (map_one ι).symm))
  have hιcomm : ∀ h : H, h * ι x₀ = ι x₀ * h := fun h => inl_cyclicGenerator_pow_m_comm h
  have hxcent : ∀ h : H, IsConj (ι x₀) h ↔ h = ι x₀ := by
    intro h
    constructor
    · intro hc
      obtain ⟨c, rfl⟩ := isConj_iff.mp hc
      rw [hιcomm c, mul_inv_cancel_right]
    · rintro rfl
      exact IsConj.refl _
  have hinv : ∀ h : H, orderOf h = 2 ↔ h = ι x₀ ∨ IsConj (ι y₀) h := by
    intro h
    rw [hord2]
    constructor
    · rintro ⟨hh, hh1⟩
      have hh' : h = ι h.left := eq_inl_of_mul_self hd hh
      have hw' : ι (h.left * h.left) = 1 := by rw [map_mul, ← hh', hh]
      have hw : h.left * h.left = 1 := hιinj (hw'.trans (map_one ι).symm)
      rcases involution_cases hb h4 hw with hw1 | hwx | hwc
      · exfalso
        apply hh1
        rw [hh', hw1, map_one]
      · left
        rw [hh']
        exact congrArg ι hwx
      · right
        rw [hh']
        exact isConj_inl hwc
    · rintro (rfl | hc)
      · exact ⟨hιxx, hιx1⟩
      · obtain ⟨c, hc'⟩ := isConj_iff.mp hc
        have hconj : MulAut.conj c (ι y₀) = h := by
          rw [MulAut.conj_apply]
          exact hc'
        refine ⟨?_, ?_⟩
        · rw [← hconj, ← map_mul, hιyy, map_one]
        · rw [← hconj]
          intro h1
          exact hιy1 ((MulEquiv.map_eq_one_iff _).mp h1)
  have hcardW : Nat.card W = m * q * (q ^ 2 - 1) := card_centralExtension_eq
  have hcardH : Nat.card H = m * d * q * (q ^ 2 - 1) := by
    have h1 : Nat.card H = Nat.card W * d := SemidirectProduct.card
    rw [h1, hcardW]
    ring
  have hCW : Nat.card (Subgroup.centralizer {y₀}) =
      if IsSquare (-1 : F) then m * (q - 1) else m * (q + 1) :=
    card_centralizer_involutionY hb
  have hCH0 : Nat.card (Subgroup.centralizer {ι y₀}) =
      Nat.card (Subgroup.centralizer {y₀}) * d :=
    card_centralizer_inl (y := involutionY F b m hm heven) fieldAction_involutionY
  have hCH : (Nat.card (Subgroup.centralizer {ι y₀}) : ℤ) = m * d * (q - ε) := by
    rw [hCH0, hCW]
    by_cases hs : IsSquare (-1 : F)
    · rw [ite_eq_left hs, hε1 hs]
      push_cast [Nat.cast_sub (show 1 ≤ q by omega)]
      ring
    · rw [ite_eq_right hs, hε2 hs]
      push_cast
      ring
  have hcl : (Nat.card {h : H // IsConj (ι y₀) h} : ℤ) = q * (q + ε) := by
    have hmul := card_isConj_mul_card_centralizer (ι y₀)
    rw [hcardH] at hmul
    have hmulZ : (Nat.card {h : H // IsConj (ι y₀) h} : ℤ) *
        (Nat.card (Subgroup.centralizer {ι y₀}) : ℤ) = m * d * q * (q ^ 2 - 1 : ℕ) := by
      exact_mod_cast hmul
    rw [hCH] at hmulZ
    have hε : ε * ε = 1 := by
      by_cases hs : IsSquare (-1 : F)
      · rw [hε1 hs]
        norm_num
      · rw [hε2 hs]
        norm_num
    have hne : (m : ℤ) * d * (q - ε) ≠ 0 := by
      have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
      have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := Sigma)).ne'
      have hqε : (q : ℤ) - ε ≠ 0 := by
        by_cases hs : IsSquare (-1 : F)
        · rw [hε1 hs]
          omega
        · rw [hε2 hs]
          omega
      exact mul_ne_zero (mul_ne_zero hm0 hd0) hqε
    have hq2 : ((q ^ 2 - 1 : ℕ) : ℤ) = (q - ε) * (q + ε) := by
      rw [Nat.cast_sub (by nlinarith : 1 ≤ q ^ 2)]
      push_cast
      linear_combination hε
    rw [hq2] at hmulZ
    apply mul_right_cancel₀ hne
    linear_combination hmulZ
  have hxy : IsConj y₀ (x₀ * y₀) := by
    have hxc : x₀ * y₀ = y₀ * x₀ := cyclicGenerator_pow_m_comm F b m hm heven y₀
    have hxyy : x₀ * y₀ * (x₀ * y₀) = 1 := by
      calc x₀ * y₀ * (x₀ * y₀) = x₀ * (y₀ * x₀) * y₀ := by group
        _ = x₀ * (x₀ * y₀) * y₀ := by rw [hxc]
        _ = (x₀ * x₀) * (y₀ * y₀) := by group
        _ = 1 := by rw [hxx, hyy, mul_one]
    rcases involution_cases hb h4 hxyy with h1 | h1 | h1
    · exfalso
      apply hyx
      calc y₀ = x₀ * (x₀ * y₀) := by rw [← mul_assoc, hxx, one_mul]
        _ = x₀ := by rw [h1, mul_one]
    · exfalso
      apply hy1
      calc y₀ = x₀ * (x₀ * y₀) := by rw [← mul_assoc, hxx, one_mul]
        _ = 1 := by rw [h1]; exact hxx
    · exact h1
  have hStx : St (ι x₀) = q := by
    have h1 : St (ι x₀) = (Nat.card {p : Omega F // x₀ • p = p} : ℂ) - 1 := by
      change fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F)
        (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m)) - 1 = _
      rw [fixedPointCount_inl]
    rw [h1, card_fixed_of_mem_zpowers hxA]
    push_cast
    ring
  have hSty : St (ι y₀) = ε := by
    have h1 : St (ι y₀) = (Nat.card {p : Omega F // y₀ • p = p} : ℂ) - 1 := by
      change fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F)
        (SemidirectProduct.inl (involutionY F b m hm heven)) - 1 = _
      rw [fixedPointCount_inl]
      rfl
    have h3 : Nat.card {p : Omega F // y₀ • p = p} = if IsSquare (-1 : F) then 2 else 0 :=
      card_fixed_involutionY hb
    rw [h1, h3]
    by_cases hs : IsSquare (-1 : F)
    · rw [ite_eq_left hs, hε1 hs]
      norm_num
    · rw [ite_eq_right hs, hε2 hs]
      norm_num
  refine ⟨weyl_val F, cyclicGenerator_pow_m F b m hm heven, (hord2 y₀).mpr ⟨hyy, hy1⟩,
    (hord2 (ι y₀)).mpr ⟨hιyy, hιy1⟩, hinv, hxcent,
    fun hc => hyx (hιinj ((hxcent _).mp hc)), hcardH, hCH, hcl, hxy,
    fun σ => fieldAction_involutionY σ, nonsquareMatrix_val F b,
    fun X j σ v w hv hw hwv => semilinearAction_projective F b m hm heven Sigma hSigma X j σ v w
      hv hw hwv, ?_⟩
  intro σ₀ hgen ζm ζd hζm hζd lam Ξ
  obtain ⟨hirrΞ, hinjΞ, -, -⟩ :=
    augmentation_twists F b m hm heven Sigma hSigma hb1 σ₀ hgen ζm ζd hζm hζd
  have hζhalf : ζm ^ (m / 2) = -1 := by
    have h1 : IsPrimitiveRoot (ζm ^ (m / 2)) (m / (m / 2)) :=
      hζm.pow_of_dvd (by omega) (Nat.div_dvd_of_dvd (even_iff_two_dvd.mp heven))
    have h2' : m / (m / 2) = 2 := by
      obtain ⟨k, hk⟩ := heven
      rw [show m / 2 = k by omega, hk, ← two_mul, Nat.mul_div_cancel _ (by omega)]
    rw [h2'] at h1
    exact h1.eq_neg_one_of_two_right
  have hlamx : ∀ r s, lam r s (ι x₀) = 1 := by
    intro r s
    change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s
      (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m)) : ℂ) = 1
    rw [linearCharacter_inl_cyclicGenerator_pow, mul_comm, pow_mul, hζm.pow_eq_one, one_pow]
  have hlamy : ∀ r s, lam r s (ι y₀) = (-1) ^ r.val := by
    intro r s
    have hJ : linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s
        (SemidirectProduct.inl (specialInclusion F b m hm heven (weyl F))) = 1 :=
      linearCharacter_matrixLayer F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s
        (MonoidHom.mem_range.mpr ⟨weyl F, rfl⟩)
    change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s
      (SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
        specialInclusion F b m hm heven (weyl F))) : ℂ) = _
    rw [map_mul, map_mul, hJ, mul_one, ← pow_mul, linearCharacter_inl_cyclicGenerator_pow,
      show 2 * (m / 4) = m / 2 by omega, mul_comm, pow_mul, hζhalf]
  refine ⟨fun r s X j k => linearCharacter_formula F b m hm heven Sigma hSigma σ₀ hgen ζm ζd
    hζm hζd r s X j k, fun r s => ⟨monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp
      (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s)), ?_⟩, hirrΞ,
    fun r s => ⟨hlamx r s, hlamy r s, ?_, ?_⟩, hinjΞ⟩
  · change (linearCharacter F b m hm heven Sigma hSigma σ₀ hgen ζm ζd hζm hζd r s 1 : ℂ) = 1
    rw [map_one, Units.val_one]
  · change lam r s (ι x₀) * St (ι x₀) = _
    rw [hlamx, hStx, one_mul]
  · change lam r s (ι y₀) * St (ι y₀) = _
    rw [hlamy, hSty, mul_comm]

end CFSG.Wreathed.CentralSL2
