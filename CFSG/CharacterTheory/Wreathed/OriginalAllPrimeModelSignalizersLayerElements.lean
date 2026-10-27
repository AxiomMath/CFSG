module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersBasic
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersTools

public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.CentralSL2 CFSG.ABGTheoremB
open scoped Pointwise

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem inl_specialInclusion_mul (A B : SpecialLinearGroup (Fin 2) F) :
    (SemidirectProduct.inl (specialInclusion F b m hm heven A) :
        SemilinearExtension F b m hm heven Sigma hSigma) *
      SemidirectProduct.inl (specialInclusion F b m hm heven B) =
        SemidirectProduct.inl (specialInclusion F b m hm heven (A * B)) := by
  rw [map_mul, map_mul]

theorem inl_specialInclusion_inv (A : SpecialLinearGroup (Fin 2) F) :
    (SemidirectProduct.inl (specialInclusion F b m hm heven A) :
        SemilinearExtension F b m hm heven Sigma hSigma)⁻¹ =
      SemidirectProduct.inl (specialInclusion F b m hm heven A⁻¹) := by
  rw [map_inv, map_inv]

theorem inl_specialInclusion_pow (A : SpecialLinearGroup (Fin 2) F) (n : ℕ) :
    (SemidirectProduct.inl (specialInclusion F b m hm heven A) :
        SemilinearExtension F b m hm heven Sigma hSigma) ^ n =
      SemidirectProduct.inl (specialInclusion F b m hm heven (A ^ n)) := by
  rw [map_pow, map_pow]

theorem modelY_conj_inl_specialInclusion (Z : SpecialLinearGroup (Fin 2) F) :
    modelY b m hm heven Sigma hSigma *
        SemidirectProduct.inl (specialInclusion F b m hm heven Z) *
        (modelY b m hm heven Sigma hSigma)⁻¹ =
      SemidirectProduct.inl (specialInclusion F b m hm heven (weyl F * Z * (weyl F)⁻¹)) := by
  rw [modelY_eq, semidirect_conj_inl]
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, MulAut.one_apply]
  congr 1
  have hc : ∀ g : CentralExtension F b m hm heven,
      (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * g =
        g * (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) :=
    fun g => (Commute.pow_left (cyclicGenerator_sq_comm F b m hm heven g) (m / 4)).eq
  rw [involutionY, map_mul, map_mul, map_inv]
  calc (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * specialInclusion F b m hm heven (weyl F) *
        specialInclusion F b m hm heven Z *
        ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          specialInclusion F b m hm heven (weyl F))⁻¹
      = (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          (specialInclusion F b m hm heven (weyl F) * specialInclusion F b m hm heven Z *
            (specialInclusion F b m hm heven (weyl F))⁻¹) *
          ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4))⁻¹ := by group
    _ = (specialInclusion F b m hm heven (weyl F) * specialInclusion F b m hm heven Z *
            (specialInclusion F b m hm heven (weyl F))⁻¹) *
          (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4))⁻¹ := by rw [hc]
    _ = _ := by rw [mul_inv_cancel_right]

theorem modelY_mul_self (h4 : 4 ∣ m) :
    modelY b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma = 1 := by
  rw [modelY_eq, ← map_mul, involutionY_mul_self h4, map_one]

theorem modelY_mem_modelC :
    modelY b m hm heven Sigma hSigma ∈ modelC b m hm heven Sigma hSigma :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem modelY_conj_eq_inv_of_signalizer [Finite F] (h4 : 4 ∣ m) {K : Subgroup _} {r : ℕ}
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hX : X ∈ signalizers K (modelC b m hm heven Sigma hSigma) r) {x} (hx : x ∈ X) :
    modelY b m hm heven Sigma hSigma * x * (modelY b m hm heven Sigma hSigma)⁻¹ = x⁻¹ :=
  conj_eq_inv_of_inf_centralizer_eq_bot (modelY_mul_self h4) (hX.2.2.1 modelY_mem_modelC)
    hX.2.2.2 hx

theorem comm_of_signalizer [Finite F] (h4 : 4 ∣ m) {K : Subgroup _} {r : ℕ}
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hX : X ∈ signalizers K (modelC b m hm heven Sigma hSigma) r) {x x'} (hx : x ∈ X)
    (hx' : x' ∈ X) : x * x' = x' * x := by
  have h1 := modelY_conj_eq_inv_of_signalizer h4 hX (X.mul_mem hx hx')
  have h2 : modelY b m hm heven Sigma hSigma * (x * x') * (modelY b m hm heven Sigma hSigma)⁻¹ =
      (modelY b m hm heven Sigma hSigma * x * (modelY b m hm heven Sigma hSigma)⁻¹) *
        (modelY b m hm heven Sigma hSigma * x' * (modelY b m hm heven Sigma hSigma)⁻¹) := by
    group
  rw [h2, modelY_conj_eq_inv_of_signalizer h4 hX hx, modelY_conj_eq_inv_of_signalizer h4 hX hx',
    _root_.mul_inv_rev] at h1
  have h3 := congrArg (·⁻¹) h1
  simp only [_root_.mul_inv_rev, inv_inv] at h3
  exact h3.symm

theorem exists_isotropic_of_mem_signalizer [Fintype F] (h2 : (2 : F) ≠ 0)
    (hq : 5 < Nat.card F) (h4 : 4 ∣ m) {r : ℕ}
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hX : X ∈ signalizers (modelLayer b m hm heven Sigma hSigma)
      (modelC b m hm heven Sigma hSigma) r) {x} (hx : x ∈ X) (hx1 : x ≠ 1) :
    ∃ Z : SpecialLinearGroup (Fin 2) F,
      SemidirectProduct.inl (specialInclusion F b m hm heven Z) = x ∧ Z 0 1 = Z 1 0 ∧
        (Z 0 0 - Z 1 1) ^ 2 + 4 * Z 0 1 ^ 2 = 0 ∧ Z ≠ 1 ∧ Z ≠ -1 := by
  obtain ⟨Z, rfl⟩ := mem_modelLayer_iff.mp (hX.1 hx)
  have hinj := inl_specialInclusion_injective (b := b) (hm := hm) (heven := heven)
    (Sigma := Sigma) (hSigma := hSigma)
  have hJ : weyl F * Z * (weyl F)⁻¹ = Z⁻¹ := by
    have h := modelY_conj_eq_inv_of_signalizer h4 hX hx
    rw [modelY_conj_inl_specialInclusion, inl_specialInclusion_inv] at h
    exact hinj h
  have hZs := symm_of_weyl_conj_eq_inv hJ
  obtain ⟨t, ht, htne⟩ := exists_torus_mul_ne_zero h2 hq
  have hcomm : Z * (t * Z * t⁻¹) = t * Z * t⁻¹ * Z := by
    have hc : (SemidirectProduct.inl (specialInclusion F b m hm heven t) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ modelC b m hm heven Sigma hSigma :=
      (inl_specialInclusion_mem_modelC_iff t).mpr ht
    have hmem := (Subgroup.mem_normalizer_iff.mp (hX.2.2.1 hc) _).mp hx
    have h := comm_of_signalizer h4 hX hx hmem
    simp only [inl_specialInclusion_mul, inl_specialInclusion_inv] at h
    exact hinj h
  have hiso := isotropic_of_commute_conj hZs ht hcomm htne
  have hZ1 : Z ≠ 1 := by
    rintro rfl
    apply hx1
    rw [map_one, map_one]
  have hZm1 : Z ≠ -1 := by
    rintro rfl
    apply hx1
    have hmemC : (SemidirectProduct.inl (specialInclusion F b m hm heven (-1)) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ modelC b m hm heven Sigma hSigma := by
      rw [← modelX_eq]
      exact modelX_mem_modelC
    have hb : _ ∈ X ⊓ modelC b m hm heven Sigma hSigma := ⟨hx, hmemC⟩
    rw [hX.2.2.2] at hb
    exact (Subgroup.mem_bot).mp hb
  exact ⟨Z, rfl, hZs, hiso, hZ1, hZm1⟩

theorem isSquare_neg_one_of_signalizer [Fintype F] (h2 : (2 : F) ≠ 0) (hq : 5 < Nat.card F)
    (h4 : 4 ∣ m) {r : ℕ} {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hX : X ∈ signalizers (modelLayer b m hm heven Sigma hSigma)
      (modelC b m hm heven Sigma hSigma) r) (hX1 : X ≠ ⊥) : IsSquare (-1 : F) := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨Z, -, hZs, hiso, hZ1, hZm1⟩ := exists_isotropic_of_mem_signalizer h2 hq h4 hX hx hx1'
  exact isSquare_neg_one_of_isotropic h2 hZs hiso hZ1 hZm1

theorem neg_rootSL_pow_ne_one (h2 : (2 : F) ≠ 0) {j : F} (hj : j * j = -1) (l : F) {n : ℕ}
    (hn : Odd n) : (-rootSL j hj l) ^ n ≠ 1 := by
  intro h
  rw [neg_pow, hn.neg_one_pow, neg_one_mul, rootSL_nsmul] at h
  have e01 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => X 0 1) h
  have e00 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => X 0 0) h
  change -((n : F) * l) = 0 at e01
  change -(1 + (n : F) * l * j) = 1 at e00
  have hnl : (n : F) * l = 0 := neg_eq_zero.mp e01
  rw [hnl, zero_mul, add_zero] at e00
  apply h2
  linear_combination -e00

theorem mem_rootGroup_of_mem_signalizer [Fintype F] (h2 : (2 : F) ≠ 0) (hq : 5 < Nat.card F)
    (h4 : 4 ∣ m) {i : F} (hi : i * i = -1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hX : X ∈ signalizers (modelLayer b m hm heven Sigma hSigma)
      (modelC b m hm heven Sigma hSigma) r) {x} (hx : x ∈ X) :
    x ∈ rootGroup b m hm heven Sigma hSigma i hi ∨
      x ∈ rootGroup b m hm heven Sigma hSigma (-i) (neg_mul_neg_eq_neg_one hi) := by
  by_cases hx1 : x = 1
  · left
    rw [hx1]
    exact Subgroup.one_mem _
  obtain ⟨Z, rfl, hZs, hiso, hZ1, hZm1⟩ := exists_isotropic_of_mem_signalizer h2 hq h4 hX hx hx1
  have hr : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := hX.2.1 ⟨_, hx⟩
  have hZk : Z ^ r ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
    rw [inl_specialInclusion_pow] at h
    have h' : (SemidirectProduct.inl (specialInclusion F b m hm heven (Z ^ r ^ k)) :
        SemilinearExtension F b m hm heven Sigma hSigma) =
          SemidirectProduct.inl (specialInclusion F b m hm heven 1) := by
      rw [h, map_one, map_one]
    exact inl_specialInclusion_injective h'
  have hodd : Odd (r ^ k) := (hr.out.eq_two_or_odd'.resolve_left hr2).pow
  rcases eq_rootSL_of_isotropic h2 hi hZs hiso with ⟨l, hl | hl⟩ | ⟨l, hl | hl⟩
  · left
    rw [hl]
    exact inl_rootSL_mem_rootGroup hi l
  · exact absurd (hl ▸ hZk) (neg_rootSL_pow_ne_one h2 hi l hodd)
  · right
    rw [hl]
    exact inl_rootSL_mem_rootGroup _ l
  · exact absurd (hl ▸ hZk) (neg_rootSL_pow_ne_one h2 _ l hodd)

theorem prime_eq_of_signalizer [Fintype F] (h2 : (2 : F) ≠ 0) (hq : 5 < Nat.card F)
    (h4 : 4 ∣ m) {p f : ℕ} (hp : p.Prime) (hcard : Nat.card F = p ^ f) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hX : X ∈ signalizers (modelLayer b m hm heven Sigma hSigma)
      (modelC b m hm heven Sigma hSigma) r) (hX1 : X ≠ ⊥) : r = p := by
  obtain ⟨i, hi⟩ := isSquare_neg_one_of_signalizer h2 hq h4 hX hX1
  have hi' : i * i = -1 := hi.symm
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hr' : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := hX.2.1 ⟨_, hx⟩
  have hxk : x ^ r ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  obtain ⟨j, hj, l, hxl⟩ : ∃ (j : F) (hj : j * j = -1) (l : F),
      SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL j hj l)) = x := by
    rcases mem_rootGroup_of_mem_signalizer h2 hq h4 hi' hr hr2 hX hx with h | h
    · obtain ⟨l, hl⟩ := mem_rootGroup_iff.mp h
      exact ⟨i, hi', l, hl⟩
    · obtain ⟨l, hl⟩ := mem_rootGroup_iff.mp h
      exact ⟨-i, _, l, hl⟩
  subst hxl
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hx1'
    rw [rootSL_zero, map_one, map_one]
  rw [inl_specialInclusion_pow, rootSL_nsmul] at hxk
  have hxk' : (SemidirectProduct.inl (specialInclusion F b m hm heven
      (rootSL j hj (((r ^ k : ℕ) : F) * l))) : SemilinearExtension F b m hm heven Sigma hSigma) =
        SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL j hj 0)) := by
    rw [hxk, rootSL_zero, map_one, map_one]
  have h0 := rootSL_injective j hj (inl_specialInclusion_injective hxk')
  have hrk : ((r ^ k : ℕ) : F) = 0 := (mul_eq_zero.mp h0).resolve_right hl0
  have hchar : ringChar F = p := by
    obtain ⟨n, hcp, hn⟩ := FiniteField.card F (ringChar F)
    rw [← Nat.card_eq_fintype_card, hcard] at hn
    have hpd : p ∣ ringChar F ^ (n : ℕ) := by
      rw [← hn]
      exact dvd_pow_self p (by
        rintro rfl
        rw [pow_zero] at hcard
        have : 1 < Nat.card F := Finite.one_lt_card
        omega)
    exact ((Nat.prime_dvd_prime_iff_eq hp hcp).mp (hp.dvd_of_dvd_pow hpd)).symm
  have hpr : p ∣ r ^ k := by
    rw [← hchar]
    exact (CharP.cast_eq_zero_iff F (ringChar F) _).mp hrk
  exact ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpr)).symm

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
