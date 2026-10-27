module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.Lin2

open Matrix MatrixGroups Matrix.SpecialLinearGroup

section SL2

variable {F : Type*} [Field F]

@[expose] def slUpper (c : F) : SL(2, F) :=
  transvection (show (0 : Fin 2) ≠ 1 by decide) c

@[expose] def slLower (c : F) : SL(2, F) :=
  transvection (show (1 : Fin 2) ≠ 0 by decide) c

theorem slUpper_val (c : F) : (slUpper c : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slUpper, transvection_coe]

theorem slLower_val (c : F) : (slLower c : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slLower, transvection_coe]

theorem slUpper_zero : slUpper (0 : F) = 1 := transvection_coeff_zero _

theorem slUpper_add (a b : F) : slUpper (a + b) = slUpper a * slUpper b := transvection_add _ _ _

theorem slUpper_inv (a : F) : (slUpper a)⁻¹ = slUpper (-a) := transvection_inv _ _

theorem slUpper_injective : Function.Injective (slUpper : F → SL(2, F)) := by
  intro a b h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [slUpper_val] using this

@[expose] def slUpperHom (F : Type*) [Field F] : Multiplicative F →* SL(2, F) where
  toFun c := slUpper (Multiplicative.toAdd c)
  map_one' := slUpper_zero
  map_mul' _ _ := slUpper_add _ _

@[expose] def slUni (F : Type*) [Field F] : Subgroup SL(2, F) := (slUpperHom F).range

theorem mem_slUni {A : SL(2, F)} : A ∈ slUni F ↔ ∃ c : F, A = slUpper c := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩

theorem slUpper_mem_slUni (c : F) : slUpper c ∈ slUni F := mem_slUni.mpr ⟨c, rfl⟩

theorem card_slUni [Finite F] : Nat.card (slUni F) = Nat.card F := by
  have hinj : Function.Injective (slUpperHom F) := fun a b h =>
    Multiplicative.toAdd.injective (slUpper_injective (F := F) h)
  exact Nat.card_congr ((MonoidHom.ofInjective hinj).toEquiv.symm.trans Multiplicative.toAdd)

theorem conj_slUpper_of_apply_one_zero (A : SL(2, F)) (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (t : F) : A * slUpper t * A⁻¹ = slUpper ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t) := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h := A.property
    rw [Matrix.det_fin_two, hA, mul_zero, sub_zero] at h
    exact h
  have hdet' : (A : Matrix (Fin 2) (Fin 2) F) 1 1 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [mul_comm, hdet]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [slUpper_val, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, hA, hdet, hdet', pow_two]
  all_goals ring

theorem mem_normalizer_slUni_of_apply_one_zero (A : SL(2, F))
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    A ∈ Subgroup.normalizer (slUni F : Set SL(2, F)) := by
  have hinv : ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hA]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨t, rfl⟩ := mem_slUni.mp hy
    rw [conj_slUpper_of_apply_one_zero A hA]
    exact slUpper_mem_slUni _
  · intro hy
    obtain ⟨t, ht⟩ := mem_slUni.mp hy
    have h2 : y = A⁻¹ * (A * y * A⁻¹) * A := by group
    rw [h2, ht]
    have := conj_slUpper_of_apply_one_zero A⁻¹ hinv t
    rw [inv_inv] at this
    rw [this]
    exact slUpper_mem_slUni _

@[expose] def slWeyl (c : F) (hc : c ≠ 0) : SL(2, F) :=
  ⟨!![0, -c⁻¹; c, 0], by simp [Matrix.det_fin_two, hc]⟩

theorem slWeyl_val (c : F) (hc : c ≠ 0) :
    (slWeyl c hc : Matrix (Fin 2) (Fin 2) F) = !![0, -c⁻¹; c, 0] := rfl

theorem eq_slUpper_mul_slWeyl_mul_slUpper (A : SL(2, F))
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    A = slUpper ((A : Matrix (Fin 2) (Fin 2) F) 0 0 / (A : Matrix (Fin 2) (Fin 2) F) 1 0) *
      slWeyl ((A : Matrix (Fin 2) (Fin 2) F) 1 0) hA *
      slUpper ((A : Matrix (Fin 2) (Fin 2) F) 1 1 / (A : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have h := A.property
    rwa [Matrix.det_fin_two] at h
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [slUpper_val, slWeyl_val, Matrix.mul_apply, Fin.sum_univ_two, hA]
  · field_simp
    linear_combination (-1 : F) * hdet
  · field_simp

theorem slWeyl_mul_slUpper_mul_inv (c : F) (hc : c ≠ 0) (t : F) :
    slWeyl c hc * slUpper t * (slWeyl c hc)⁻¹ = slLower (-(c ^ 2 * t)) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [slUpper_val, slLower_val, slWeyl_val, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hc]
  all_goals field_simp

theorem eq_top_of_slUni_le {K : Subgroup SL(2, F)} (hUK : slUni F ≤ K)
    (hK : ¬ K ≤ Subgroup.normalizer (slUni F : Set SL(2, F))) : K = ⊤ := by
  obtain ⟨A, hAK, hAN⟩ := Set.not_subset.mp hK
  have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := fun h =>
    hAN (mem_normalizer_slUni_of_apply_one_zero A h)
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0 with hcdef
  have hW : slWeyl c hc ∈ K := by
    have h1 := eq_slUpper_mul_slWeyl_mul_slUpper A hc
    have e : slWeyl c hc =
        (slUpper ((A : Matrix (Fin 2) (Fin 2) F) 0 0 / c))⁻¹ * A *
          (slUpper ((A : Matrix (Fin 2) (Fin 2) F) 1 1 / c))⁻¹ := by
      conv_lhs => rw [show slWeyl c hc = (slUpper ((A : Matrix (Fin 2) (Fin 2) F) 0 0 / c))⁻¹ *
        (slUpper ((A : Matrix (Fin 2) (Fin 2) F) 0 0 / c) * slWeyl c hc *
          slUpper ((A : Matrix (Fin 2) (Fin 2) F) 1 1 / c)) *
        (slUpper ((A : Matrix (Fin 2) (Fin 2) F) 1 1 / c))⁻¹ by group]
      rw [← h1]
    rw [e]
    exact K.mul_mem (K.mul_mem (K.inv_mem (hUK (slUpper_mem_slUni _))) hAK)
      (K.inv_mem (hUK (slUpper_mem_slUni _)))
  have hlower : ∀ y : F, slLower y ∈ K := by
    intro y
    have h2 := slWeyl_mul_slUpper_mul_inv c hc (-(y / c ^ 2))
    have e : -(c ^ 2 * -(y / c ^ 2)) = y := by field_simp
    rw [e] at h2
    rw [← h2]
    exact K.mul_mem (K.mul_mem hW (hUK (slUpper_mem_slUni _))) (K.inv_mem hW)
  apply top_unique
  intro B _
  refine Matrix.SL2.transvection_induction (fun g => g ∈ K) ?_ (fun _ _ => K.mul_mem) B
  intro i j hij r
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    exact hUK (slUpper_mem_slUni r)
  · obtain rfl : j = 0 := by fin_cases j <;> tauto
    exact hlower r

theorem card_specialLinear_two [Fintype F] :
    Nat.card SL(2, F) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have h := Matrix.card_SL_field (n := 2) (𝔽 := F)
  rw [h]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card F = r + 1 := ⟨Fintype.card F - 1, by omega⟩
  rw [hr]
  have e1 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have e2 : (r + 1) ^ 2 - (r + 1) = r * (r + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have hr0 : 0 < r := by omega
  rw [e1, e2, Nat.add_sub_cancel]
  rw [show r * (r + 2) * (r * (r + 1)) = r * ((r + 1) * (r * (r + 2))) by ring]
  rw [Nat.mul_div_cancel_left _ hr0]

theorem isSylowTwoOf_slUni [Fintype F] {m : ℕ} (hF : Fintype.card F = 2 ^ m) (hm : 0 < m) :
    IsSylowTwoOf (slUni F) ⊤ := by
  have hU : Nat.card (slUni F) = 2 ^ m := by
    rw [card_slUni, Nat.card_eq_fintype_card, hF]
  refine isSylowTwoOf_of_card_eq le_top (IsPGroup.of_card hU) ?_
  rw [hU, twoPart, Subgroup.card_top, card_specialLinear_two, hF]
  have hodd : ¬ 2 ∣ (2 ^ m) ^ 2 - 1 := by
    have h2 : 2 ∣ (2 ^ m) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
    have h1 : 0 < (2 ^ m) ^ 2 := by positivity
    omega
  rw [Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd]
  simp [Nat.Prime.factorization_pow Nat.prime_two]

theorem dicksonLite [Fintype F] {m : ℕ} (hF : Fintype.card F = 2 ^ m) (hm : 0 < m)
    {P K : Subgroup SL(2, F)} (hP : IsSylowTwoOf P ⊤) (hPK : P ≤ K) :
    K = ⊤ ∨ K ≤ Subgroup.normalizer (P : Set SL(2, F)) := by
  obtain ⟨g, -, hg⟩ := (isSylowTwoOf_slUni hF hm).exists_conj hP
  have hmem : ∀ y : SL(2, F), y ∈ P ↔ g⁻¹ * y * g ∈ slUni F := by
    intro y
    rw [hg]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hu
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  by_cases hN : ∀ x ∈ K, g⁻¹ * x * g ∈ Subgroup.normalizer (slUni F : Set SL(2, F))
  · right
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hN x hx) (g⁻¹ * y * g)
    rw [hmem, hmem]
    rw [h1]
    have e : g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * y * x⁻¹) * g := by group
    rw [e]
  · left
    obtain ⟨x₀, hx₀K, hx₀N⟩ :
        ∃ x ∈ K, g⁻¹ * x * g ∉ Subgroup.normalizer (slUni F : Set SL(2, F)) := by
      by_contra hcon
      exact hN fun x hx => by_contra fun h' => hcon ⟨x, hx, h'⟩
    set K' : Subgroup SL(2, F) := K.map (MulAut.conj g⁻¹).toMonoidHom with hK'
    have hUK' : slUni F ≤ K' := by
      intro u hu
      refine ⟨g * u * g⁻¹, hPK ((hmem _).mpr (by simpa [mul_assoc] using hu)), ?_⟩
      simp [mul_assoc]
    have hK'N : ¬ K' ≤ Subgroup.normalizer (slUni F : Set SL(2, F)) := by
      intro h
      apply hx₀N
      exact h ⟨x₀, hx₀K, by simp [mul_assoc]⟩
    have htop := eq_top_of_slUni_le hUK' hK'N
    rw [eq_top_iff]
    intro x _
    have hx : g⁻¹ * x * g ∈ K' := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := hx
    have : k = x := by
      have := hkx
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, inv_inv] at this
      have h2 : g * (g⁻¹ * k * g) * g⁻¹ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [this]
      simpa [mul_assoc] using h2
    rwa [← this]

end SL2

end CFSG.QuasithinUnique.Lin2
