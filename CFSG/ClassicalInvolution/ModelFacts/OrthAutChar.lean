module

public import CFSG.LieType.Universal.Spin.Datum

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open CFSG.LieType.Universal.Spin

variable {m : ℕ} {F : Type} [Field F]

theorem sum_toStdD (hm : 2 ≤ m) (ℓ : Fin m) (hℓ : ℓ.val + 1 = m) (γ : Fin m → ℤ) :
    ∑ k, toStdD m γ k = 2 * γ ℓ := by
  let f : (Fin m → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ k, toStdD m v k
      map_zero' := by simp [toStdD_zero]
      map_add' := fun v w => by simp [toStdD_add, Finset.sum_add_distrib] }
  let g : (Fin m → ℤ) →+ ℤ :=
    { toFun := fun v => 2 * v ℓ
      map_zero' := by simp
      map_add' := fun v w => by simp [mul_add] }
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ f g fun k x => ?_
    have hs : (Pi.single k x : Fin m → ℤ) = x • Pi.single k 1 := by
      funext j
      simp [Pi.single_apply]
    change ∑ a, toStdD m (Pi.single k x) a = 2 * (Pi.single k x : Fin m → ℤ) ℓ
    rw [hs, toStdD_smul]
    by_cases h : k.val + 1 < m
    · rw [toStdD_single_of_lt m h]
      have hkℓ : k ≠ ℓ := fun hh => by rw [hh] at h; omega
      simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, hkℓ]
    · rw [toStdD_single_of_not_lt m h hm]
      have hkℓ : k = ℓ := Fin.ext (by omega)
      subst hkℓ
      have hne : (⟨m - 2, by omega⟩ : Fin m) ≠ k := Fin.ne_of_val_ne (by simp only; omega)
      simp [Pi.single_apply, mul_add, Finset.sum_add_distrib]
      ring
  exact DFunLike.congr_fun hfg γ

theorem hom_apply_eq_prod (ψ : Multiplicative (Fin m → ℤ) →* Fˣ) (γ : Fin m → ℤ) :
    ψ (Multiplicative.ofAdd γ) = ∏ a, ψ (Multiplicative.ofAdd (Pi.single a 1)) ^ γ a := by
  have h : γ = ∑ a, γ a • (Pi.single a 1 : Fin m → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [ofAdd_zsmul, map_zpow]

theorem exists_vec_of_hom (h2 : (2 : F) ≠ 0) (ψ : Multiplicative (Fin m → ℤ) →* Fˣ)
    (hψ : ∀ a : Fin m, ψ (Multiplicative.ofAdd (Pi.single a 1)) = 1 ∨
      ψ (Multiplicative.ofAdd (Pi.single a 1)) = -1) :
    ∃ v : Fin m → ZMod 2, ∀ γ : Fin m → ℤ,
      ψ (Multiplicative.ofAdd γ) = 1 ↔ ∑ i, (γ i : ZMod 2) * v i = 0 := by
  classical
  have hne : (-1 : Fˣ) ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun u : Fˣ => (u : F)) h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  refine ⟨fun a => if ψ (Multiplicative.ofAdd (Pi.single a 1)) = 1 then 0 else 1, fun γ => ?_⟩
  have h1 : ψ (Multiplicative.ofAdd γ) = (-1 : Fˣ) ^ (∑ i, γ i *
      (if ψ (Multiplicative.ofAdd (Pi.single i 1)) = 1 then (0 : ℤ) else 1)) := by
    rw [hom_apply_eq_prod, ← Finset.prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases hψ i with h | h
    · rw [h]
      simp
    · rw [h]
      simp [hne]
  have h4 : ∀ M : ℤ, (-1 : Fˣ) ^ M = 1 ↔ Even M := by
    intro M
    rw [neg_one_zpow_eq_ite]
    by_cases he : Even M
    · simp [he]
    · simp [he, hne]
  rw [h1, h4]
  have h3 : ((∑ i, γ i * (if ψ (Multiplicative.ofAdd (Pi.single i 1)) = 1 then (0 : ℤ) else 1) :
      ℤ) : ZMod 2) = ∑ i, (γ i : ZMod 2) *
        (if ψ (Multiplicative.ofAdd (Pi.single i 1)) = 1 then 0 else 1) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [← h3, ZMod.intCast_eq_zero_iff_even]

@[expose] def charPsi (a : Fin m → Fˣ) (μ : Fˣ) (ℓ : Fin m) :
    Multiplicative (Fin m → ℤ) →* Fˣ where
  toFun γ := (∏ k, a k ^ toStdD m (Multiplicative.toAdd γ) k) * μ ^ (-(Multiplicative.toAdd γ ℓ))
  map_one' := by simp [toStdD_zero]
  map_mul' γ δ := by
    simp only [toAdd_mul, toStdD_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, neg_add]
    exact mul_mul_mul_comm _ _ _ _

theorem charPsi_apply (a : Fin m → Fˣ) (μ : Fˣ) (ℓ : Fin m) (γ : Fin m → ℤ) :
    charPsi a μ ℓ (Multiplicative.ofAdd γ) =
      (∏ k, a k ^ toStdD m γ k) * μ ^ (-(γ ℓ)) := rfl

@[expose] def lamOf (a : Fin m → Fˣ) (μ : Fˣ) (k : Fin m) (s : Bool) : F :=
  if s then (a k : F) else (μ : F) * ((a k)⁻¹ : Fˣ)

theorem charPsi_eq_chi (hm : 2 ≤ m) (ℓ : Fin m) (hℓ : ℓ.val + 1 = m) (a : Fin m → Fˣ) (μ : Fˣ)
    {γ : Fin m → ℤ} {i j : Fin m} (s t : Bool)
    (h : toStdD m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    ((charPsi a μ ℓ (Multiplicative.ofAdd γ) : Fˣ) : F) =
      lamOf a μ j t * ((μ : F)⁻¹ * lamOf a μ i s) := by
  classical
  have hsum := sum_toStdD hm ℓ hℓ γ
  rw [h] at hsum
  have hs : ∑ k, ((Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin m → ℤ) k) =
      boolSign s + boolSign t := by
    simp [Pi.single_apply, Finset.sum_add_distrib]
  rw [hs] at hsum
  have hprod : ∏ k, a k ^ toStdD m γ k = a i ^ boolSign s * a j ^ boolSign t := by
    rw [h]
    have e : ∀ (n : Fin m) (x : ℤ), ∏ k, a k ^ (Pi.single n x : Fin m → ℤ) k = a n ^ x := by
      intro n x
      rw [Finset.prod_eq_single n (fun k _ hk => by simp [hk]) (by simp)]
      simp
    simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, e]
  rw [charPsi_apply, hprod]
  have hμ : (μ : F) ≠ 0 := μ.ne_zero
  have hai : (a i : F) ≠ 0 := (a i).ne_zero
  have haj : (a j : F) ≠ 0 := (a j).ne_zero
  cases s <;> cases t
  · have hℓ' : γ ℓ = -1 := by simp at hsum; omega
    simp only [boolSign_false, lamOf, hℓ', Units.val_mul, Units.val_zpow_eq_zpow_val]
    simp
    field_simp
  · have hℓ' : γ ℓ = 0 := by simp at hsum; omega
    simp only [boolSign_false, boolSign_true, lamOf, hℓ', Units.val_mul,
      Units.val_zpow_eq_zpow_val]
    simp
    field_simp
  · have hℓ' : γ ℓ = 0 := by simp at hsum; omega
    simp only [boolSign_false, boolSign_true, lamOf, hℓ', Units.val_mul,
      Units.val_zpow_eq_zpow_val]
    simp
    field_simp
  · have hℓ' : γ ℓ = 1 := by simp at hsum; omega
    simp only [boolSign_true, lamOf, hℓ', Units.val_mul, Units.val_zpow_eq_zpow_val]
    simp
    field_simp

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
