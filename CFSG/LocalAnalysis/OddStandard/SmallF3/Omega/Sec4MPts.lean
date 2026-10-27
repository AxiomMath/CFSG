module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4AData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private instance instDecidableIsEvenVec {n : ℕ} (v : Fin n → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

@[expose] def sec4MW (i : Fin 7) : Fin 7 → ZMod 2 := fun j => if j = i then 0 else 1

@[expose] def sec4MV : Option (Fin 7) → Fin 7 → ZMod 2
  | none => 0
  | some i => sec4MW i

private lemma sec4MW_apply (i j : Fin 7) : sec4MW i j = if j = i then 0 else 1 := rfl

private lemma sec4MV_none : sec4MV (none : Option (Fin 7)) = 0 := rfl

private lemma sec4MV_some (i : Fin 7) : sec4MV (some i) = sec4MW i := rfl

theorem sec4MW_even (i : Fin 7) : IsEvenVec (sec4MW i) := by
  fin_cases i <;> decide +kernel

theorem sec4MW_weight (i : Fin 7) : vecWeight (sec4MW i) = 6 := by
  fin_cases i <;> decide +kernel

theorem sec4MV_even (p : Option (Fin 7)) : IsEvenVec (sec4MV p) := by
  cases p with
  | none => rw [sec4MV_none]; simp [IsEvenVec]
  | some i => rw [sec4MV_some]; exact sec4MW_even i

theorem sec4MV_injective : Function.Injective sec4MV := by
  intro p q h
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some j =>
      exfalso
      have hw := congrArg vecWeight h
      rw [sec4MV_none, sec4MV_some, sec4MW_weight j] at hw
      have h0 : vecWeight (0 : Fin 7 → ZMod 2) = 0 := by simp [vecWeight]
      rw [h0] at hw
      exact absurd hw (by decide)
  | some i =>
    cases q with
    | none =>
      exfalso
      have hw := congrArg vecWeight h
      rw [sec4MV_none, sec4MV_some, sec4MW_weight i] at hw
      have h0 : vecWeight (0 : Fin 7 → ZMod 2) = 0 := by simp [vecWeight]
      rw [h0] at hw
      exact absurd hw (by decide)
    | some j =>
      rw [sec4MV_some, sec4MV_some] at h
      have hi : sec4MW j i = 0 := by
        have h1 : sec4MW i i = sec4MW j i := congr_fun h i
        have h0 : sec4MW i i = 0 := by rw [sec4MW_apply, if_pos rfl]
        rw [h0] at h1
        exact h1.symm
      by_cases hij : i = j
      · exact congrArg some hij
      · exfalso
        have h2 : sec4MW j i = 1 := by rw [sec4MW_apply, if_neg hij]
        rw [h2] at hi
        exact absurd hi (by decide)

theorem permVec_sec4MV (σ : Equiv.Perm (Fin 7)) (p : Option (Fin 7)) :
    permVec σ (sec4MV p) = sec4MV (Equiv.optionCongr σ p) := by
  cases p with
  | none => funext j; simp [permVec, sec4MV_none, Equiv.optionCongr_apply]
  | some i =>
    funext j
    simp only [permVec, Function.comp_apply, sec4MV_some, Equiv.optionCongr_apply,
      Option.map_some, sec4MW_apply]
    by_cases h : (σ.symm) j = i
    · rw [if_pos h, if_pos ((Equiv.symm_apply_eq σ).mp h)]
    · rw [if_neg h, if_neg (fun hj => h ((Equiv.symm_apply_eq σ).mpr hj))]

theorem exists_sec4MW_of_weight_six {v : Fin 7 → ZMod 2} (hv : IsEvenVec v)
    (h6 : vecWeight v = 6) : ∃ i, v = sec4MW i := by
  classical
  unfold vecWeight at h6
  have hcard : (Finset.univ.filter fun j => ¬ v j ≠ 0).card = 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun j => v j ≠ 0)
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i, ?_⟩
  funext j
  by_cases hj : j = i
  · rw [hj]
    have hvi : v i = 0 := by
      have hmem : i ∈ (Finset.univ.filter fun j => ¬ v j ≠ 0) := by rw [hi]; simp
      simpa using hmem
    rw [hvi, sec4MW_apply, if_pos rfl]
  · have hvj : v j = 1 := by
      apply zmod2_eq_one_of_ne_zero
      intro hv0
      have hmem : j ∈ (Finset.univ.filter fun j => ¬ v j ≠ 0) := by simp [hv0]
      rw [hi] at hmem
      exact hj (by simpa using hmem)
    rw [hvj, sec4MW_apply, if_neg hj]

theorem sec4MV_weight_four {p q r s : Option (Fin 7)} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    vecWeight (sec4MV p + sec4MV q + sec4MV r + sec4MV s) = 4 := by
  decide +kernel +revert

variable {G : Type} [Group G]

@[expose] def sec4MPt (t : G) (φ : (Fin 7 → ZMod 2) → G) (p : Option (Fin 7)) : G :=
  t * φ (sec4MV p)

variable {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G} {φ : (Fin 7 → ZMod 2) → G}

theorem sec4MPt_mem_A (hD : Sec4AData t L S z A B φ) (p : Option (Fin 7)) :
    sec4MPt t φ p ∈ A := by
  rw [sec4MPt]
  have htA : t ∈ A := by
    rw [hD.A_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hb : φ (sec4MV p) ∈ B := hD.bdata.perm.mem (sec4MV_even p)
  have hBA : B ≤ A := by rw [hD.A_eq]; exact le_sup_left
  exact A.mul_mem htA (hBA hb)

theorem sec4MPt_mul (hD : Sec4AData t L S z A B φ) (p q : Option (Fin 7)) :
    sec4MPt t φ p * sec4MPt t φ q = φ (sec4MV p + sec4MV q) := by
  haveI : IsMulCommutative ↥A := hD.isMax.2.1.1
  have htA : t ∈ A := by
    rw [hD.A_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hpa : φ (sec4MV p) ∈ A := by
    have hb : φ (sec4MV p) ∈ B := hD.bdata.perm.mem (sec4MV_even p)
    rw [hD.A_eq]; exact Subgroup.mem_sup_left hb
  have hqa : φ (sec4MV q) ∈ A := by
    have hb : φ (sec4MV q) ∈ B := hD.bdata.perm.mem (sec4MV_even q)
    rw [hD.A_eq]; exact Subgroup.mem_sup_left hb
  have hta : t * φ (sec4MV p) = φ (sec4MV p) * t :=
    congrArg Subtype.val (mul_comm' (⟨t, htA⟩ : A) (⟨φ (sec4MV p), hpa⟩ : A))
  have ht2 : t * t = 1 := by
    simpa [pow_two] using hD.isMax.2.1.2 t htA
  rw [sec4MPt, sec4MPt,
    hD.bdata.perm.1 (sec4MV p) (sec4MV q) (sec4MV_even p) (sec4MV_even q)]
  calc (t * φ (sec4MV p)) * (t * φ (sec4MV q))
      = (φ (sec4MV p) * t) * (t * φ (sec4MV q)) := by rw [hta]
    _ = φ (sec4MV p) * (t * (t * φ (sec4MV q))) := by rw [mul_assoc]
    _ = φ (sec4MV p) * φ (sec4MV q) := by
      rw [← mul_assoc t t (φ (sec4MV q)), ht2, one_mul]

theorem sec4MPt_mul_four (hD : Sec4AData t L S z A B φ) (p q r s : Option (Fin 7)) :
    sec4MPt t φ p * sec4MPt t φ q * (sec4MPt t φ r * sec4MPt t φ s) =
      φ (sec4MV p + sec4MV q + sec4MV r + sec4MV s) := by
  rw [sec4MPt_mul hD p q, sec4MPt_mul hD r s, add_assoc]
  rw [hD.bdata.perm.1 (sec4MV p + sec4MV q) (sec4MV r + sec4MV s)
    (isEvenVec_add (sec4MV_even p) (sec4MV_even q))
    (isEvenVec_add (sec4MV_even r) (sec4MV_even s))]

theorem sec4MPt_injective (hD : Sec4AData t L S z A B φ) :
    Function.Injective (sec4MPt t φ) := by
  intro p q h
  rw [sec4MPt, sec4MPt] at h
  apply sec4MV_injective
  exact hD.bdata.perm.2.1 (sec4MV p) (sec4MV q) (sec4MV_even p) (sec4MV_even q)
    (mul_left_cancel h)

theorem sec4MPt_mul_self (hD : Sec4AData t L S z A B φ) (p : Option (Fin 7)) :
    sec4MPt t φ p * sec4MPt t φ p = 1 := by
  simpa [pow_two] using hD.isMax.2.1.2 (sec4MPt t φ p) (sec4MPt_mem_A hD p)

end CFSG.OddStandard.SmallF3.Omega
