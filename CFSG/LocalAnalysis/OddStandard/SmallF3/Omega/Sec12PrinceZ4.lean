module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma pow_mod_four {M : Type*} [Monoid M] {y : M} (hy : y ^ 4 = 1) (n : ℕ) :
    y ^ (n % 4) = y ^ n := by
  calc y ^ (n % 4) = y ^ (n % 4) * 1 := (mul_one _).symm
    _ = y ^ (n % 4) * (y ^ 4) ^ (n / 4) := by rw [hy, one_pow]
    _ = y ^ (n % 4) * y ^ (4 * (n / 4)) := by rw [pow_mul]
    _ = y ^ (n % 4 + 4 * (n / 4)) := by rw [pow_add]
    _ = y ^ n := congrArg (fun m => y ^ m) (Nat.mod_add_div n 4)

private lemma pow_val_add {M : Type*} [Monoid M] {y : M} (hy : y ^ 4 = 1) (p q : ZMod 4) :
    y ^ (p + q).val = y ^ p.val * y ^ q.val := by
  rw [ZMod.val_add, pow_mod_four hy, pow_add]

private lemma isEvenVec_zero : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  simp [IsEvenVec]

private lemma isEvenVec_add {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp_rw [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

private lemma isEvenVec_nsmul (v : Fin 5 → ZMod 2) (n : ℕ) (hv : IsEvenVec v) :
    IsEvenVec (n • v) := by
  induction n with
  | zero => simpa using isEvenVec_zero
  | succ n ih => rw [succ_nsmul]; exact isEvenVec_add ih hv

private lemma isEvenVec_sum {ι : Type*} (s : Finset ι) (u : ι → Fin 5 → ZMod 2)
    (h : ∀ i ∈ s, IsEvenVec (u i)) : IsEvenVec (Finset.sum s u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isEvenVec_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact isEvenVec_add (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

private def pw (i : Fin 4) : Fin 5 → ZMod 2 :=
  Pi.single i.castSucc 1 + Pi.single (Fin.last 4) 1

private lemma pw_even (i : Fin 4) : IsEvenVec (pw i) := by
  unfold IsEvenVec pw
  simp_rw [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ j : Fin 5, Pi.single i.castSucc (1 : ZMod 2) j) = 1 := by
    rw [Finset.sum_eq_single i.castSucc (fun b _ hb => by rw [Pi.single_eq_of_ne hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have h2 : (∑ j : Fin 5, Pi.single (Fin.last 4) (1 : ZMod 2) j) = 1 := by
    rw [Finset.sum_eq_single (Fin.last 4) (fun b _ hb => by rw [Pi.single_eq_of_ne hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [h1, h2]
  exact CharTwo.add_self_eq_zero 1

private lemma sum_pw_apply (n : Fin 4 → ℕ) (j : Fin 4) :
    (∑ i, n i • pw i) (j.castSucc) = (n j : ZMod 2) := by
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [Pi.smul_apply, pw, Pi.add_apply, Pi.single_eq_same]
    rw [Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
    rw [add_zero, nsmul_eq_mul, mul_one]
  · intro i _ hij
    have hne : j.castSucc ≠ i.castSucc := fun h => hij (Fin.castSucc_injective 4 h.symm)
    have hne2 : j.castSucc ≠ Fin.last 4 := Fin.castSucc_ne_last j
    rw [Pi.smul_apply, pw, Pi.add_apply, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne2,
      add_zero, smul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

private lemma sum_pw_eq_zero_iff {n : Fin 4 → ℕ} (h : ∑ i, n i • pw i = 0) (j : Fin 4) :
    (n j : ZMod 2) = 0 := by
  have hc : (∑ i, n i • pw i) (j.castSucc) = 0 := by
    simpa using congrFun h j.castSucc
  rwa [sum_pw_apply] at hc

theorem prince_z4_of_sq {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (φ φ₀ : (Fin 5 → ZMod 2) → G) (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hcard : Nat.card ↥V = 256) (hφ : ∀ v, IsEvenVec v → φ v ∈ V)
    (hadd₀ : ∀ v w, IsEvenVec v → IsEvenVec w → φ₀ (v + w) = φ₀ v * φ₀ w)
    (hinj₀ : ∀ v w, IsEvenVec v → IsEvenVec w → φ₀ v = φ₀ w → v = w)
    (hsq : ∀ v, IsEvenVec v → φ v * φ v = φ₀ v) : IsZ4Pow4 V := by
  have h0even : IsEvenVec (0 : Fin 5 → ZMod 2) := isEvenVec_zero
  have hφ₀0 : φ₀ 0 = 1 := by
    have h := hadd₀ 0 0 h0even h0even
    rw [add_zero] at h
    have h1 : 1 * φ₀ 0 = φ₀ 0 * φ₀ 0 := by rw [one_mul]; exact h
    exact (mul_right_cancel h1).symm
  have hsq_one : ∀ v, IsEvenVec v → φ₀ v * φ₀ v = 1 := by
    intro v hv
    rw [← hadd₀ v v hv hv]
    have hv2 : v + v = 0 := by funext j; exact CharTwo.add_self_eq_zero (v j)
    rw [hv2, hφ₀0]
  have hφ₀_nsmul : ∀ v, IsEvenVec v → ∀ n : ℕ, φ₀ (n • v) = φ₀ v ^ n := by
    intro v hv n
    induction n with
    | zero => simp [hφ₀0]
    | succ n ih =>
        rw [succ_nsmul, hadd₀ _ _ (isEvenVec_nsmul v n hv) hv, ih, pow_succ]
  have hφpw_mem : ∀ i : Fin 4, φ₀ (pw i) ∈ V := by
    intro i
    rw [← hsq (pw i) (pw_even i)]
    exact V.mul_mem (hφ _ (pw_even i)) (hφ _ (pw_even i))
  letI : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let x : Fin 4 → ↥V := fun i => ⟨φ (pw i), hφ _ (pw_even i)⟩
  have hx2 : ∀ i, x i ^ 2 = (⟨φ₀ (pw i), hφpw_mem i⟩ : ↥V) := by
    intro i
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two]
    exact hsq (pw i) (pw_even i)
  have hx4 : ∀ i, x i ^ 4 = 1 := by
    intro i
    have hy2 : (⟨φ₀ (pw i), hφpw_mem i⟩ : ↥V) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_two, Subgroup.coe_one]
      exact hsq_one (pw i) (pw_even i)
    calc x i ^ 4 = (x i ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, ← pow_mul]
      _ = (⟨φ₀ (pw i), hφpw_mem i⟩ : ↥V) ^ 2 := by rw [hx2 i]
      _ = 1 := hy2
  let f : (Fin 4 → Multiplicative (ZMod 4)) →* ↥V :=
    { toFun := fun a => ∏ i, x i ^ (Multiplicative.toAdd (a i)).val
      map_one' := by simp
      map_mul' := fun a b => by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        rw [Pi.mul_apply, toAdd_mul]
        exact pow_val_add (hx4 i) _ _ }
  have hsq_prod : ∀ a : Fin 4 → Multiplicative (ZMod 4),
      (f a) ^ 2 = ∏ i, (x i ^ 2) ^ (Multiplicative.toAdd (a i)).val := by
    intro a
    change (∏ i, x i ^ (Multiplicative.toAdd (a i)).val) ^ 2 = _
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    conv_lhs => rw [← pow_mul]
    conv_rhs => rw [← pow_mul]
    rw [Nat.mul_comm]
  have coe_prod_eq : ∀ c : Fin 4 → ℕ,
      (↑(∏ i, (x i ^ 2) ^ (c i)) : G) = φ₀ (∑ i, c i • pw i) := by
    intro c
    suffices h : ∀ s : Finset (Fin 4),
        (↑(Finset.prod s (fun i => (x i ^ 2) ^ (c i))) : G) =
          φ₀ (Finset.sum s (fun i => c i • pw i)) by
      simpa using h Finset.univ
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hφ₀0.symm
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Subgroup.coe_mul, Finset.sum_insert ha]
        rw [hadd₀ _ _ (isEvenVec_nsmul (pw a) (c a) (pw_even a))
          (isEvenVec_sum s (fun i => c i • pw i)
            (fun i _ => isEvenVec_nsmul (pw i) (c i) (pw_even i))), ih]
        rw [Subgroup.coe_pow, hx2 a]
        rw [hφ₀_nsmul (pw a) (pw_even a) (c a)]
  have hker : ∀ a, f a = 1 → a = 1 := by
    intro a ha
    have hm_even : ∀ j, 2 ∣ (Multiplicative.toAdd (a j)).val := by
      intro j
      have h1 : (∏ i, (x i ^ 2) ^ ((Multiplicative.toAdd (a i)).val)) = 1 := by
        rw [← hsq_prod a, ha, one_pow]
      have h2 : φ₀ (∑ i, (Multiplicative.toAdd (a i)).val • pw i) = 1 := by
        have h := coe_prod_eq (fun i => (Multiplicative.toAdd (a i)).val)
        rw [h1] at h
        simpa using h.symm
      have h3 : φ₀ (∑ i, (Multiplicative.toAdd (a i)).val • pw i) = φ₀ 0 := by
        rw [h2, hφ₀0]
      have h4 : (∑ i, (Multiplicative.toAdd (a i)).val • pw i) = 0 :=
        hinj₀ _ _ (isEvenVec_sum Finset.univ _
          (fun i _ => isEvenVec_nsmul (pw i) _ (pw_even i))) h0even h3
      exact (ZMod.natCast_eq_zero_iff _ 2).mp (sum_pw_eq_zero_iff h4 j)
    set c : Fin 4 → ℕ := fun i => (Multiplicative.toAdd (a i)).val / 2 with hc_def
    have hc_even : ∀ j, 2 ∣ c j := by
      intro j
      have hfa : f a = ∏ i, (x i ^ 2) ^ (c i) := by
        change (∏ i, x i ^ (Multiplicative.toAdd (a i)).val) = ∏ i, (x i ^ 2) ^ (c i)
        apply Finset.prod_congr rfl
        intro i _
        have hm_eq : (Multiplicative.toAdd (a i)).val = 2 * c i := by
          rw [hc_def]
          exact (Nat.mul_div_cancel' (hm_even i)).symm
        rw [hm_eq, ← pow_mul]
      have h1 : (∏ i, (x i ^ 2) ^ (c i)) = 1 := by rw [← hfa]; exact ha
      have h2 : φ₀ (∑ i, c i • pw i) = 1 := by
        have h := coe_prod_eq c
        rw [h1] at h
        simpa using h.symm
      have h3 : φ₀ (∑ i, c i • pw i) = φ₀ 0 := by rw [h2, hφ₀0]
      have h4 : (∑ i, c i • pw i) = 0 :=
        hinj₀ _ _ (isEvenVec_sum Finset.univ _
          (fun i _ => isEvenVec_nsmul (pw i) _ (pw_even i))) h0even h3
      exact (ZMod.natCast_eq_zero_iff _ 2).mp (sum_pw_eq_zero_iff h4 j)
    have hc_zero : ∀ j, c j = 0 := by
      intro j
      have hm_eq : (Multiplicative.toAdd (a j)).val = 2 * c j := by
        rw [hc_def]
        exact (Nat.mul_div_cancel' (hm_even j)).symm
      have hm_lt : (Multiplicative.toAdd (a j)).val < 4 := ZMod.val_lt _
      have hlt : c j < 2 := by omega
      rcases hc_even j with ⟨k, hk⟩
      omega
    funext j
    change a j = 1
    rw [← toAdd_eq_zero]
    exact (ZMod.val_eq_zero _).mp (by
      have hm_eq : (Multiplicative.toAdd (a j)).val = 2 * c j := by
        rw [hc_def]
        exact (Nat.mul_div_cancel' (hm_even j)).symm
      rw [hm_eq, hc_zero j, mul_zero])
  have hfinj : Function.Injective f := by
    intro a b hab
    have h : f (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hker _ h)
  have hcard_target : Nat.card (Fin 4 → Multiplicative (ZMod 4)) = 256 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact ⟨(MulEquiv.ofBijective f (hfinj.bijective_of_nat_card_le (by
    rw [hcard, hcard_target]))).symm⟩

end CFSG.OddStandard.SmallF3.Omega
