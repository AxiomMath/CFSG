module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L412B

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem diagSL2_neg_one_eq_neg_one : diagSL2 (-1 : Kˣ) = (-1 : SL(2, K)) := by
  apply Subtype.ext
  rw [coe_diagSL2, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem longSL2_neg_one_eq_longTorus {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {m : ℕ} (F : HypFrame Q m) {i j : Fin m} (hij : i ≠ j)
    (s t : Bool) : F.longSL2 hij s t (-1) = F.longTorus hij s t (-1) := by
  rw [HypFrame.longTorus_apply, diagSL2_neg_one_eq_neg_one]

theorem commute_longTorus_shortRoot {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (u : Bool) (c : K) :
    (oddFrame n K).longTorus hij true true (-1) * (oddFrame n K).shortRoot k u (.ofAdd c) =
      (oddFrame n K).shortRoot k u (.ofAdd c) * (oddFrame n K).longTorus hij true true (-1) := by
  have h := (oddFrame n K).longTorus_conj_shortRoot hij true true (-1) k u c
  have he : longCoroot i j true true k u = 0 := by simp [longCoroot, hki, hkj]
  rw [he, zpow_zero, Units.val_one, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem longTorus_conj_shortRoot_right {i r : Fin n} (hir : i ≠ r) (u : Bool) (c : K) :
    (oddFrame n K).longTorus hir true true (-1) * (oddFrame n K).shortRoot r u (.ofAdd c) *
        ((oddFrame n K).longTorus hir true true (-1))⁻¹ =
      (oddFrame n K).shortRoot r u (.ofAdd (-c)) := by
  have hs : ((((-1 : Kˣ) ^ longCoroot i r true true r u : Kˣ)) : K) = -1 := by
    cases u <;> simp [longCoroot, Ne.symm hir]
  rw [(oddFrame n K).longTorus_conj_shortRoot hir true true (-1) r u c, hs, neg_one_mul]

variable [Finite K]

theorem eq_one_of_forall_insert (hK : Nat.card K = 3) {i₀ i₁ : Fin n} (hij : i₀ ≠ i₁)
    {N : Subgroup (spinGroup (quadOdd n K))}
    (hNn : ∀ c ∈ centralizer ({(oddFrame n K).longSL2 hij true true (-1)} :
      Set (spinGroup (quadOdd n K))), ∀ y ∈ N, c * y * c⁻¹ ∈ N)
    (hcop : Nat.Coprime 2 (Nat.card N))
    (hJ : ∀ s : Bool, ∀ x ∈ N, ∀ A : SL(2, K),
      x * (oddFrame n K).longSL2 hij true s A = (oddFrame n K).longSL2 hij true s A * x)
    (S : Finset (Fin n))
    (IH : ∀ r, r ∉ S → ∀ y ∈ N, (∀ s ∈ insert r S, ∀ hs : i₀ ≠ s,
      y * (oddFrame n K).longTorus hs true true (-1) =
        (oddFrame n K).longTorus hs true true (-1) * y) → y = 1)
    {x : spinGroup (quadOdd n K)} (hx : x ∈ N)
    (hxS : ∀ r ∈ S, ∀ hr : i₀ ≠ r, x * (oddFrame n K).longTorus hr true true (-1) =
      (oddFrame n K).longTorus hr true true (-1) * x) :
    x = 1 := by
  have : Finite (spinGroup (quadOdd n K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _
      (coe_ker_spinMatrix_quadOdd (two_ne_zero_of_card_three hK))
  have h3 : (3 : K) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card, hK] at h
    exact_mod_cast h
  have ht : (oddFrame n K).longSL2 hij true true (-1) =
      (oddFrame n K).longTorus hij true true (-1) :=
    longSL2_neg_one_eq_longTorus _ hij true true
  have hvv : ∀ (r : Fin n) (hr : i₀ ≠ r), (oddFrame n K).longTorus hr true true (-1) *
      (oddFrame n K).longTorus hr true true (-1) = 1 := by
    intro r hr
    rw [← map_mul, show ((-1 : Kˣ) * (-1)) = 1 by simp, map_one]
  have hvC : ∀ (r : Fin n) (hr : i₀ ≠ r), (oddFrame n K).longTorus hr true true (-1) ∈
      centralizer ({(oddFrame n K).longSL2 hij true true (-1)} :
        Set (spinGroup (quadOdd n K))) := by
    intro r hr
    rw [mem_centralizer_singleton_iff, ht]
    exact ((oddFrame n K).commute_longTorus_longTorus hr true true (-1) hij true true (-1)).eq
  have hgC : ∀ r : Fin n, r ≠ i₀ → r ≠ i₁ → ∀ (b : Bool) (c : K),
      (oddFrame n K).shortRoot r b (.ofAdd c) ∈
        centralizer ({(oddFrame n K).longSL2 hij true true (-1)} :
          Set (spinGroup (quadOdd n K))) := by
    intro r hr0 hr1 b c
    rw [mem_centralizer_singleton_iff, ht]
    exact (commute_longTorus_shortRoot hij hr0 hr1 b c).symm
  set M : Subgroup (spinGroup (quadOdd n K)) := N ⊓ ⨅ (r : Fin n) (_ : r ∈ S) (hr : i₀ ≠ r),
    centralizer {(oddFrame n K).longTorus hr true true (-1)} with hM
  have hmemM : ∀ y, y ∈ M ↔ y ∈ N ∧ ∀ r ∈ S, ∀ hr : i₀ ≠ r,
      y * (oddFrame n K).longTorus hr true true (-1) =
        (oddFrame n K).longTorus hr true true (-1) * y := by
    intro y
    simp only [hM, mem_inf, mem_iInf, mem_centralizer_singleton_iff]
  have hxM : x ∈ M := (hmemM x).mpr ⟨hx, hxS⟩
  have hshort : ∀ r : Fin n, r ≠ i₀ → r ≠ i₁ → r ∉ S → ∀ b : Bool,
      x * (oddFrame n K).shortRoot r b (.ofAdd 1) =
        (oddFrame n K).shortRoot r b (.ofAdd 1) * x := by
    intro r hr0 hr1 hrS b
    have hr : i₀ ≠ r := Ne.symm hr0
    have hvM : ∀ y ∈ M, (oddFrame n K).longTorus hr true true (-1) * y *
        ((oddFrame n K).longTorus hr true true (-1))⁻¹ ∈ M := by
      intro y hy
      obtain ⟨hyN, hyS⟩ := (hmemM y).mp hy
      refine (hmemM _).mpr ⟨hNn _ (hvC r hr) y hyN, fun s hs hs0 => ?_⟩
      have cv : Commute ((oddFrame n K).longTorus hr true true (-1))
          ((oddFrame n K).longTorus hs0 true true (-1)) :=
        (oddFrame n K).commute_longTorus_longTorus hr true true (-1) hs0 true true (-1)
      exact ((cv.mul_left (hyS s hs hs0)).mul_left cv.inv_left).eq
    have hfix : ∀ y ∈ M, (oddFrame n K).longTorus hr true true (-1) * y =
        y * (oddFrame n K).longTorus hr true true (-1) → y = 1 := by
      intro y hy hyv
      obtain ⟨hyN, hyS⟩ := (hmemM y).mp hy
      refine IH r hrS y hyN ?_
      intro s hs hs0
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hyv.symm
      · exact hyS s hs hs0
    have hinv : ∀ y ∈ M, (oddFrame n K).longTorus hr true true (-1) * y *
        ((oddFrame n K).longTorus hr true true (-1))⁻¹ = y⁻¹ := fun y hy =>
      conj_eq_inv_of_forall_commute_eq_one (hvv r hr) hvM hfix hy
    have hgM : ∀ y ∈ M, ((oddFrame n K).shortRoot r b (.ofAdd 1))⁻¹ * y *
        (oddFrame n K).shortRoot r b (.ofAdd 1) ∈ M := by
      intro y hy
      obtain ⟨hyN, hyS⟩ := (hmemM y).mp hy
      have hgN := hNn _ (inv_mem (hgC r hr0 hr1 b 1)) y hyN
      rw [inv_inv] at hgN
      refine (hmemM _).mpr ⟨hgN, fun s hs hs0 => ?_⟩
      have hrs : r ≠ s := fun h => hrS (h ▸ hs)
      have cg : Commute ((oddFrame n K).shortRoot r b (.ofAdd 1))
          ((oddFrame n K).longTorus hs0 true true (-1)) :=
        (commute_longTorus_shortRoot hs0 hr0 hrs b 1).symm
      exact ((cg.inv_left.mul_left (hyS s hs hs0)).mul_left cg).eq
    have hcomm := commute_conj_mul_inv_of_inverts (hvv r hr) hinv hgM hxM
    have hw : (oddFrame n K).longTorus hr true true (-1) * (oddFrame n K).shortRoot r b (.ofAdd 1) *
        ((oddFrame n K).longTorus hr true true (-1))⁻¹ *
          ((oddFrame n K).shortRoot r b (.ofAdd 1))⁻¹ =
        (oddFrame n K).shortRoot r b (.ofAdd 1) := by
      rw [longTorus_conj_shortRoot_right hr b 1, ← map_inv, ← map_mul, ← ofAdd_neg,
        ← ofAdd_add, show (-1 + -1 : K) = 1 by linear_combination -h3]
    rw [hw] at hcomm
    exact hcomm
  have hxo : Nat.Coprime 2 (orderOf x) := by
    have h1 : orderOf x ∣ Nat.card N := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_right h1 hcop
  have hJ1 := hJ true x hx
  have hJ2 := hJ false x hx
  refine eq_one_of_commute_three hK hij hxo ?_ ?_ ?_ ?_ ?_
  · have h := hJ1 (upperSL2 1)
    rwa [HypFrame.longSL2_upperSL2] at h
  · have h := hJ2 (upperSL2 1)
    rwa [HypFrame.longSL2_upperSL2] at h
  · have h := hJ1 (lowerSL2 1)
    rwa [HypFrame.longSL2_lowerSL2] at h
  · have h := hJ2 (lowerSL2 1)
    rwa [HypFrame.longSL2_lowerSL2] at h
  · intro r hr hr1
    by_cases hrS : r ∈ S
    · exact Or.inl (hxS r hrS hr)
    · exact Or.inr (hshort r (Ne.symm hr) hr1 hrS)

theorem pPrimeCore_centralizer_longSL2_three (hK : Nat.card K = 3) {i₀ i₁ : Fin n}
    (hij : i₀ ≠ i₁) :
    pPrimeCore 2 ↥(centralizer {(oddFrame n K).longSL2 hij true true (-1)}) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := two_ne_zero_of_card_three hK
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have : Finite (spinGroup (quadOdd n K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ : quadOdd n K ≠ 0 := (nondegenerate_quadOdd n K).ne_zero
  set C := centralizer ({(oddFrame n K).longSL2 hij true true (-1)} :
    Set (spinGroup (quadOdd n K))) with hC
  set N := (pPrimeCore 2 ↥C).map C.subtype with hN
  have hNC : N ≤ C := map_subtype_le _
  have hNn : ∀ c ∈ C, ∀ y ∈ N, c * y * c⁻¹ ∈ N := by
    rintro c hc _ ⟨y, hy, rfl⟩
    have h1 : (⟨c, hc⟩ : ↥C) * y * (⟨c, hc⟩ : ↥C)⁻¹ ∈ pPrimeCore 2 ↥C :=
      (pPrimeCore_normal (p := 2) (G := ↥C)).conj_mem y hy ⟨c, hc⟩
    exact ⟨_, h1, by simp⟩
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    rw [hN, card_map_of_injective C.subtype_injective]
    exact pPrimeCore_coprime_card
  have hzc : spinGroup.negOne (quadOdd n K) hQ ∈ center (spinGroup (quadOdd n K)) :=
    ker_spinAction_le_center _
      ((mem_ker_spinAction_iff _ (nondegenerate_quadOdd n K) _).mpr (Or.inr rfl))
  have hCs : ∀ s : Bool, centralizer ({(oddFrame n K).longSL2 hij true s (-1)} :
      Set (spinGroup (quadOdd n K))) = C := by
    intro s
    cases s
    · have h1 : (oddFrame n K).longSL2 hij true false (-1) =
          spinGroup.negOne (quadOdd n K) hQ * (oddFrame n K).longSL2 hij true true (-1) :=
        longSL2_neg_one_not _ hij hQ true true
      rw [h1]
      exact centralizer_mul_of_mem_center hzc
    · rfl
  have hJ : ∀ s : Bool, ∀ x ∈ N, ∀ A : SL(2, K),
      x * (oddFrame n K).longSL2 hij true s A = (oddFrame n K).longSL2 hij true s A * x := by
    intro s x hx A
    have hle := range_longSL2_le_centralizer (oddFrame n K).toHypFrame hij true s
    rw [hCs] at hle
    have hnorm := normal_range_longSL2_quadOdd hodd (oddFrame n K).toHypFrame hij true s
    rw [hCs, normal_subgroupOf_iff hle] at hnorm
    exact commute_of_normal_of_pPrimeCore_eq_bot hNC hle hNn (fun c hc y hy => hnorm y c hy hc)
      hcop (pPrimeCore_range_sl2_odd hodd _ (longSL2_injective _ hij true s)) hx ⟨A, rfl⟩
  have key : ∀ S : Finset (Fin n), S.card ≤ Fintype.card (Fin n) → ∀ x ∈ N,
      (∀ r ∈ S, ∀ hr : i₀ ≠ r, x * (oddFrame n K).longTorus hr true true (-1) =
        (oddFrame n K).longTorus hr true true (-1) * x) → x = 1 := by
    refine Finset.strongDownwardInduction (p := fun S => ∀ x ∈ N,
      (∀ r ∈ S, ∀ hr : i₀ ≠ r, x * (oddFrame n K).longTorus hr true true (-1) =
        (oddFrame n K).longTorus hr true true (-1) * x) → x = 1) ?_
    intro S IH _ x hx hxS
    exact eq_one_of_forall_insert hK hij hNn hcop hJ S
      (fun r hrS => IH (Finset.card_le_univ _) (Finset.ssubset_insert hrS)) hx hxS
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have h := key ∅ (Finset.card_le_univ _) (y : spinGroup (quadOdd n K)) ⟨y, hy, rfl⟩ (by simp)
  exact Subtype.ext (by rw [h, Subgroup.coe_one])

end CFSG.ComponentClassification.HarrisLit.T1
