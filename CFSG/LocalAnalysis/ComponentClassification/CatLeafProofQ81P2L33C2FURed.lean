module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LWit
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUAllInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2.PSUTwo

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] : CFSG.oddCore X = pPrimeCore 2 X := by
  unfold CFSG.oddCore pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem pPrimeCore_eq_bot_of_normal {X : Type*} [Group X] [Finite X]
    (hX : pPrimeCore 2 X = ⊥) (M : Subgroup X) [M.Normal] : pPrimeCore 2 ↥M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ((pPrimeCore 2 ↥M).map M.subtype).Normal := inferInstance
  have hc : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥M).map M.subtype)) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact pPrimeCore_coprime_card
  exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp
    (pPrimeCore_eq_bot_iff.mp hX _ hN hc)

theorem false_of_fixed {Y : Type} [Group Y] {a : MulAut Y}
    (hO : pPrimeCore 2 ↥(fixedPoints a) = ⊥)
    (hP : IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)))
    {y : Y} (hy : a y = y) (hy1 : y ≠ 1) {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) : False := by
  obtain ⟨k, hk⟩ := isPGroup_of_pPrimeCore_eq_bot hO hP ⟨y, mem_fixedPoints.mpr hy⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf y ∣ Nat.gcd (2 ^ k) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hym)
  rw [Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm), Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact hy1 h1

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

abbrev PU (h : UnitaryFieldData 2 f K) (n : ℕ) : Type :=
  primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem pPrimeCore_fixed_eq_bot (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (β : MulAut (PU h n)) (hβ : orderOf β = 2) : pPrimeCore 2 ↥(fixedPoints β) = ⊥ := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have : Finite (MulAut (PU h n)) := EvenCatalog.finite_mulAut_primeFormP h
  have h0 := even_unitary_all_involution_full_centralizer_odd_core h hC hn hq
    (H := ⊤) le_top β (mem_top β) hβ
  rw [oddCore_eq_pPrimeCore_two] at h0
  have hM := pPrimeCore_eq_bot_of_normal h0
    ((inner (PU h n)).subgroupOf (⊤ ⊓ centralizer {β}))
  have hcj := UnbalancingLocal.EvenUnitaryComponents.conj_injective_primeFormP h hC hn
  have hle : inner (PU h n) ⊓ centralizer {β} ≤ ⊤ ⊓ centralizer {β} :=
    inf_le_inf_right _ le_top
  have heq : (inner (PU h n) ⊓ centralizer {β}).subgroupOf (⊤ ⊓ centralizer {β}) =
      (inner (PU h n)).subgroupOf (⊤ ⊓ centralizer {β}) := by
    ext x
    simp only [mem_subgroupOf, mem_inf]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (mem_inf.mp x.2).2⟩⟩
  let e : ↥(fixedPoints β) ≃* ↥((inner (PU h n)).subgroupOf (⊤ ⊓ centralizer {β})) :=
    (CatLeafProof.fixedInnerEquiv hcj β).trans ((Subgroup.subgroupOfEquivOfLe hle).symm.trans
      (MulEquiv.subgroupCongr heq))
  have hmap := pPrimeCore_map_iso 2 e
  rw [hM] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

theorem exists_isometry_order_three {k : Type} [Field k] [CharP k 2]
    {C : Matrix (Fin n) (Fin n) k} (hCt : Cᵀ = C) (hC2 : C * C = 1) {u v : Fin n → k}
    (hu : u ⬝ᵥ (C *ᵥ u) = 0) (hv : v ⬝ᵥ (C *ᵥ v) = 0) (huv : u ⬝ᵥ (C *ᵥ v) = 1) :
    ∃ g ∈ matrixIsometryGroup C, g ≠ 1 ∧ g ^ 3 = 1 := by
  have hvu : v ⬝ᵥ (C *ᵥ u) = 1 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hCt, dotProduct_comm, huv]
  have hA := unipotentGL_mem hCt hC2 hu 1
  have hB := unipotentGL_mem hCt hC2 hv 1
  set A := FourGroupEvenCanonical.unipotentGL (nilMatrix C 1 u)
    (nilMatrix_mul_nilMatrix_eq_zero C 1 1 hu) with hAdef
  set B := FourGroupEvenCanonical.unipotentGL (nilMatrix C 1 v)
    (nilMatrix_mul_nilMatrix_eq_zero C 1 1 hv) with hBdef
  have hAm : (A : Matrix (Fin n) (Fin n) k) = 1 + vecMulVec (C *ᵥ u) u := by
    rw [hAdef, FourGroupEvenCanonical.coe_unipotentGL, nilMatrix, one_smul]
  have hBm : (B : Matrix (Fin n) (Fin n) k) = 1 + vecMulVec (C *ᵥ v) v := by
    rw [hBdef, FourGroupEvenCanonical.coe_unipotentGL, nilMatrix, one_smul]
  have haa : vecMulVec (C *ᵥ u) u * vecMulVec (C *ᵥ u) u = 0 := by
    simp only [vecMulVec_mul_vecMulVec, hu, zero_smul, vecMulVec_zero]
  have hbb : vecMulVec (C *ᵥ v) v * vecMulVec (C *ᵥ v) v = 0 := by
    simp only [vecMulVec_mul_vecMulVec, hv, zero_smul, vecMulVec_zero]
  have haba : vecMulVec (C *ᵥ u) u * vecMulVec (C *ᵥ v) v * vecMulVec (C *ᵥ u) u =
      vecMulVec (C *ᵥ u) u := by
    simp only [vecMulVec_mul_vecMulVec, huv, hvu, one_smul]
  have hbab : vecMulVec (C *ᵥ v) v * vecMulVec (C *ᵥ u) u * vecMulVec (C *ᵥ v) v =
      vecMulVec (C *ᵥ v) v := by
    simp only [vecMulVec_mul_vecMulVec, huv, hvu, one_smul]
  refine ⟨A * B, mul_mem hA hB, ?_, ?_⟩
  · intro h1
    have h1' : (1 + vecMulVec (C *ᵥ u) u) * (1 + vecMulVec (C *ᵥ v) v) = 1 := by
      rw [← hAm, ← hBm, ← Units.val_mul, h1, Units.val_one]
    have hab : vecMulVec (C *ᵥ u) u = vecMulVec (C *ᵥ v) v := by
      have h2 : (1 + vecMulVec (C *ᵥ u) u) * ((1 + vecMulVec (C *ᵥ u) u) *
          (1 + vecMulVec (C *ᵥ v) v)) = 1 + vecMulVec (C *ᵥ u) u := by
        rw [h1', Matrix.mul_one]
      rw [← Matrix.mul_assoc, FourGroupEvenCanonical.one_add_mul_self haa, Matrix.one_mul] at h2
      exact (add_left_cancel h2).symm
    have hCu : C *ᵥ u ≠ 0 := fun h0 => by
      rw [h0, dotProduct_zero] at hvu
      exact zero_ne_one hvu
    have hu0 : u ≠ 0 := fun h0 => by
      rw [h0, zero_dotProduct] at huv
      exact zero_ne_one huv
    apply vecMulVec_ne_zero hCu hu0
    calc vecMulVec (C *ᵥ u) u
        = vecMulVec (C *ᵥ u) u * vecMulVec (C *ᵥ v) v * vecMulVec (C *ᵥ u) u := haba.symm
      _ = 0 := by rw [← hab, haa, Matrix.zero_mul]
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_mul, hAm, hBm, Units.val_one]
    exact pow_three_of_rel FourGroupEvenCanonical.matrix_add_self haa hbb haba hbab

theorem exists_fixed_order_three_of_bar (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (β : MulAut (PU h n)) (hβ : orderOf β = 2)
    (hbar : ∀ x, primeFormFieldFactor h isPrimeFormGram_one hn hq β x = h.bar x) :
    ∃ y : PU h n, β y = y ∧ y ≠ 1 ∧ y ^ 3 = 1 := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθβ⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hn hq β hβ hbar
  have := UnitaryFieldTransfer.fixedField_charP h
  have h11 : (1 : h.fixedField) + 1 = 0 := CharTwo.add_self_eq_zero 1
  obtain ⟨Cl, hCl, g, hg, hg1, hg3⟩ : ∃ Cl : GL (Fin n) h.fixedField,
      (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C₀ ∧
      ∃ g ∈ matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField), g ≠ 1 ∧
        g ^ 3 = 1 := by
    rcases hcase₀ with h1 | ⟨r, hr, hJ⟩
    · refine ⟨1, by rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), h1], ?_⟩
      rw [Units.val_one]
      have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
      have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
      refine exists_isometry_order_three transpose_one (Matrix.one_mul 1)
        (u := Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1)
        (v := Pi.single ⟨1, by omega⟩ 1 + Pi.single ⟨2, by omega⟩ 1) ?_ ?_ ?_
      · simp [h01, h01.symm, h11]
      · simp [h12, h12.symm, h11]
      · simp [h01.symm, h02.symm, h12.symm]
    · refine ⟨blockSwapGL (K := h.fixedField) (r := r) (by omega), ?_, ?_⟩
      · rw [coe_blockSwapGL, hJ]
        ext i j
        simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
        split_ifs <;> simp
      · rw [coe_blockSwapGL]
        have h0 : 0 < n := by omega
        have hrn : r < n := by omega
        have hJapp : ∀ i j : Fin n, (blockSwapJ n r : Matrix (Fin n) (Fin n) h.fixedField) i j =
            if (j : ℕ) = i + r ∨ (i : ℕ) = j + r then 1 else 0 := fun _ _ => rfl
        refine exists_isometry_order_three blockSwapJ_transpose (blockSwapJ_mul_self (by omega))
          (u := Pi.single ⟨0, h0⟩ 1) (v := Pi.single ⟨r, hrn⟩ 1) ?_ ?_ ?_
        · rw [mulVec_single_one, single_dotProduct, one_mul]
          change (blockSwapJ n r : Matrix (Fin n) (Fin n) h.fixedField) ⟨0, h0⟩ ⟨0, h0⟩ = 0
          rw [hJapp]
          exact ite_eq_right_iff.mpr fun hc => absurd hc (by omega)
        · rw [mulVec_single_one, single_dotProduct, one_mul]
          change (blockSwapJ n r : Matrix (Fin n) (Fin n) h.fixedField) ⟨r, hrn⟩ ⟨r, hrn⟩ = 0
          rw [hJapp]
          exact ite_eq_right_iff.mpr fun hc => absurd hc (by omega)
        · rw [mulVec_single_one, single_dotProduct, one_mul]
          change (blockSwapJ n r : Matrix (Fin n) (Fin n) h.fixedField) ⟨0, h0⟩ ⟨r, hrn⟩ = 1
          rw [hJapp]
          exact ite_eq_left_iff.mpr fun hc => absurd (Or.inl (Nat.zero_add r).symm) hc
  refine ⟨θ (fixedIsometryProj h hCl ⟨g, hg⟩), ?_, ?_, ?_⟩
  · rw [hθβ, MulEquiv.symm_apply_apply, primeFormFieldAut_fixedIsometryProj h hCl hC₀ hbar]
  · intro h1
    apply hg1
    have h2 : fixedIsometryProj h hCl ⟨g, hg⟩ = 1 := θ.injective (by rw [h1, map_one])
    have h3 : (⟨g, hg⟩ : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) = 1 :=
      fixedIsometryProj_injective h hCl hn (by rw [h2, map_one])
    exact congrArg Subtype.val h3
  · have h3 : (⟨g, hg⟩ : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) ^ 3 =
        1 := Subtype.ext (by rw [SubgroupClass.coe_pow, hg3, OneMemClass.coe_one])
    rw [← map_pow, ← map_pow, h3, map_one, map_one]

end CFSG.ComponentClassification.HarrisLit.L33.C2.PSUTwo
