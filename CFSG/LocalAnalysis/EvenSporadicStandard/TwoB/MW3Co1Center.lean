module

public import Certificates.Certificate25050
public import CFSG.Sporadic.Co1.Module.OddBuildBase1

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB.MW3

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Odd CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.Blueprint Matrix

attribute [local irreducible] rr

noncomputable def regsGM : List NativeSporadic.Co1 :=
  runEval [eA, eB, rho3] progM

noncomputable def regM (i : ℕ) : NativeSporadic.Co1 :=
  regsGM.getD i 1

theorem regs_relM : RegsRel mat regsGM regsRowsM := by
  refine runRows_spec mat progM ?_
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 => exact mat_eA
  | 1 => exact mat_eB
  | 2 =>
    rw [initRows3_two, getD_two]
    exact mat_reg 27
  | i + 3 => simp [rowsMatrix_idRows, initRows3]

section

attribute [local irreducible] regsGM regsRowsM

theorem mat_regM (i : ℕ) :
    mat (regM i) = rowsMatrix 24 (rrM i) := by
  have h : ∀ j : ℕ, mat (regsGM.getD j 1) =
      rowsMatrix 24 (regsRowsM[j]?.getD (idRows 24)) := And.right regs_relM
  simpa only [regM, rrM] using h i

end

theorem commOK_facts :
    (∀ i ∈ cycIdx ++ relIdx, mulRows 24 (rrM i) (rr 27) = mulRows 24 (rr 27) (rrM i)) ∧
      mulRows 24 (transposeRows 24 sRows) sInvRows = idRows 24 ∧
      actRows (sumRows relIdx) vec0 = 0 ∧
      addRows (mulRows 24 cRows (sumRows relIdx)) (idRows 24) = eRows := by
  have h := Certificates.certificate25050
  simp only [commOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem regM_mem_centralizer
    {i : ℕ} (hi : i ∈ cycIdx ++ relIdx) :
    regM i ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat_injective
  rw [map_mul, map_mul, mat_regM, show rho3 = reg 27 from rfl, mat_reg 27,
    ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, (commOK_facts.1 i hi)]


theorem rowsMatrix_foldl_addRows (l : List ℕ) (acc : Array ℕ) :
    rowsMatrix 24 (l.foldl (fun acc i => addRows acc (rrM i)) acc) =
      rowsMatrix 24 acc + (l.map fun i => rowsMatrix 24 (rrM i)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons i l ih => rw [List.foldl_cons, ih, rowsMatrix_addRows]; simp [add_assoc]

theorem rowsMatrix_replicate_zero : rowsMatrix 24 (Array.replicate 24 0) = 0 := by
  ext i j
  simp [rowsMatrix_apply, toVecD_zero]

theorem rowsMatrix_sumRows (l : List ℕ) :
    rowsMatrix 24 (sumRows l) = (l.map fun i => rowsMatrix 24 (rrM i)).sum := by
  rw [sumRows, rowsMatrix_foldl_addRows, rowsMatrix_replicate_zero, zero_add]

theorem rowsMatrix_eRows :
    rowsMatrix 24 eRows = vecMulVec (toVecD 24 vec0) (toVecD 24 coef1) +
      vecMulVec (rowsMatrix 24 (rr 27) *ᵥ toVecD 24 vec0) (toVecD 24 coef2) := by
  have hr : rowsMatrix 24 (rr 27) *ᵥ toVecD 24 vec0 = toVecD 24 (actRows (rr 27) vec0) :=
    rowsMatrix_mulVec 24 (rr 27) vec0
  rw [hr]
  ext i j
  rw [rowsMatrix_apply, Matrix.add_apply, vecMulVec_apply, vecMulVec_apply]
  simp only [eRows, Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some, toVecD_xor,
    Pi.add_apply]
  rw [toVecD_apply 24 vec0 i, toVecD_apply 24 (actRows (rr 27) vec0) i]
  split_ifs <;> simp [toVecD_zero]

theorem sRows_getD (j : Fin 24) :
    sRows[j.val]?.getD 0 = actRows (rrM (cycIdx.getD j.val 0)) vec0 := by
  have hlen : cycIdx.length = 24 := rfl
  have hj : j.val < cycIdx.length := lt_of_lt_of_eq j.isLt hlen.symm
  simp [sRows, List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem cycIdx_getD_mem (j : Fin 24) : cycIdx.getD j.val 0 ∈ cycIdx ++ relIdx := by
  have hlen : cycIdx.length = 24 := rfl
  have hj : j.val < cycIdx.length := lt_of_lt_of_eq j.isLt hlen.symm
  rw [List.mem_append, List.getD_eq_getElem _ _ hj]
  exact Or.inl (List.getElem_mem hj)

theorem commutant_rho3
    {N : Matrix (Fin 24) (Fin 24) (ZMod 2)}
    (hN : ∀ d ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1), N * mat d = mat d * N) :
    ∃ a b : ZMod 2, N = a • (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) + b • mat rho3 := by
  obtain ⟨hcomm, hS, hR, hC⟩ := commOK_facts
  have hρ : mat rho3 = rowsMatrix 24 (rr 27) := mat_reg 27
  have hNM : ∀ i ∈ cycIdx ++ relIdx, N * rowsMatrix 24 (rrM i) = rowsMatrix 24 (rrM i) * N := by
    intro i hi
    have := hN _ (regM_mem_centralizer hi)
    rwa [mat_regM] at this
  have hPM : ∀ i ∈ cycIdx ++ relIdx, rowsMatrix 24 (rr 27) * rowsMatrix 24 (rrM i) =
      rowsMatrix 24 (rrM i) * rowsMatrix 24 (rr 27) := by
    intro i hi
    rw [← rowsMatrix_mulRows, ← rowsMatrix_mulRows, hcomm i hi]
  set v : Fin 24 → ZMod 2 := toVecD 24 vec0 with hv
  set R : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 (sumRows relIdx) with hRdef
  have hRsum : R = (relIdx.map fun i => rowsMatrix 24 (rrM i)).sum := rowsMatrix_sumRows relIdx
  have hNR : N * R = R * N := by
    rw [hRsum]
    have : ∀ l : List ℕ, (∀ i ∈ l, N * rowsMatrix 24 (rrM i) = rowsMatrix 24 (rrM i) * N) →
        N * (l.map fun i => rowsMatrix 24 (rrM i)).sum =
          (l.map fun i => rowsMatrix 24 (rrM i)).sum * N := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons i l ih =>
        intro h
        rw [List.map_cons, List.sum_cons, Matrix.mul_add, Matrix.add_mul,
          h i (List.mem_cons_self), ih fun j hj => h j (List.mem_cons_of_mem _ hj)]
    exact this relIdx fun i hi => hNM i (List.mem_append_right _ hi)
  have hRv : R *ᵥ v = 0 := by
    rw [hRdef, hv, rowsMatrix_mulVec]
    exact (congrArg (toVecD 24) hR).trans (toVecD_zero 24)
  have hRu : R *ᵥ (N *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hNR, ← Matrix.mulVec_mulVec, hRv, Matrix.mulVec_zero]
  have hCR : rowsMatrix 24 cRows * R + 1 = rowsMatrix 24 eRows := by
    have := congrArg (rowsMatrix 24) hC
    rwa [rowsMatrix_addRows, rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hu : N *ᵥ v = (rowsMatrix 24 eRows) *ᵥ (N *ᵥ v) := by
    rw [← hCR, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hRu, Matrix.mulVec_zero, zero_add,
      Matrix.one_mulVec]
  set a : ZMod 2 := toVecD 24 coef1 ⬝ᵥ (N *ᵥ v) with ha
  set b : ZMod 2 := toVecD 24 coef2 ⬝ᵥ (N *ᵥ v) with hb
  have hu' : N *ᵥ v = a • v + b • (rowsMatrix 24 (rr 27) *ᵥ v) := by
    conv_lhs => rw [hu, rowsMatrix_eRows, Matrix.add_mulVec, Matrix.vecMulVec_mulVec,
      Matrix.vecMulVec_mulVec]
    simp [ha, hb, hv]
  refine ⟨a, b, ?_⟩
  set N' : Matrix (Fin 24) (Fin 24) (ZMod 2) := N - a • 1 - b • rowsMatrix 24 (rr 27) with hN'
  have hN'v : N' *ᵥ v = 0 := by
    rw [hN', Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hu']
    abel
  have hN'M : ∀ i ∈ cycIdx ++ relIdx, N' * rowsMatrix 24 (rrM i) = rowsMatrix 24 (rrM i) * N' := by
    intro i hi
    rw [hN', Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hNM i hi,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hPM i hi]
  set S : Matrix (Fin 24) (Fin 24) (ZMod 2) := (rowsMatrix 24 sRows)ᵀ with hSdef
  have hSS : S * rowsMatrix 24 sInvRows = 1 := by
    have := congrArg (rowsMatrix 24) hS
    rwa [rowsMatrix_mulRows, rowsMatrix_transposeRows, rowsMatrix_idRows] at this
  have hN'S : N' * S = 0 := by
    ext i j
    have hcol : (fun k => S k j) = rowsMatrix 24 (rrM (cycIdx.getD j.val 0)) *ᵥ v := by
      funext k
      rw [hSdef, Matrix.transpose_apply, rowsMatrix_apply, sRows_getD, actRows, hv,
        ← rowsMatrix_mulVec]
    have h1 : (N' * S) i j = (N' *ᵥ fun k => S k j) i := rfl
    rw [h1, hcol, Matrix.mulVec_mulVec, hN'M _ (cycIdx_getD_mem j), ← Matrix.mulVec_mulVec,
      hN'v, Matrix.mulVec_zero]
    rfl
  have hN'0 : N' = 0 := by
    calc N' = N' * (S * rowsMatrix 24 sInvRows) := by rw [hSS, Matrix.mul_one]
      _ = (N' * S) * rowsMatrix 24 sInvRows := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hN'S, Matrix.zero_mul]
  rw [hρ]
  have h0 : N - a • 1 - b • rowsMatrix 24 (rr 27) = 0 := hN' ▸ hN'0
  have h1 : N - a • (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = b • rowsMatrix 24 (rr 27) :=
    sub_eq_zero.1 h0
  calc N = (N - a • 1) + a • 1 := (sub_add_cancel _ _).symm
    _ = b • rowsMatrix 24 (rr 27) + a • 1 := by rw [h1]
    _ = a • 1 + b • rowsMatrix 24 (rr 27) := add_comm _ _


theorem mat_ne_zero (g : NativeSporadic.Co1) : mat g ≠ 0 := by
  intro h
  have h1 : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = 0 := by
    rw [← map_one mat, ← mul_inv_cancel g, map_mul, h, Matrix.zero_mul]
  have := congrFun (congrFun h1 0) 0
  simp at this

theorem matrix_add_self (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) : M + M = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem eq_one_or_eq_rho3_of_commute
    {ζ : NativeSporadic.Co1}
    (hζ : ∀ d ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1), ζ * d = d * ζ) :
    ζ = 1 ∨ ζ = rho3 := by
  obtain ⟨a, b, hab⟩ := commutant_rho3 (N := mat ζ)
    (fun d hd => by rw [← map_mul, ← map_mul, hζ d hd])
  have hρρ : mat rho3 * mat rho3 = 1 := by rw [← map_mul, rho3_sq, map_one]
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
  · exfalso
    rw [zero_smul, zero_smul, add_zero] at hab
    exact mat_ne_zero ζ hab
  · right
    rw [zero_smul, zero_add, one_smul] at hab
    exact mat_injective hab
  · left
    rw [zero_smul, add_zero, one_smul] at hab
    exact mat_injective (hab.trans (map_one mat).symm)
  · exfalso
    rw [one_smul, one_smul] at hab
    refine mat_ne_zero (ζ * ζ) ?_
    rw [map_mul, hab]
    calc (1 + mat rho3) * (1 + mat rho3) = (1 + 1) + (mat rho3 + mat rho3) := by
          rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
            Matrix.one_mul, hρρ]
          abel
      _ = 0 := by rw [matrix_add_self 1, matrix_add_self (mat rho3), add_zero]

theorem eq_one_or_eq_of_commute_of_isConj
    {r ζ : NativeSporadic.Co1}
    (hr : IsConj rho3 r)
    (hζ : ∀ d ∈ Subgroup.centralizer ({r} : Set NativeSporadic.Co1), ζ * d = d * ζ) :
    ζ = 1 ∨ ζ = r := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hr
  have key : c⁻¹ * ζ * c = 1 ∨ c⁻¹ * ζ * c = rho3 := by
    refine eq_one_or_eq_rho3_of_commute fun d hd => ?_
    have hd' := Subgroup.mem_centralizer_singleton_iff.1 hd
    have hcd : c * d * c⁻¹ ∈ Subgroup.centralizer ({r} : Set NativeSporadic.Co1) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
      calc c * d * c⁻¹ * (c * rho3 * c⁻¹) = c * (d * rho3) * c⁻¹ := by group
        _ = c * (rho3 * d) * c⁻¹ := by rw [hd']
        _ = c * rho3 * c⁻¹ * (c * d * c⁻¹) := by group
    have h := hζ _ hcd
    calc c⁻¹ * ζ * c * d = c⁻¹ * (ζ * (c * d * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * d * c⁻¹) * ζ) * c := by rw [h]
      _ = d * (c⁻¹ * ζ * c) := by group
  rcases key with h | h
  · left
    have : ζ = c * (c⁻¹ * ζ * c) * c⁻¹ := by group
    rw [this, h]; group
  · right
    have : ζ = c * (c⁻¹ * ζ * c) * c⁻¹ := by group
    rw [this, h, hc]

end CFSG.EvenSporadicStandard.TwoB.MW3
