module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open scoped commutatorElement

variable {n : ℕ} {K : Type*} [Field K]

section BlockDiag

theorem blockComplProj_mul_self (I : Finset (Fin n)) :
    blockComplProj (K := K) I * blockComplProj I = blockComplProj I := by
  rw [blockComplProj, diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem blockComplProj_compl (I : Finset (Fin n)) :
    blockComplProj (K := K) Iᶜ = 1 - blockComplProj I := by
  ext i j
  rw [blockComplProj, blockComplProj, Matrix.sub_apply, diagonal_apply, diagonal_apply, one_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ I <;> simp [hi]
  · simp [hij]

@[expose] def blockDiagSL (I : Finset (Fin n)) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {M | (M : Matrix (Fin n) (Fin n) K) * blockComplProj I =
    blockComplProj I * (M : Matrix (Fin n) (Fin n) K)}
  one_mem' := by
    show ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * blockComplProj I =
      blockComplProj I * ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one]
  mul_mem' {M N} hM hN := by
    have hM' : (M : Matrix (Fin n) (Fin n) K) * blockComplProj I =
        blockComplProj I * (M : Matrix (Fin n) (Fin n) K) := hM
    have hN' : (N : Matrix (Fin n) (Fin n) K) * blockComplProj I =
        blockComplProj I * (N : Matrix (Fin n) (Fin n) K) := hN
    show ((M * N : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * blockComplProj I =
      blockComplProj I * ((M * N : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hN', ← Matrix.mul_assoc, hM',
      Matrix.mul_assoc]
  inv_mem' {M} hM := by
    have hM' : (M : Matrix (Fin n) (Fin n) K) * blockComplProj I =
        blockComplProj I * (M : Matrix (Fin n) (Fin n) K) := hM
    show ((M⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * blockComplProj I =
      blockComplProj I * ((M⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    set M' := ((M⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM'def
    have h1 : M' * (M : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [hM'def, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h2 : (M : Matrix (Fin n) (Fin n) K) * M' = 1 := by
      rw [hM'def, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    calc M' * blockComplProj I = M' * blockComplProj I * ((M : Matrix (Fin n) (Fin n) K) * M') := by
          rw [h2, Matrix.mul_one]
      _ = M' * (blockComplProj I * (M : Matrix (Fin n) (Fin n) K)) * M' := by
          simp only [Matrix.mul_assoc]
      _ = M' * ((M : Matrix (Fin n) (Fin n) K) * blockComplProj I) * M' := by rw [hM']
      _ = (M' * (M : Matrix (Fin n) (Fin n) K)) * blockComplProj I * M' := by
          simp only [Matrix.mul_assoc]
      _ = blockComplProj I * M' := by rw [h1, Matrix.one_mul]

theorem mem_blockDiagSL_iff_mul {I : Finset (Fin n)} {M : SpecialLinearGroup (Fin n) K} :
    M ∈ blockDiagSL I ↔ (M : Matrix (Fin n) (Fin n) K) * blockComplProj I =
      blockComplProj I * (M : Matrix (Fin n) (Fin n) K) :=
  Iff.rfl

theorem mem_blockDiagSL {I : Finset (Fin n)} {M : SpecialLinearGroup (Fin n) K} :
    M ∈ blockDiagSL I ↔ ∀ i j, (i ∈ I ↔ j ∉ I) → (M : Matrix (Fin n) (Fin n) K) i j = 0 := by
  rw [mem_blockDiagSL_iff_mul, ← Matrix.ext_iff]
  simp only [blockComplProj, mul_diagonal, diagonal_mul]
  constructor
  · intro h i j hij
    have h1 := h i j
    by_cases hi : i ∈ I
    · have hj : j ∉ I := hij.1 hi
      simpa [hi, hj] using h1
    · have hj : j ∈ I := by
        by_contra hj
        exact hi (hij.2 hj)
      simpa [hi, hj] using h1.symm
  · intro h i j
    by_cases hi : i ∈ I <;> by_cases hj : j ∈ I
    · simp [hi, hj]
    · rw [h i j ⟨fun _ => hj, fun _ => hi⟩]
      simp
    · rw [h i j ⟨fun h' => absurd h' hi, fun h' => absurd hj h'⟩]
      simp
    · simp [hi, hj]

theorem blockSpecialLinear_le_blockDiagSL (I : Finset (Fin n)) :
    blockSpecialLinear (K := K) I ≤ blockDiagSL I := by
  intro M hM
  rw [mem_blockDiagSL_iff_mul]
  obtain ⟨h1, h2⟩ := mem_blockSpecialLinear_iff_mul.1 hM
  rw [h1, h2]

theorem blockSpecialLinear_compl_le_blockDiagSL (I : Finset (Fin n)) :
    blockSpecialLinear (K := K) Iᶜ ≤ blockDiagSL I := by
  intro M hM
  rw [mem_blockDiagSL_iff_mul]
  obtain ⟨h1, h2⟩ := mem_blockSpecialLinear_iff_mul.1 hM
  rw [blockComplProj_compl] at h1 h2
  have h3 : (M : Matrix (Fin n) (Fin n) K) * blockComplProj I =
      (M : Matrix (Fin n) (Fin n) K) - (1 - blockComplProj I) := by
    rw [← h1, Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]
  have h4 : blockComplProj I * (M : Matrix (Fin n) (Fin n) K) =
      (M : Matrix (Fin n) (Fin n) K) - (1 - blockComplProj I) := by
    rw [← h2, Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel]
  rw [h3, h4]

end BlockDiag

section Idempotent

variable {R : Type*} [Ring R] {p m m' : R}

theorem idem_split_mul (hp : p * p = p) (hm : m * p = p * m) :
    (m * (1 - p) + p) * (m * p + (1 - p)) = m := by
  have hpm : p * m = m * p := hm.symm
  have e1 : m * p * (m * p) = m * m * p := by
    calc m * p * (m * p) = m * (p * m) * p := by noncomm_ring
      _ = m * m * (p * p) := by rw [hpm]; noncomm_ring
      _ = m * m * p := by rw [hp]
  have e2 : p * (m * p) = m * p := by rw [← mul_assoc, hpm, mul_assoc, hp]
  calc (m * (1 - p) + p) * (m * p + (1 - p))
      = m * m * p - m * p * (m * p) + m - m * p - m * p + m * (p * p) + p * (m * p) + p -
          p * p := by
        noncomm_ring
    _ = m := by rw [e1, e2, hp]; abel

theorem idem_block_mul (hp : p * p = p) (hm' : m' * p = p * m') :
    m * m' * (1 - p) + p = (m * (1 - p) + p) * (m' * (1 - p) + p) := by
  have hpm' : p * m' = m' * p := hm'.symm
  have e1 : m * (1 - p) * (m' * (1 - p)) = m * m' * (1 - p) := by
    calc m * (1 - p) * (m' * (1 - p)) = m * m' * (1 - p) - m * (p * m') + m * (p * m') * p := by
          noncomm_ring
      _ = m * m' * (1 - p) := by
          have e : m * (m' * p) * p = m * (m' * p) := by
            rw [mul_assoc m, mul_assoc m', hp]
          rw [hpm', e]
          abel
  have e2 : m * (1 - p) * p = 0 := by
    rw [mul_assoc, sub_mul, one_mul, hp, sub_self, mul_zero]
  have e3 : p * (m' * (1 - p)) = 0 := by
    rw [← mul_assoc, hpm', mul_assoc, mul_sub, mul_one, hp, sub_self, mul_zero]
  calc m * m' * (1 - p) + p = m * (1 - p) * (m' * (1 - p)) + m * (1 - p) * p +
        p * (m' * (1 - p)) + p * p := by rw [e1, e2, e3, hp, add_zero, add_zero]
    _ = (m * (1 - p) + p) * (m' * (1 - p) + p) := by noncomm_ring

theorem idem_block_left (hp : p * p = p) (hm : m * p = p * m) :
    (m * (1 - p) + p) * p = p ∧ p * (m * (1 - p) + p) = p := by
  refine ⟨?_, ?_⟩
  · rw [add_mul, hp, mul_assoc, sub_mul, one_mul, hp, sub_self, mul_zero, zero_add]
  · rw [mul_add, hp, ← mul_assoc, ← hm, mul_assoc, mul_sub, mul_one, hp, sub_self, mul_zero,
      zero_add]

theorem idem_block_right (hp : p * p = p) (hm : m * p = p * m) :
    (m * p + (1 - p)) * (1 - p) = 1 - p ∧ (1 - p) * (m * p + (1 - p)) = 1 - p := by
  have h1 : (1 - p) * (1 - p) = 1 - p := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hp, sub_self, sub_zero]
  refine ⟨?_, ?_⟩
  · rw [add_mul, h1, mul_assoc, mul_sub, mul_one, hp, sub_self, mul_zero, zero_add]
  · rw [mul_add, h1, ← mul_assoc, sub_mul, one_mul, ← hm, sub_mul, mul_assoc, hp, sub_self,
      zero_add]

end Idempotent

section BlockDet

@[expose] noncomputable def blockDetHom (I : Finset (Fin n)) : blockDiagSL (K := K) I →* K where
  toFun M := ((M : Matrix (Fin n) (Fin n) K) * (1 - blockComplProj I) + blockComplProj I).det
  map_one' := by
    simp only [OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul,
      sub_add_cancel, det_one]
  map_mul' M N := by
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [idem_block_mul (blockComplProj_mul_self I) (mem_blockDiagSL_iff_mul.1 N.2), det_mul]

theorem mem_sup_of_blockDetHom_eq_one {I : Finset (Fin n)} (M : blockDiagSL (K := K) I)
    (hM : blockDetHom I M = 1) :
    (M : SpecialLinearGroup (Fin n) K) ∈ blockSpecialLinear I ⊔ blockSpecialLinear Iᶜ := by
  set P := blockComplProj (K := K) I with hP
  set m := ((M : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) with hm
  have hPP : P * P = P := blockComplProj_mul_self I
  have hmP : m * P = P * m := mem_blockDiagSL_iff_mul.1 M.2
  set X : SpecialLinearGroup (Fin n) K := ⟨m * (1 - P) + P, hM⟩ with hX
  have hsplit := idem_split_mul hPP hmP
  have hdetY : (m * P + (1 - P)).det = 1 := by
    have h := congrArg Matrix.det hsplit
    rw [det_mul, hm, Matrix.SpecialLinearGroup.det_coe] at h
    have hX1 : (m * (1 - P) + P).det = 1 := hM
    rw [hX1, one_mul] at h
    exact h
  set Y : SpecialLinearGroup (Fin n) K := ⟨m * P + (1 - P), hdetY⟩ with hY
  have hXI : X ∈ blockSpecialLinear I :=
    mem_blockSpecialLinear_iff_mul.2 (idem_block_left hPP hmP)
  have hYI : Y ∈ blockSpecialLinear Iᶜ := by
    rw [mem_blockSpecialLinear_iff_mul, blockComplProj_compl]
    exact idem_block_right hPP hmP
  have hXY : X * Y = M := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact hsplit)
  rw [← hXY]
  exact mul_mem (mem_sup_left hXI) (mem_sup_right hYI)

theorem commutator_blockDiagSL_le (I : Finset (Fin n)) :
    ⁅blockDiagSL (K := K) I, blockDiagSL (K := K) I⁆ ≤
      blockSpecialLinear I ⊔ blockSpecialLinear Iᶜ := by
  rw [Subgroup.commutator_le]
  intro M hM N hN
  set M' : blockDiagSL (K := K) I := ⟨M, hM⟩
  set N' : blockDiagSL (K := K) I := ⟨N, hN⟩
  have h : blockDetHom I ⁅M', N'⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul]
    calc blockDetHom I M' * blockDetHom I N' * blockDetHom I M'⁻¹ * blockDetHom I N'⁻¹
        = blockDetHom I (M' * M'⁻¹) * blockDetHom I (N' * N'⁻¹) := by
          rw [map_mul, map_mul]
          ring
      _ = 1 := by rw [mul_inv_cancel, mul_inv_cancel, map_one, one_mul]
  have := mem_sup_of_blockDetHom_eq_one ⁅M', N'⁆ h
  simpa [M', N', commutatorElement_def] using this

end BlockDet

section Fix

@[expose] def fixAut {H : Type*} [Group H] (β : MulAut H) : Subgroup H where
  carrier := {x | β x = x}
  one_mem' := map_one β
  mul_mem' {x y} hx hy := by
    have hx' : β x = x := hx
    have hy' : β y = y := hy
    show β (x * y) = x * y
    rw [map_mul, hx', hy']
  inv_mem' {x} hx := by
    have hx' : β x = x := hx
    show β x⁻¹ = x⁻¹
    rw [map_inv, hx']

theorem mem_fixAut {H : Type*} [Group H] {β : MulAut H} {x : H} : x ∈ fixAut β ↔ β x = x :=
  Iff.rfl

theorem ne_zero_of_coe_eq_diagonal (D : GL (Fin n) K) {d : Fin n → K}
    (hD : (D : Matrix (Fin n) (Fin n) K) = diagonal d) (i : Fin n) : d i ≠ 0 := by
  intro h0
  have h := congrFun (congrFun (Units.mul_inv D) i) i
  rw [hD, diagonal_mul, one_apply_eq, h0, zero_mul] at h
  exact zero_ne_one h

theorem mem_blockDiagSL_of_conjAut_proj_eq [CharP K 2] {I : Finset (Fin n)} (hI : I.Nonempty)
    (hIc : Iᶜ.Nonempty) (D : GL (Fin n) K) {l ν : K} (hlν : l ≠ ν)
    (hD : (D : Matrix (Fin n) (Fin n) K) = diagonal fun i => if i ∈ I then l else ν)
    {M : SpecialLinearGroup (Fin n) K} (hM : conjAut n K D (proj n K M) = proj n K M) :
    M ∈ blockDiagSL I := by
  set d : Fin n → K := fun i => if i ∈ I then l else ν with hd
  have hd0 := ne_zero_of_coe_eq_diagonal D hD
  have hl0 : l ≠ 0 := by
    obtain ⟨i, hi⟩ := hI
    have := hd0 i
    simpa [hd, hi] using this
  have hν0 : ν ≠ 0 := by
    obtain ⟨i, hi⟩ := hIc
    rw [Finset.mem_compl] at hi
    have := hd0 i
    simpa [hd, hi] using this
  rw [conjAut_proj, proj_eq_proj_iff] at hM
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hM
  set X := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K D M with hX
  have hMX : (M : Matrix (Fin n) (Fin n) K) = (c : K) • (X : Matrix (Fin n) (Fin n) K) := by
    have h : M = X * (X⁻¹ * M) := by group
    rw [h, Matrix.SpecialLinearGroup.coe_mul, hc, scalar_apply, ← smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one]
  have hMD : (M : Matrix (Fin n) (Fin n) K) * (D : Matrix (Fin n) (Fin n) K) =
      (c : K) • ((D : Matrix (Fin n) (Fin n) K) * M) := by
    conv_lhs => rw [hMX]
    rw [hX, coe_slConjugation, Matrix.smul_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hentry : ∀ i j, (M : Matrix (Fin n) (Fin n) K) i j * (d j - c * d i) = 0 := by
    intro i j
    have h := congrFun (congrFun hMD i) j
    rw [hD, mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul] at h
    linear_combination h
  have hdet : (M : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact one_ne_zero
  have hc1 : (c : K) = 1 := by
    by_contra hc1
    have h1c : (1 : K) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
    by_cases hνc : ν = c * l
    · obtain ⟨i, hi⟩ := hIc
      rw [Finset.mem_compl] at hi
      refine hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_)
      refine (mul_eq_zero.1 (hentry i j)).resolve_right ?_
      by_cases hj : j ∈ I
      · simp only [hd, hi, hj, ite_true, ite_false]
        rw [hνc]
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        have e : l - c * (c * l) = l * (1 - c) ^ 2 := by
          linear_combination (l * c - l * c ^ 2) * h2
        rw [e]
        exact mul_ne_zero hl0 (pow_ne_zero 2 h1c)
      · simp only [hd, hi, hj, ite_false]
        rw [show ν - c * ν = ν * (1 - c) by ring]
        exact mul_ne_zero hν0 h1c
    · obtain ⟨i, hi⟩ := hI
      refine hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_)
      refine (mul_eq_zero.1 (hentry i j)).resolve_right ?_
      by_cases hj : j ∈ I
      · simp only [hd, hi, hj, ite_true]
        rw [show l - c * l = l * (1 - c) by ring]
        exact mul_ne_zero hl0 h1c
      · simp only [hd, hi, hj, ite_true, ite_false]
        exact sub_ne_zero.2 hνc
  rw [mem_blockDiagSL]
  intro i j hij
  have h := hentry i j
  rw [hc1, one_mul] at h
  refine (mul_eq_zero.1 h).resolve_right ?_
  by_cases hi : i ∈ I
  · have hj : j ∉ I := hij.1 hi
    simp only [hd, hi, hj, ite_true, ite_false]
    exact sub_ne_zero.2 (Ne.symm hlν)
  · have hj : j ∈ I := by
      by_contra hj
      exact hi (hij.2 hj)
    simp only [hd, hi, hj, ite_true, ite_false]
    exact sub_ne_zero.2 hlν

theorem conjAut_proj_eq_of_mem_blockDiagSL {I : Finset (Fin n)} (D : GL (Fin n) K) {l ν : K}
    (hD : (D : Matrix (Fin n) (Fin n) K) = diagonal fun i => if i ∈ I then l else ν)
    {M : SpecialLinearGroup (Fin n) K} (hM : M ∈ blockDiagSL I) :
    conjAut n K D (proj n K M) = proj n K M := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have hcomm : (D : Matrix (Fin n) (Fin n) K) * M = M * D := by
    ext i j
    rw [hD, diagonal_mul, mul_diagonal]
    by_cases hi : i ∈ I <;> by_cases hj : j ∈ I
    · simp [hi, hj, mul_comm]
    · rw [mem_blockDiagSL.1 hM i j ⟨fun _ => hj, fun _ => hi⟩]
      simp
    · rw [mem_blockDiagSL.1 hM i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩]
      simp
    · simp [hi, hj, mul_comm]
  rw [hcomm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem fixAut_conjAut_eq_map_blockDiagSL [CharP K 2] {I : Finset (Fin n)} (hI : I.Nonempty)
    (hIc : Iᶜ.Nonempty) (D : GL (Fin n) K) {l ν : K} (hlν : l ≠ ν)
    (hD : (D : Matrix (Fin n) (Fin n) K) = diagonal fun i => if i ∈ I then l else ν) :
    fixAut (conjAut n K D) = (blockDiagSL (K := K) I).map (proj n K) := by
  ext x
  obtain ⟨M, rfl⟩ := proj_surjective n K x
  rw [mem_fixAut]
  constructor
  · intro h
    exact ⟨M, mem_blockDiagSL_of_conjAut_proj_eq hI hIc D hlν hD h, rfl⟩
  · rintro ⟨M', hM', hM'M⟩
    rw [← hM'M]
    exact conjAut_proj_eq_of_mem_blockDiagSL D hD hM'

theorem commutator_blockSL_eq_of_two_le [Finite K] {I : Finset (Fin n)} (hI : 2 ≤ I.card)
    (hK : 4 ≤ Nat.card K) : ⁅blockSL (K := K) I, blockSL (K := K) I⁆ = blockSL (K := K) I := by
  rcases Nat.lt_or_ge I.card 3 with h | h
  · exact commutator_blockSL_eq_of_card_two (by omega) hK
  · exact commutator_blockSL_eq_of_three_le h

theorem commutator_sup_eq_of_perfect {H : Type*} [Group H] {A B : Subgroup H}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) ?_
  calc A ⊔ B = ⁅A, A⁆ ⊔ ⁅B, B⁆ := by rw [hA, hB]
    _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
        (Subgroup.commutator_mono le_sup_right le_sup_right)

theorem perfectCore_fixAut_conjAut_eq [Finite K] [CharP K 2] {I : Finset (Fin n)}
    (hI : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card) (hK : 4 ≤ Nat.card K) (D : GL (Fin n) K) {l ν : K}
    (hlν : l ≠ ν)
    (hD : (D : Matrix (Fin n) (Fin n) K) = diagonal fun i => if i ∈ I then l else ν) :
    perfectCore (fixAut (conjAut n K D)) = blockSL I ⊔ blockSL Iᶜ := by
  have hfix := fixAut_conjAut_eq_map_blockDiagSL (Finset.card_pos.1 (by omega))
    (Finset.card_pos.1 (by omega)) D hlν hD
  refine InvPlacement.perfectCore_eq_of_perfect_of_commutator_le ?_ ?_ ?_
  · rw [hfix, blockSL, blockSL, ← Subgroup.map_sup]
    exact Subgroup.map_mono (sup_le (blockSpecialLinear_le_blockDiagSL I)
      (blockSpecialLinear_compl_le_blockDiagSL I))
  · exact commutator_sup_eq_of_perfect (commutator_blockSL_eq_of_two_le hI hK)
      (commutator_blockSL_eq_of_two_le hIc hK)
  · rw [hfix, ← Subgroup.map_commutator, blockSL, blockSL, ← Subgroup.map_sup]
    exact Subgroup.map_mono (commutator_blockDiagSL_le I)

end Fix

end CFSG.SeitzReduction.LinearPilot
