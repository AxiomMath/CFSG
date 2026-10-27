module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLCore2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLCore

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddSp

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup CFSG.ComponentClassification.CatFactsSp4
open CFSG.ComponentClassification.CatLeafProof.EndOddCore CFSG.ComponentClassification.FooteLit

variable {K : Type} [Field K]

theorem kron_eq_fromBlocks (g h : Matrix (Fin 2) (Fin 2) K) :
    kron g h = fromBlocks (g 0 0 • h) (g 0 1 • h) (g 1 0 • h) (g 1 1 • h) := rfl

theorem kron_one_left (h : Matrix (Fin 2) (Fin 2) K) : kron 1 h = fromBlocks h 0 0 h := by
  simp [kron_eq_fromBlocks]

theorem eq_kron_one_of_commute {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h1 : M * kron !![1, 1; 0, 1] 1 = kron !![1, 1; 0, 1] 1 * M)
    (h2 : M * kron !![1, 0; 1, 1] 1 = kron !![1, 0; 1, 1] 1 * M) :
    M = kron 1 M.toBlocks₁₁ := by
  have e1 : kron (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) 1 = fromBlocks 1 1 0 1 := by
    simp [kron_eq_fromBlocks]
  have e2 : kron (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) 1 = fromBlocks 1 0 1 1 := by
    simp [kron_eq_fromBlocks]
  rw [e1] at h1
  rw [e2] at h2
  rw [kron_one_left]
  rw [← fromBlocks_toBlocks M] at h1 h2 ⊢
  simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.one_mul,
    Matrix.zero_mul, add_zero, zero_add, fromBlocks_inj] at h1 h2
  obtain ⟨a1, a2, -, -⟩ := h1
  obtain ⟨b1, -, -, -⟩ := h2
  simp only [toBlocks_fromBlocks₁₁]
  have hC : M.toBlocks₂₁ = 0 := by
    have := congrArg (· - M.toBlocks₁₁) a1
    simpa using this.symm
  have hB : M.toBlocks₁₂ = 0 := by
    have := congrArg (fun X => X - M.toBlocks₁₁) b1
    simpa using this
  have hD : M.toBlocks₂₂ = M.toBlocks₁₁ := by
    rw [hB] at a2
    simpa using a2.symm
  rw [hB, hC, hD]

theorem kron_one_injective {X Y : Matrix (Fin 2) (Fin 2) K} (h : kron 1 X = kron 1 Y) : X = Y := by
  rw [kron_one_left, kron_one_left] at h
  exact (fromBlocks_inj.mp h).1

theorem kron_one_neg_one : kron (1 : Matrix (Fin 2) (Fin 2) K) (-1) = -1 := by
  rw [kron_one_left, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem eq_J₁_or_neg (h2 : (2 : K) ≠ 0) {h : Matrix (Fin 2) (Fin 2) K} (hO : hᵀ * h = 1)
    (hsq : h * h = -1) : h = J₁ ∨ h = -J₁ := by
  have hT : hᵀ = -h := by
    calc hᵀ = hᵀ * (h * -h) := by rw [Matrix.mul_neg, hsq, neg_neg, Matrix.mul_one]
      _ = (hᵀ * h) * -h := by rw [Matrix.mul_assoc]
      _ = -h := by rw [hO, Matrix.one_mul]
  have t00 := congrFun (congrFun hT 0) 0
  have t11 := congrFun (congrFun hT 1) 1
  have t01 := congrFun (congrFun hT 0) 1
  simp only [transpose_apply, Matrix.neg_apply] at t00 t11 t01
  have h00 : h 0 0 = 0 := by
    have : (2 : K) * h 0 0 = 0 := by linear_combination t00
    exact (mul_eq_zero.mp this).resolve_left h2
  have h11 : h 1 1 = 0 := by
    have : (2 : K) * h 1 1 = 0 := by linear_combination t11
    exact (mul_eq_zero.mp this).resolve_left h2
  have s00 := congrFun (congrFun hsq 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, one_apply_eq] at s00
  rw [h00, t01] at s00
  have hb : (h 0 1 - 1) * (h 0 1 + 1) = 0 := by linear_combination -s00
  rcases mul_eq_zero.mp hb with hb | hb
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J₁, h00, h11, t01] <;> linear_combination hb
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J₁, h00, h11, t01] <;>
      first | linear_combination hb | linear_combination -hb

theorem exists_quat_of_isTwoComponentAt_u1 [Finite K] (hodd : Odd (Nat.card K))
    {Y : Subgroup (StatedProj (StatedSp 2 K))} (hY : IsTwoComponentAt (u1 K) Y) :
    ∃ H : Subgroup Y, Nonempty (H ≃* QuaternionGroup 2) := by
  have h2 := two_ne_zero_of_odd_card hodd
  have hK2 : ringChar K ≠ 2 := by
    intro h
    exact h2 (by rw [← Nat.cast_ofNat, ringChar.spec]; exact h ▸ dvd_rfl)
  obtain ⟨hE, -⟩ := pComponent_centralizer_u1 hodd hY.2.1 hY.2.2
  rcases hE with rfl | rfl
  · exact exists_quaternion_of_mulEquiv_SL hK2 (E1Equiv h2).symm
  · exact exists_quaternion_of_mulEquiv_SL hK2 (E2Equiv h2).symm

theorem exists_quat_of_conj_u1 [Finite K] (hodd : Odd (Nat.card K))
    {b g : StatedProj (StatedSp 2 K)} (hg : g⁻¹ * b * g = u1 K)
    {Y : Subgroup (StatedProj (StatedSp 2 K))} (hY : IsTwoComponentAt b Y) :
    ∃ H : Subgroup Y, Nonempty (H ≃* QuaternionGroup 2) := by
  set φ : StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 K) := MulAut.conj g⁻¹ with hφ
  have hφb : φ b = u1 K := by
    rw [hφ, MulAut.conj_apply, inv_inv]
    exact hg
  have h1 := isTwoComponentAt_map φ hY
  rw [hφb] at h1
  obtain ⟨H, ⟨e⟩⟩ := exists_quat_of_isTwoComponentAt_u1 hodd h1
  let eY : Y ≃* Y.map φ.toMonoidHom := Y.equivMapOfInjective φ.toMonoidHom φ.injective
  exact ⟨H.map eY.symm.toMonoidHom, ⟨(H.equivMapOfInjective _ eY.symm.injective).symm.trans e⟩⟩

theorem false_of_config_u1 [Finite K] (hodd : Odd (Nat.card K))
    {L D : Subgroup (StatedProj (StatedSp 2 K))} (h : Config (u1 K) L D) : False := by
  obtain ⟨H, ⟨e⟩⟩ := exists_quat_of_isTwoComponentAt_u1 hodd h.twoComp
  exact h.false_of_quat H e

theorem proj_eq_u2 {T : StatedSp 2 K}
    (hT : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron 1 J₁ ∨
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -kron 1 J₁) :
    proj 2 K T = u2 K := by
  have hs : (T2 K)⁻¹ * T ∈ spScalars 2 K := by
    rw [mem_spScalars_iff]
    have hinv : ((T2 K : StatedSp 2 K)⁻¹ * T2 K) = 1 := inv_mul_cancel _
    have hTT : ((T2 K : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((T2 K)⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) = 1 := by
      have := congrArg (fun y : StatedSp 2 K =>
        ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
        (mul_inv_cancel (T2 K))
      simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using this
    rcases hT with hT | hT
    · left
      have := congrArg (fun y : StatedSp 2 K =>
        ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hinv
      simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one,
        coe_T2] at this
      rw [Subgroup.coe_mul, Units.val_mul, hT]
      exact this
    · right
      have := congrArg (fun y : StatedSp 2 K =>
        ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hinv
      simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one,
        coe_T2] at this
      rw [Subgroup.coe_mul, Units.val_mul, hT, Matrix.mul_neg, this]
  have h1 : proj 2 K ((T2 K)⁻¹ * T) = 1 := by
    rw [← MonoidHom.mem_ker, ker_proj]
    exact hs
  rw [map_mul, map_inv] at h1
  rw [u2]
  calc proj 2 K T = proj 2 K (T2 K) * ((proj 2 K (T2 K))⁻¹ * proj 2 K T) := by group
    _ = proj 2 K (T2 K) := by rw [h1, mul_one]

theorem false_of_config_u2 [Finite K] (hodd : Odd (Nat.card K))
    {L D : Subgroup (StatedProj (StatedSp 2 K))} (h : Config (u2 K) L D) : False := by
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨hL, h5⟩ := pComponent_centralizer_u2 hodd h.twoComp.2.1 h.twoComp.2.2
  subst hL
  have h4 : 4 ≤ Nat.card K := by omega
  have hO := pPrimeCore_Lsub h4
  obtain ⟨b, hbD, hb2, hbu⟩ := h.exists_involution_ne
  have hbL : b ∈ centralizer (Lsub K : Set (StatedProj (StatedSp 2 K))) :=
    coreActionKernel_le_centralizer hO (mem_inf.mp (h.D_le hbD)).2
  obtain ⟨B, rfl⟩ := proj_surjective b
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) := (isQuasisimple_SL2' h4).1
  have : Group.IsPerfect (diagSL K).range := Group.IsPerfect.range (diagSL K)
  have hZ : spScalars 2 K ≤ center (StatedSp 2 K) := fun z hz => mem_center_of_mem_spScalars hz
  have hcomm := commute_of_commutator_mem hZ (Subgroup.commutator_eq_self (H := (diagSL K).range))
    (g := B) (by
      intro x hx
      rw [← ker_proj, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have hxL : proj 2 K x ∈ Lsub K := mem_map_of_mem _ hx
      rw [← mem_centralizer_iff.mp hbL _ hxL]
      group)
  set M := ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hMg : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      M * kron (g : Matrix (Fin 2) (Fin 2) K) 1 = kron (g : Matrix (Fin 2) (Fin 2) K) 1 * M := by
    intro g
    have := congrArg (fun y : StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
      (hcomm (diagSL K g) ⟨g, rfl⟩)
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_diagSL] using this
  have hMk : M = kron 1 M.toBlocks₁₁ :=
    eq_kron_one_of_commute (hMg ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩)
      (hMg ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩)
  set hh := M.toBlocks₁₁ with hhdef
  have hO2 : hhᵀ * hh = 1 := by
    have hs := symplectic_of_mem B
    rw [← hM, hMk, kron_symplectic_iff, det_one, one_smul] at hs
    exact hs
  have hB2 : B * B ∈ spScalars 2 K := by
    have h1 := pow_orderOf_eq_one (proj 2 K B)
    rw [hb2, pow_two, ← map_mul] at h1
    rw [← ker_proj, MonoidHom.mem_ker]
    exact h1
  rw [mem_spScalars_iff, Subgroup.coe_mul, Units.val_mul, ← hM, hMk, kron_mul,
    Matrix.one_mul] at hB2
  rcases hB2 with hsq | hsq
  ·
    have hsq' : hh * hh = 1 := kron_one_injective (by rw [hsq, kron_one_one])
    have hM1 : M ≠ 1 := by
      intro hM1
      have : proj 2 K B = 1 := by
        rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
        exact Or.inl hM1
      rw [this, orderOf_one] at hb2
      norm_num at hb2
    have hMm : M ≠ -1 := by
      intro hMm
      have : proj 2 K B = 1 := by
        rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
        exact Or.inr hMm
      rw [this, orderOf_one] at hb2
      norm_num at hb2
    have hMM : M * M = 1 := by rw [hMk, kron_mul, Matrix.one_mul, hsq', kron_one_one]
    obtain ⟨g, hg⟩ := exists_conj_T1 h2 B hMM hM1 hMm
    have hconj : (proj 2 K g)⁻¹ * proj 2 K B * proj 2 K g = u1 K := by
      rw [← map_inv, ← map_mul, ← map_mul, hg]
      rfl
    exact h.false_of_pump_quat hbD hb2 fun Y hY => exists_quat_of_conj_u1 hodd hconj hY
  ·
    have hsq' : hh * hh = -1 := kron_one_injective (by rw [hsq, kron_one_neg_one])
    apply hbu
    apply proj_eq_u2
    rcases eq_J₁_or_neg h2 hO2 hsq' with hJ | hJ
    · left
      rw [← hM, hMk, hJ]
    · right
      rw [← hM, hMk, hJ, kron_eq_fromBlocks, kron_eq_fromBlocks, fromBlocks_neg]
      simp

theorem false_of_config_psp4 [Finite K] (hodd : Odd (Nat.card K))
    {z : StatedProj (StatedSp 2 K)} {L D : Subgroup (StatedProj (StatedSp 2 K))}
    (h : Config z L D) : False := by
  obtain ⟨g, hg | hg⟩ := exists_conj_of_orderOf_eq_two hodd h.twoComp.1
  · have h1 := h.map (MulAut.conj g⁻¹)
    rw [MulAut.conj_apply, inv_inv, hg] at h1
    exact false_of_config_u1 hodd h1
  · have h1 := h.map (MulAut.conj g⁻¹)
    rw [MulAut.conj_apply, inv_inv, hg] at h1
    exact false_of_config_u2 hodd h1

end CFSG.ComponentClassification.CatLeafProof.EndOddSp
