module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFLevi
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerCentralKernel

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SpL

open Matrix CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial (SymplecticTorusWeyl.mem_statedSp_iff)
open scoped MatrixGroups

section Block

variable {F : Type} [Field F] {n : ℕ}

theorem a₀_formJ : (Levi.a₀GL F n : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * formJ n F *
    (Levi.a₀GL F n : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      ((-1 : Fˣ) : F) • formJ n F := by
  show (diagonal (Levi.dsign F n))ᵀ * fromBlocks 0 1 (-1) 0 * diagonal (Levi.dsign F n) = _
  rw [diagonal_transpose, Levi.diagonal_dsign, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, formJ, fromBlocks_neg]
  simp

theorem a₀_mem_gsp : Levi.a₀GL F n ∈ gsp n F := ⟨-1, a₀_formJ⟩

theorem blockGL_mem_statedSp (B : GL (Fin n) F) : Levi.blockGL B ∈ StatedSp n F := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff, Levi.blockGL_val, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply]
  have h1 : (B : Matrix (Fin n) (Fin n) F)ᵀ * ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ =
      1 := by rw [← transpose_mul, Units.inv_mul, transpose_one]
  have h2 : ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) =
      1 := Units.inv_mul B
  simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, transpose_transpose, neg_zero]
  rw [h1, h2]

theorem exists_blockGL_of_comm_sp (h2 : (2 : F) ≠ 0) {g : GL (Fin n ⊕ Fin n) F}
    (hg : g ∈ StatedSp n F) (hc : g * Levi.a₀GL F n = Levi.a₀GL F n * g) :
    ∃ B : GL (Fin n) F, g = Levi.blockGL B := by
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    with hM
  have hMD : M * diagonal (Levi.dsign F n) = diagonal (Levi.dsign F n) * M :=
    congrArg (fun x : GL (Fin n ⊕ Fin n) F => (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) hc
  rw [← fromBlocks_toBlocks M, Levi.diagonal_dsign, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at hMD
  obtain ⟨-, h12, h21, -⟩ := hMD
  have h12' : M.toBlocks₁₂ = 0 := by
    apply Q3MFOD.eq_zero_of_eq_neg_matrix h2
    simpa using h12.symm
  have h21' : M.toBlocks₂₁ = 0 := by
    apply Q3MFOD.eq_zero_of_eq_neg_matrix h2
    simpa using h21
  have hMeq : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks M, h12', h21']
  have hsp := SymplecticTorusWeyl.mem_statedSp_iff.mp hg
  rw [← hM, hMeq, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at hsp
  obtain ⟨-, hMM, -, -⟩ := hsp
  simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_one] at hMM
  have hB2 : M.toBlocks₂₂ᵀ * M.toBlocks₁₁ = 1 := by
    have := congrArg transpose hMM
    simpa [transpose_mul] using this
  have hB1 : M.toBlocks₁₁ * M.toBlocks₂₂ᵀ = 1 := mul_eq_one_comm.mpr hB2
  refine ⟨⟨M.toBlocks₁₁, M.toBlocks₂₂ᵀ, hB1, hB2⟩, Units.ext ?_⟩
  rw [Levi.blockGL_val]
  change M = _
  conv_lhs => rw [hMeq]
  simp

theorem mem_fixedSubgroup_conjSp (A : gsp n F) (b : StatedSp n F) :
    b ∈ fixedSubgroup (conjSp n F A) ↔
      (b : GL (Fin n ⊕ Fin n) F) * (A : GL (Fin n ⊕ Fin n) F) =
        (A : GL (Fin n ⊕ Fin n) F) * b := by
  rw [Q3NM.mem_fixedSubgroup_iff]
  constructor
  · intro h
    have h' : (A : GL (Fin n ⊕ Fin n) F) * b * (A : GL (Fin n ⊕ Fin n) F)⁻¹ = b :=
      congrArg Subtype.val h
    calc (b : GL (Fin n ⊕ Fin n) F) * (A : GL (Fin n ⊕ Fin n) F)
        = ((A : GL (Fin n ⊕ Fin n) F) * b * (A : GL (Fin n ⊕ Fin n) F)⁻¹) * A := by rw [h']
      _ = A * b := by group
  · intro h
    refine Subtype.ext ?_
    show (A : GL (Fin n ⊕ Fin n) F) * b * (A : GL (Fin n ⊕ Fin n) F)⁻¹ = b
    rw [← h]
    group

variable (F n) in
@[expose] noncomputable def embSp : SL(n, F) →* StatedSp n F :=
  (Levi.blockHom.comp Matrix.SpecialLinearGroup.toGL).codRestrict (StatedSp n F)
    fun _ => blockGL_mem_statedSp _

theorem coe_embSp (A : SL(n, F)) :
    ((embSp F n A : StatedSp n F) : GL (Fin n ⊕ Fin n) F) =
      Levi.blockGL (Matrix.SpecialLinearGroup.toGL A) := rfl

theorem embSp_injective : Function.Injective (embSp F n) := by
  intro A B h
  have h1 := Levi.blockGL_injective (congrArg Subtype.val h)
  apply Subtype.ext
  exact congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h1

end Block

section Main

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem mul_self_eq_one_of_mem_center (hF : Nat.card F = 3) {z : StatedSp n F}
    (hz : z ∈ Subgroup.center (StatedSp n F)) : z * z = 1 := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hcc : (c : F) * c = 1 := by
    rcases Q3MFOD.cases_of_card_three hF (c : F) with h | h | h
    · exact absurd h c.ne_zero
    · rw [h, one_mul]
    · rw [h]; ring
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Units.val_mul, ← hc]
  simp [Matrix.GeneralLinearGroup.scalar, ← Matrix.smul_one_eq_diagonal, smul_smul, hcc]

theorem isPGroup_center_statedSp (hF : Nat.card F = 3) :
    IsPGroup 2 (Subgroup.center (StatedSp n F)) := by
  intro z
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, _root_.sq]
  exact mul_self_eq_one_of_mem_center hF z.2

theorem oddCoreIn_fixed_conjSp_a₀ (hF : Nat.card F = 3) (hn : 1 ≤ n) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (StatedSp n F)
      (conjSp n F ⟨Levi.a₀GL F n, a₀_mem_gsp⟩))) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hZ2 := isPGroup_center_statedSp (n := n) hF
  set A₀ : gsp n F := ⟨Levi.a₀GL F n, a₀_mem_gsp⟩ with hA₀
  have hker : ((QuotientGroup.mk' (Subgroup.center (StatedSp n F))).comp (embSp F n)).ker ≤
      Subgroup.center SL(n, F) := by
    intro A hA
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hA
    rw [Subgroup.mem_center_iff]
    intro B
    apply embSp_injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hA (embSp F n B)
  have hC : IsPGroup 2 ((QuotientGroup.mk' (Subgroup.center (StatedSp n F))).comp
      (embSp F n)).ker := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have hx := x.2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h1 := mul_self_eq_one_of_mem_center hF hx
    rw [← map_mul] at h1
    have h3 : (x : SL(n, F)) * x = 1 := embSp_injective (by rw [h1, map_one])
    rw [pow_one, _root_.sq, Subgroup.coe_mul, h3]
    rfl
  have hno : oddCoreIn ((embSp F n).range.map
      (QuotientGroup.mk' (Subgroup.center (StatedSp n F)))) = ⊥ := by
    rw [← MonoidHom.range_comp]
    exact oddCoreIn_range_eq_bot_of_central_kernel _
      (componentOddCore_specialLinear_eq_bot hF n) hker hC
  refine oddCoreIn_fixed_eq_bot_of_blocks hZ2 _ (ι := Unit) (fun _ => (embSp F n).range) ?_ ?_
    (fun _ => hno) ?_
  · intro _ x hx
    obtain ⟨A, rfl⟩ := hx
    rw [mem_fixedSubgroup_conjSp, coe_embSp]
    exact Levi.blockGL_mul_a₀GL _
  · intro _ b hb x hx
    obtain ⟨A, rfl⟩ := hx
    have hbc := (mem_fixedSubgroup_conjSp A₀ b).mp hb
    obtain ⟨B, hB⟩ := exists_blockGL_of_comm_sp h2 b.2 hbc
    refine ⟨Levi.conjSL B A, Subtype.ext ?_⟩
    rw [coe_embSp, Levi.toGL_conjSL, Levi.blockGL_mul, Levi.blockGL_mul, Levi.blockGL_inv]
    show _ = (b : GL (Fin n ⊕ Fin n) F) * Levi.blockGL (Matrix.SpecialLinearGroup.toGL A) *
      (b : GL (Fin n ⊕ Fin n) F)⁻¹
    rw [hB]
  · intro ν hν hcomm
    have hνc := (mem_fixedSubgroup_conjSp A₀ ν).mp hν
    obtain ⟨B, hB⟩ := exists_blockGL_of_comm_sp h2 ν.2 hνc
    have hBA : ∀ A : SL(n, F), B * Matrix.SpecialLinearGroup.toGL A =
        Matrix.SpecialLinearGroup.toGL A * B := by
      intro A
      have h1 := congrArg Subtype.val (hcomm () (embSp F n A) ⟨A, rfl⟩)
      have h1' : (ν : GL (Fin n ⊕ Fin n) F) * Levi.blockGL (Matrix.SpecialLinearGroup.toGL A) =
          Levi.blockGL (Matrix.SpecialLinearGroup.toGL A) * (ν : GL (Fin n ⊕ Fin n) F) := h1
      rw [hB, ← Levi.blockGL_mul, ← Levi.blockGL_mul] at h1'
      exact Levi.blockGL_injective h1'
    obtain ⟨c, hc⟩ := Levi.scalar_of_commute_toGL hBA
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 := Units.mul_inv B
      rw [hc, h0, map_zero, Matrix.zero_mul] at h1
      have := congr_fun (congr_fun h1 ⟨0, hn⟩) ⟨0, hn⟩
      simp at this
    have hcc : c * c = 1 := by
      rcases Q3MFOD.cases_of_card_three hF c with h | h | h
      · exact absurd h hc0
      · rw [h, one_mul]
      · rw [h]; ring
    have hBB : B * B = 1 := by
      apply Units.ext
      rw [Units.val_mul, hc, ← map_mul, hcc, map_one]
      rfl
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, _root_.sq, Subgroup.coe_mul, hB, ← Levi.blockGL_mul, hBB, Levi.blockGL_one]
    rfl

end Main

end CFSG.ClassicalInvolution.Q3.TL4.SpL
