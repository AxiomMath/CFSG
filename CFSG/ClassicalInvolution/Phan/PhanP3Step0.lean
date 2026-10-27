module

public import CFSG.ClassicalInvolution.Phan.PhanP2Inv
public import CFSG.ClassicalInvolution.Phan.PhanG9Fib

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.MF15
open scoped MatrixGroups Pointwise

section Matrix

variable {F : Type} [Field F]

@[expose] def FJ (ε : F) (M : Matrix (Fin 2) (Fin 2) F) : Prop :=
  M 1 1 = M 0 0 ∧ M 1 0 = -ε * M 0 1

theorem FJ.comm {ε : F} {M N : Matrix (Fin 2) (Fin 2) F} (hM : FJ ε M) (hN : FJ ε N) :
    M * N = N * M := by
  obtain ⟨hM1, hM2⟩ := hM
  obtain ⟨hN1, hN2⟩ := hN
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hM1, hM2, hN1, hN2] <;>
    ring

theorem incl_frame0 (M : Matrix (Fin 2) (Fin 2) F) :
    (frame0 (F := F)).incl M = vecXY ![M 0 0, -M 0 1, 0, 0] ![M 1 1, M 1 0, 0, 0] := by
  ext s
  rcases s with i | i <;> fin_cases i <;>
    simp [Frame.incl_apply, frame0, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂]

theorem incl_one_mem_planeA (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    (frame0 (F := F)).incl 1 ∈ planeA ε hε h4 := by
  have hx : (frame0 (F := F)).incl 1 = vecXY ![1, 0, 0, 0] ![1, 0, 0, 0] := by
    rw [incl_frame0]
    congr 1
    ext i
    fin_cases i <;> simp
  refine ⟨?_, ?_, ?_⟩
  · show (frame0 (F := F)).La (-1) _ = _
    rw [hx, La_neg_one_frame0]
    ext s
    rcases s with i | i <;> fin_cases i <;> simp
  · show (frame1 ε hε h4).La (-1) _ = _
    rw [hx, La_neg_one_frame1]
    ext s
    rcases s with i | i <;> fin_cases i <;> simp
  · show (frame2 (F := F)).La (-1) _ = _
    rw [hx, La_neg_one_frame2]
    ext s
    rcases s with i | i <;> fin_cases i <;> simp

theorem FJ_of_La_stab {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0} {M : SL(2, F)}
    (hM : (frame0 (F := F)).La M ((frame0 (F := F)).incl 1) ∈ planeA ε hε h4) :
    FJ ε (M : Matrix (Fin 2) (Fin 2) F) := by
  rw [Frame.La_apply_incl, Matrix.mul_one, incl_frame0] at hM
  obtain ⟨-, h1, -⟩ := hM
  change (frame1 ε hε h4).La (-1) _ = _ at h1
  rw [La_neg_one_frame1] at h1
  have e0 := congrFun h1 (Sum.inl 0)
  have e1 := congrFun h1 (Sum.inl 1)
  simp only [vecXY_inl, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
    Matrix.cons_val] at e0 e1
  refine ⟨e0, ?_⟩
  have : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = ε * ((M : Matrix (Fin 2) (Fin 2) F) 1 0 / ε) := by
    field_simp
  rw [this, e1]
  ring

end Matrix

section Core

variable {F K : Type} [Field F] [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem exists_mul_of_mem_parab_zero (hK : Nat.card K = (p ^ f) ^ 2) {x : spinGroup (quadPlus 4 F)}
    (hx : x ∈ parab S {0}) : ∃ t ∈ torusSub S, ∃ ρ ∈ (S.ι 0).range, x = t * ρ := by
  rw [parab, Lsup_singleton] at hx
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (torusSub S) (S.ι 0).range
    (torusSub_le_normalizer_range hK 0)
  have hx' : x ∈ (↑(torusSub S) : Set (spinGroup (quadPlus 4 F))) *
      (↑(S.ι 0).range : Set (spinGroup (quadPlus 4 F))) := by
    rw [← h]
    exact hx
  obtain ⟨t, ht, ρ, hρ, rfl⟩ := hx'
  exact ⟨t, ht, ρ, hρ, rfl⟩

theorem exists_FJ_of_mem_stab (hS : ModelSpec S ε hε h4) {ρ : spinGroup (quadPlus 4 F)}
    (hρ : ρ ∈ (S.ι 0).range)
    (hst : ρ ∈ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4)) :
    ∃ M : SL(2, F), (stdFrames ε hε h4 0).La M = spinAction (quadPlus 4 F) ρ ∧
      FJ ε (M : Matrix (Fin 2) (Fin 2) F) := by
  have hmem : spinAction (quadPlus 4 F) ρ ∈ (stdFrames ε hε h4 0).La.range := by
    rw [← hS.map_range 0]
    exact ⟨ρ, hρ, rfl⟩
  obtain ⟨M, hM⟩ := hmem
  refine ⟨M, hM, FJ_of_La_stab (hε := hε) (h4 := h4) ?_⟩
  have := (hst _).2 (incl_one_mem_planeA ε hε h4)
  rw [← hM] at this
  exact this

theorem mem_range_tor_zero_of_stab (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    {ρ : spinGroup (quadPlus 4 F)} (hρ : ρ ∈ (S.ι 0).range)
    (hstab : ρ ∈ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4)) :
    ρ ∈ (tor S 0).range := by
  obtain ⟨M, hM, hFJ⟩ := exists_FJ_of_mem_stab hS hρ hstab
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK (by omega : 3 ≤ p ^ f)
  have ht₀ : tor S 0 x₀ ∈ torusSub S := tor_mem_torusSub S 0 x₀
  have ht₀R : tor S 0 x₀ ∈ (S.ι 0).range := ⟨_, rfl⟩
  have hst₀ : tor S 0 x₀ ∈ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4) :=
    torusSub_le_stabOf_eigSpace hK hg hS h2 h2K (-1) 1 1 ht₀
  obtain ⟨M₀, hM₀, hFJ₀⟩ := exists_FJ_of_mem_stab hS ht₀R hst₀
  have hcomm : ρ * tor S 0 x₀ = tor S 0 x₀ * ρ := by
    have hmem : ρ * tor S 0 x₀ * (tor S 0 x₀ * ρ)⁻¹ ∈ (S.ι 0).range :=
      mul_mem (mul_mem hρ ht₀R) (inv_mem (mul_mem ht₀R hρ))
    have h1 := hS.inj 0 _ hmem (by
      rw [map_mul, map_mul, map_inv, map_mul, ← hM, ← hM₀, ← map_mul, ← map_mul, ← map_inv,
        ← map_mul]
      have : M * M₀ = M₀ * M := Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        exact FJ.comm hFJ hFJ₀)
      rw [this, mul_inv_cancel, map_one])
    exact mul_inv_eq_one.1 h1
  obtain ⟨a, rfl⟩ := hρ
  have hab : a * torusTwo (unitaryInvolution K p f) x₀ =
      torusTwo (unitaryInvolution K p f) x₀ * a :=
    hg.inj 0 (by
      rw [map_mul, map_mul]
      exact hcomm)
  obtain ⟨y, rfl⟩ := mem_range_torusTwo_of_commute hx₀ hab
  exact ⟨y, rfl⟩

theorem mem_torusSub_of_mem_range_zero (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    {ρ : spinGroup (quadPlus 4 F)} (hρ : ρ ∈ (S.ι 0).range)
    (hstab : ρ ∈ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4)) : ρ ∈ torusSub S := by
  obtain ⟨y, rfl⟩ := mem_range_tor_zero_of_stab hK hg hS hq h2 h2K hρ hstab
  exact tor_mem_torusSub S 0 y

theorem parab_zero_inf_parab_le_torusSub (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0) :
    parab S {0} ⊓ parab S {1, 2, 3} ≤ torusSub S := by
  rintro x ⟨hx0, hx123⟩
  obtain ⟨t, ht, ρ, hρ, rfl⟩ := exists_mul_of_mem_parab_zero hK hx0
  have hstab : ρ ∈ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4) := by
    have h1 := parab_le_stabOf_planeA hK hg hS h2 h2K hx123
    have h2' := torusSub_le_stabOf_eigSpace hK hg hS h2 h2K (-1) 1 1 ht
    have := mul_mem (inv_mem h2') h1
    rw [inv_mul_cancel_left] at this
    exact this
  exact mul_mem ht (mem_torusSub_of_mem_range_zero hK hg hS hq h2 h2K hρ hstab)

theorem ptStep0_of_model (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0) :
    CFSG.ClassicalInvolution.PhanG.PtStep0 S := by
  intro e g hadj hpt
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective e
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
  rw [phanSystem_adj_mk] at hadj
  rw [CFSG.ClassicalInvolution.PhanG.ptMap_eq_iff,
    CFSG.ClassicalInvolution.PhanG.mem_residue_mk_iff] at hpt
  exact QuotientGroup.eq.2 (parab_zero_inf_parab_le_torusSub hK hg hS hq h2 h2K ⟨hadj, hpt⟩)

end Core

end CFSG.ClassicalInvolution.PhanP
