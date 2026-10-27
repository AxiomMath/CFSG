module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row49

public section

noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X2

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K ζ9 ζ9_pow_nine)
open CFSG.RankThree.PartTwo.KFacts.KS21.DFT (powVec powVec_apply rot3)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48 (w4 tau4 P₀ c4 coe_tau4 w4_mem_P₀ tau4_mem_P₀)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.Row49 (tau3 tau3_apply tau3_mem_R₃ R₃_le_fixSub w4_mul_tau3 fieldSU4_w4 tau4_const_central)
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (fieldSU4 coe_fieldSU4)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48 (fixSub mem_fixSub)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (σ4)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.Row49 (R₃ tau3 w4_mul_tau3)

@[expose] def sw : Equiv.Perm (Fin 4) := Equiv.swap 0 1

theorem neg_one_K : (-1 : K) = 1 := by
  rw [CharTwo.neg_eq]

theorem swGL_mem : (TauCeti.permutationGL (k := K) sw : GL (Fin 4) K) ∈ SUid σ4 4 := by
  rw [mem_SUid]
  constructor
  · rw [TauCeti.permutationGL_coe, Matrix.det_permutation]
    have : Equiv.Perm.sign sw⁻¹ = -1 := by decide
    rw [this]
    simp [neg_one_K]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, TauCeti.permutationGL_coe,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, sw, Equiv.Perm.inv_def, Equiv.swap_apply_def] <;>
      decide

@[expose] def swSU : SU4 := ⟨TauCeti.permutationGL (k := K) sw, swGL_mem⟩

theorem fieldSU4_swSU (φ : K ≃+* K) : fieldSU4 φ swSU = swSU := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_fieldSU4, coe_glAut]
  change ((TauCeti.permutationGL (k := K) sw : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ =
    ((TauCeti.permutationGL (k := K) sw : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  ext i j
  simp [TauCeti.permutationGL_coe, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, apply_ite φ,
    sw, Equiv.swap_apply_def]

theorem comm_w4_swSU : w4 * swSU * w4⁻¹ * swSU⁻¹ = w4 ∨ w4 * swSU * w4⁻¹ * swSU⁻¹ = w4⁻¹ := by
  have key : c4 * sw * c4⁻¹ * sw⁻¹ = c4 ∨ c4 * sw * c4⁻¹ * sw⁻¹ = c4⁻¹ := by decide
  have hw : ∀ σ : Equiv.Perm (Fin 4), ((TauCeti.permutationGL (k := K) σ : GL (Fin 4) K)) =
      TauCeti.permutationGL (k := K) σ := fun _ => rfl
  rcases key with h | h
  · left
    apply Subtype.ext
    change TauCeti.permutationGL (k := K) c4 * TauCeti.permutationGL (k := K) sw *
      (TauCeti.permutationGL (k := K) c4)⁻¹ * (TauCeti.permutationGL (k := K) sw)⁻¹ =
      TauCeti.permutationGL (k := K) c4
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h]
  · right
    apply Subtype.ext
    change TauCeti.permutationGL (k := K) c4 * TauCeti.permutationGL (k := K) sw *
      (TauCeti.permutationGL (k := K) c4)⁻¹ * (TauCeti.permutationGL (k := K) sw)⁻¹ =
      (TauCeti.permutationGL (k := K) c4)⁻¹
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h]

theorem swap_perm_mul_diag (d : Fin 4 → K) (hd : d 0 = d 1) :
    (Equiv.Perm.permMatrix K sw⁻¹ : Matrix (Fin 4) (Fin 4) K) * diagonal d =
      diagonal d * Equiv.Perm.permMatrix K sw⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.diagonal_apply,
      sw, Equiv.swap_apply_def, hd, Fin.sum_univ_four] <;> simp [hd]

theorem tau4_const_entry01 (a : ZMod 9) :
    (fun k : Fin 4 => (torusSnoc 3 (powVec ζ9 ζ9_pow_nine (.ofAdd fun _ : Fin 3 => a)) k : K)) 0 =
      (fun k : Fin 4 => (torusSnoc 3 (powVec ζ9 ζ9_pow_nine (.ofAdd fun _ : Fin 3 => a)) k : K)) 1 := by
  have h0 := torusSnoc_castSucc 3 (powVec ζ9 ζ9_pow_nine (.ofAdd fun _ : Fin 3 => a)) 0
  have h1 := torusSnoc_castSucc 3 (powVec ζ9 ζ9_pow_nine (.ofAdd fun _ : Fin 3 => a)) 1
  change ((torusSnoc 3 _ (Fin.castSucc 0) : Kˣ) : K) = ((torusSnoc 3 _ (Fin.castSucc 1) : Kˣ) : K)
  rw [h0, h1, powVec_apply, powVec_apply]

theorem swSU_mul_tau4_const (a : ZMod 9) :
    swSU * tau4 (.ofAdd fun _ => a) = tau4 (.ofAdd fun _ => a) * swSU := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  change ((TauCeti.permutationGL (k := K) sw : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((tau4 (.ofAdd fun _ => a) : SU4) : GL (Fin 4) K) =
    ((tau4 (.ofAdd fun _ => a) : SU4) : GL (Fin 4) K) *
      ((TauCeti.permutationGL (k := K) sw : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  rw [coe_tau4, TauCeti.permutationGL_coe]
  exact swap_perm_mul_diag _ (tau4_const_entry01 a)

@[expose] def C0 (a : ZMod 9) (φ : K ≃+* K) : Subgroup SU4 :=
  Subgroup.centralizer ({tau4 (.ofAdd fun _ => a)} : Set SU4) ⊓
    CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub (fieldSU4 φ)

theorem mem_C0 {a : ZMod 9} {φ : K ≃+* K} {g : SU4} :
    g ∈ C0 a φ ↔ g * tau4 (.ofAdd fun _ => a) = tau4 (.ofAdd fun _ => a) * g ∧
      fieldSU4 φ g = g := by
  unfold C0
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mem_fixSub]

theorem w4_mem_C0 (a : ZMod 9) (φ : K ≃+* K) : w4 ∈ C0 a φ :=
  mem_C0.2 ⟨tau4_const_central a w4 w4_mem_P₀, Row49.fieldSU4_w4 φ⟩

theorem swSU_mem_C0 (a : ZMod 9) (φ : K ≃+* K) : swSU ∈ C0 a φ :=
  mem_C0.2 ⟨swSU_mul_tau4_const a, fieldSU4_swSU φ⟩

theorem tau3_mem_C0 (a : ZMod 9) {φ : K ≃+* K} (hφ3 : φ ^ 3 = 1) (u : Fin 3 → ZMod 3) :
    tau3 (.ofAdd u) ∈ C0 a φ := by
  refine mem_C0.2 ⟨?_, ?_⟩
  · have hP : tau3 (.ofAdd u) ∈ P₀ := by
      rw [tau3_apply]
      exact tau4_mem_P₀ _
    exact tau4_const_central a _ hP
  · exact (mem_fixSub).2 (Row49.R₃_le_fixSub hφ3 (Row49.tau3_mem_R₃ u))

theorem comm_w4_tau3 (u : Fin 3 → ZMod 3) :
    w4 * tau3 (.ofAdd u) * w4⁻¹ * (tau3 (.ofAdd u))⁻¹ = tau3 (.ofAdd (rot3 u - u)) := by
  have h := Row49.w4_mul_tau3 u
  have h2 : w4 * tau3 (.ofAdd u) * w4⁻¹ = tau3 (.ofAdd (rot3 u)) := by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add, sub_eq_add_neg]

theorem w4_mem_derived (a : ZMod 9) (φ : K ≃+* K) : w4 ∈ ⁅C0 a φ, C0 a φ⁆ := by
  have hc : ⁅w4, swSU⁆ ∈ ⁅C0 a φ, C0 a φ⁆ :=
    Subgroup.commutator_mem_commutator (w4_mem_C0 a φ) (swSU_mem_C0 a φ)
  rw [commutatorElement_def] at hc
  rcases comm_w4_swSU with h | h
  · rw [h] at hc
    exact hc
  · rw [h] at hc
    simpa using (⁅C0 a φ, C0 a φ⁆).inv_mem hc

theorem tau3_v0_mem_derived (a : ZMod 9) {φ : K ≃+* K} (hφ3 : φ ^ 3 = 1) :
    tau3 (.ofAdd ![1, 2, 0]) ∈ ⁅C0 a φ, C0 a φ⁆ := by
  have h := Subgroup.commutator_mem_commutator (w4_mem_C0 a φ) (tau3_mem_C0 a hφ3 ![2, 0, 0])
  rw [commutatorElement_def, comm_w4_tau3] at h
  have hv : rot3 (![2, 0, 0] : Fin 3 → ZMod 3) - ![2, 0, 0] = ![1, 2, 0] := by decide
  rwa [hv] at h

theorem w4_tau3_v0_noncomm : w4 * tau3 (.ofAdd ![1, 2, 0]) ≠ tau3 (.ofAdd ![1, 2, 0]) * w4 := by
  intro h
  rw [Row49.w4_mul_tau3] at h
  have h2 : tau3 (.ofAdd (rot3 (![1, 2, 0] : Fin 3 → ZMod 3))) = tau3 (.ofAdd ![1, 2, 0]) :=
    mul_right_cancel h
  have h3 := Row49.tau3_injective h2
  have h4 : rot3 (![1, 2, 0] : Fin 3 → ZMod 3) = ![1, 2, 0] := Multiplicative.ofAdd.injective h3
  revert h4
  decide

theorem exists_three_derived_noncomm (a : ZMod 9) {φ : K ≃+* K} (hφ3 : φ ^ 3 = 1) :
    ∃ E : Subgroup SU4, IsPGroup 3 E ∧ E ≤ ⁅C0 a φ, C0 a φ⁆ ∧
      ∃ g ∈ E, ∃ g' ∈ E, g * g' ≠ g' * g := by
  have hR : IsPGroup 3 (Row49.R₃ : Subgroup SU4) :=
    IsPGroup.of_card (n := 4) (by rw [Row49.card_R₃]; norm_num)
  refine ⟨Row49.R₃ ⊓ ⁅C0 a φ, C0 a φ⁆, hR.to_le inf_le_left, inf_le_right, w4,
    ⟨Row49.w4_mem_R₃, w4_mem_derived a φ⟩, tau3 (.ofAdd ![1, 2, 0]),
    ⟨Row49.tau3_mem_R₃ _, tau3_v0_mem_derived a hφ3⟩, w4_tau3_v0_noncomm⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X2

end

end
