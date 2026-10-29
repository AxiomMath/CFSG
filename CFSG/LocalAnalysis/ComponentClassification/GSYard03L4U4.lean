module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Defs
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverL4U4
import CFSG.GH74.Generic.S1.Exo.UniDescentAdj
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Cases
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill
import CFSG.GH74.GLS.TwoThin.G.Section
import CFSG.GH74.GLS.TwoThin.KGroupCore
import CFSG.GH74.Generic.S1.LinFull
import CFSG.GH74.KGroups.L28Tables
import CFSG.GH74.KGroups.L34Aut
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphCore
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphDescent
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUInnerPaired
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternal
import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassPoint
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm
import CFSG.Quasithin.Vol2.KGFactC31RuRef
import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
import CFSG.Walter.J1Recog
import Certificates.Certificate10025
import Certificates.Certificate5007
import Certificates.Certificate7233Base

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.Sol76.Sig.GSYard02 Matrix CFSG.Open CFSG.GH74.Generic.S1.Exo

theorem CentralSquareFour.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    CentralSquareFour Q → CentralSquareFour Q' := by
  intro h x' hx'
  have hx : e.symm x' * e.symm x' ∈ center Q := by
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro g
    apply e.injective
    have := hx' (e g)
    simpa [map_mul] using this
  obtain ⟨A, hA, hAx⟩ := h (e.symm x') hx
  refine ⟨A.map e.toMonoidHom, ?_, ?_⟩
  · refine isKleinFour_of_card_eq_four ?_ fun y hy => ?_
    · rw [Subgroup.card_map_of_injective e.injective, hA.card_four]
    · obtain ⟨v, hv, rfl⟩ := hy
      rw [← map_pow, sq_eq_one_of_isKleinFour hA hv, map_one]
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    rw [hh']
    have hax : e.symm x' * a = a * e.symm x' :=
      mem_centralizer_iff.1 (hAx ha) (e.symm x') (Set.mem_singleton _)
    have := congrArg e hax
    simpa [map_mul] using this

section Pair

private theorem pairU_sq_aux {R : Type*} [Ring R] {P : R} (hP : P * P = P) :
    (1 - P - P) * (1 - P - P) = 1 := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
  abel

private theorem pairU_sq_aux' {R : Type*} [Ring R] {p₀ p₁ : R} (h₀ : p₀ * p₀ = p₀)
    (h₁ : p₁ * p₁ = p₁) (h₀₁ : p₀ * p₁ = 0) (h₁₀ : p₁ * p₀ = 0) :
    (1 - (p₀ + p₁) - (p₀ + p₁)) * (1 - (p₀ + p₁) - (p₀ + p₁)) = 1 := by
  apply pairU_sq_aux
  simp only [add_mul, mul_add, h₀, h₁, h₀₁, h₁₀, add_zero, zero_add]

variable {F : Type} [Field F]

private def pairU (a₀ b₀ a₁ b₁ : Fin 4 → F) : Matrix (Fin 4) (Fin 4) F :=
  1 - (vecMulVec a₀ b₀ + vecMulVec a₁ b₁) - (vecMulVec a₀ b₀ + vecMulVec a₁ b₁)

private theorem vmv_mul (a b c d : Fin 4 → F) :
    vecMulVec a b * vecMulVec c d = (b ⬝ᵥ c) • vecMulVec a d := by
  rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]

private theorem pairU_mul_self {a₀ b₀ a₁ b₁ : Fin 4 → F} (h00 : b₀ ⬝ᵥ a₀ = 1)
    (h11 : b₁ ⬝ᵥ a₁ = 1) (h01 : b₀ ⬝ᵥ a₁ = 0) (h10 : b₁ ⬝ᵥ a₀ = 0) :
    pairU a₀ b₀ a₁ b₁ * pairU a₀ b₀ a₁ b₁ = 1 := by
  unfold pairU
  apply pairU_sq_aux'
  · rw [vmv_mul, h00, one_smul]
  · rw [vmv_mul, h11, one_smul]
  · rw [vmv_mul, h01, zero_smul]
  · rw [vmv_mul, h10, zero_smul]

private theorem det_one_sub_two_vmv (a b : Fin 4 → F) :
    (1 - vecMulVec a b - vecMulVec a b : Matrix (Fin 4) (Fin 4) F).det = 1 - 2 * (b ⬝ᵥ a) := by
  have h : (1 - vecMulVec a b - vecMulVec a b : Matrix (Fin 4) (Fin 4) F) =
      1 + replicateCol Unit ((-2 : F) • a) * replicateRow Unit b := by
    rw [← vecMulVec_eq Unit]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct_smul, smul_eq_mul]
  ring

private theorem pairU_eq_mul {a₀ b₀ a₁ b₁ : Fin 4 → F} (h01 : b₀ ⬝ᵥ a₁ = 0) :
    pairU a₀ b₀ a₁ b₁ = (1 - vecMulVec a₀ b₀ - vecMulVec a₀ b₀) *
      (1 - vecMulVec a₁ b₁ - vecMulVec a₁ b₁) := by
  have e₀₁ : vecMulVec a₀ b₀ * vecMulVec a₁ b₁ = 0 := by rw [vmv_mul, h01, zero_smul]
  unfold pairU
  simp only [sub_mul, mul_sub, one_mul, mul_one, e₀₁]
  abel

private theorem pairU_det {a₀ b₀ a₁ b₁ : Fin 4 → F} (h00 : b₀ ⬝ᵥ a₀ = 1)
    (h11 : b₁ ⬝ᵥ a₁ = 1) (h01 : b₀ ⬝ᵥ a₁ = 0) :
    (pairU a₀ b₀ a₁ b₁).det = 1 := by
  rw [pairU_eq_mul h01, Matrix.det_mul, det_one_sub_two_vmv, det_one_sub_two_vmv, h00, h11]
  ring

private theorem pairU_trace {a₀ b₀ a₁ b₁ : Fin 4 → F} (h00 : b₀ ⬝ᵥ a₀ = 1)
    (h11 : b₁ ⬝ᵥ a₁ = 1) : (pairU a₀ b₀ a₁ b₁).trace = 0 := by
  have h4 : ((Fintype.card (Fin 4) : ℕ) : F) = 4 := by simp
  unfold pairU
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one,
    trace_vecMulVec, trace_vecMulVec, dotProduct_comm a₀ b₀, dotProduct_comm a₁ b₁, h00, h11, h4]
  ring

private theorem pairU_comm {a₀ b₀ a₁ b₁ : Fin 4 → F} {M : Matrix (Fin 4) (Fin 4) F}
    (hM : M * (vecMulVec a₀ b₀ + vecMulVec a₁ b₁) = (vecMulVec a₀ b₀ + vecMulVec a₁ b₁) * M) :
    pairU a₀ b₀ a₁ b₁ * M = M * pairU a₀ b₀ a₁ b₁ := by
  unfold pairU
  simp only [sub_mul, mul_sub, one_mul, mul_one, hM]

end Pair

section Finish

variable {F : Type} [Field F]

private theorem ne_four_of_ne_two (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  intro h
  apply h2
  have h' : (2 : F) * 2 = 0 := by linear_combination h
  exact (mul_self_eq_zero.1 h')

private theorem exists_klein_of_involution (h2 : (2 : F) ≠ 0) (H : Subgroup (GL (Fin 4) F))
    (hneg : (-1 : GL (Fin 4) F) ∈ H) (x : H) (U : Matrix (Fin 4) (Fin 4) F) (hUU : U * U = 1)
    (htr : U.trace = 0) (hUH : (⟨U, U, hUU, hUU⟩ : GL (Fin 4) F) ∈ H)
    (hUx : U * ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * U) :
    ∃ A : Subgroup H, IsKleinFour A ∧ A ≤ centralizer {x} := by
  have h4 := ne_four_of_ne_two h2
  let n : H := ⟨-1, hneg⟩
  let w : H := ⟨⟨U, U, hUU, hUU⟩, hUH⟩
  have hn : n * n = 1 := Subtype.ext (by simp [n])
  have hw : w * w = 1 := Subtype.ext (Units.ext hUU)
  have hnw : n * w = w * n := Subtype.ext (by simp [n, w])
  have hn1 : n ≠ 1 := by
    intro h
    have h' := congrArg (fun y : H => ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) h
    have h'' : (-1 : F) = 1 := by simpa [n] using h'
    exact h2 (by linear_combination -h'')
  have hw1 : w ≠ 1 := by
    intro h
    have hU1 : U = 1 := congrArg (fun y : H => ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h
    rw [hU1, Matrix.trace_one] at htr
    apply h4
    simpa using htr
  have hnw' : n ≠ w := by
    intro h
    have hU1 : U = -1 :=
      (congrArg (fun y : H => ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h).symm.trans
        (by simp [n])
    rw [hU1, Matrix.trace_neg, Matrix.trace_one] at htr
    apply h4
    have : -((Fintype.card (Fin 4) : ℕ) : F) = 0 := htr
    simpa using this
  refine ⟨l4uKlein hn hw hnw, l4uKlein_isKleinFour hn hw hnw hn1 hw1 hnw', ?_⟩
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  have hcx : x * n = n * x := Subtype.ext (by simp [n])
  have hcw : x * w = w * x := Subtype.ext (Units.ext (by
    show ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * U = U * ((x : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)
    exact hUx.symm))
  exact wp1_comm_klein hn hw hnw hcx hcw hg

end Finish

section SL4

variable {F : Type} [Field F]

private theorem exists_pair_of_not_scalar (M : Matrix (Fin 4) (Fin 4) F)
    (hns : ∀ d : F, M ≠ d • 1) :
    ∃ v β : Fin 4 → F, β ⬝ᵥ v = 0 ∧ β ⬝ᵥ (M *ᵥ v) = 1 := by
  classical
  have hex : ∃ v : Fin 4 → F, LinearIndependent F ![v, M *ᵥ v] := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
      (f := Matrix.toLin' M) (fun v => by rw [Matrix.toLin'_apply]; exact hcon v)
    have : Matrix.toLin' M = Matrix.toLin' (a • (1 : Matrix (Fin 4) (Fin 4) F)) := by
      rw [map_smul, Matrix.toLin'_one, ha]; rfl
    exact hns a (Matrix.toLin'.injective this)
  obtain ⟨v, hv⟩ := hex
  have hnot : M *ᵥ v ∉ Submodule.span F {v} := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    have := (LinearIndependent.pair_iff.1 hv) a (-1) (by rw [neg_smul, one_smul, ha]; abel)
    exact one_ne_zero (neg_eq_zero.1 this.2)
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hfv : f v = 0 := by
    have : f v ∈ (Submodule.span F {v}).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span rfl)
    rw [hf2] at this
    exact (Submodule.mem_bot F).1 this
  set w : Fin 4 → F := fun i => f (fun j => if i = j then 1 else 0) with hw
  have hfw : ∀ x : Fin 4 → F, f x = w ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ (f : (Fin 4 → F) →ₗ[F] F) x]
    simp only [dotProduct, smul_eq_mul, hw]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨v, (f (M *ᵥ v))⁻¹ • w, ?_, ?_⟩
  · rw [smul_dotProduct, ← hfw, hfv, smul_zero]
  · rw [smul_dotProduct, ← hfw, smul_eq_mul, inv_mul_cancel₀ hf1]

private theorem sl4_core (M : Matrix (Fin 4) (Fin 4) F) (c : F) (hc : M * M = c • 1)
    (hns : ∀ d : F, M ≠ d • 1) :
    ∃ U : Matrix (Fin 4) (Fin 4) F, U * U = 1 ∧ U.det = 1 ∧ U.trace = 0 ∧ U * M = M * U := by
  obtain ⟨v, β, hβv, hβMv⟩ := exists_pair_of_not_scalar M hns
  have h00 : (β ᵥ* M) ⬝ᵥ v = 1 := by rw [← Matrix.dotProduct_mulVec]; exact hβMv
  have h11 : β ⬝ᵥ (M *ᵥ v) = 1 := hβMv
  have h01 : (β ᵥ* M) ⬝ᵥ (M *ᵥ v) = 0 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hc, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, hβv, smul_zero]
  have h10 : β ⬝ᵥ v = 0 := hβv
  have hcomm : M * (vecMulVec v (β ᵥ* M) + vecMulVec (M *ᵥ v) β) =
      (vecMulVec v (β ᵥ* M) + vecMulVec (M *ᵥ v) β) * M := by
    rw [mul_add, add_mul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMulVec_mul, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, hc, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.vecMul_smul, Matrix.vecMul_one, smul_vecMulVec, vecMulVec_smul]
    abel
  exact ⟨pairU v (β ᵥ* M) (M *ᵥ v) β, pairU_mul_self h00 h11 h01 h10,
    pairU_det h00 h11 h01, pairU_trace h00 h11, pairU_comm hcomm⟩

private def diag4 : Matrix (Fin 4) (Fin 4) F := Matrix.diagonal ![1, 1, -1, -1]

private theorem diag4_sq : (diag4 : Matrix (Fin 4) (Fin 4) F) * diag4 = 1 := by
  unfold diag4
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem diag4_det : (diag4 : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  unfold diag4
  rw [Matrix.det_diagonal, Fin.prod_univ_four]
  simp

private theorem diag4_trace : (diag4 : Matrix (Fin 4) (Fin 4) F).trace = 0 := by
  unfold diag4
  rw [Matrix.trace_diagonal, Fin.sum_univ_four]
  simp

theorem centralSquareFour_statedSL4 {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    CentralSquareFour ↥(CFSG.Open.StatedSL 4 F) := by
  intro x hx
  have hx' : ((x * x : ↥(StatedSL 4 F)) : GL (Fin 4) F) ∈ StatedScalars (Fin 4) F := by
    rw [CFSG.GH74.L5U5.center_statedSL_eq 4, Subgroup.mem_subgroupOf] at hx
    exact hx
  rw [StatedScalars, MonoidHom.mem_range] at hx'
  obtain ⟨c, hc⟩ := hx'
  have hMM : ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (c : F) • 1 := by
    have := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Subgroup.coe_mul,
      Units.val_mul] at this
    rw [← this, Matrix.smul_one_eq_diagonal]
  have hneg : (-1 : GL (Fin 4) F) ∈ StatedSL 4 F :=
    CFSG.Open.StatedAPI.mem_statedSL_of_det (by simp [Matrix.det_neg] <;> norm_num)
  by_cases hs : ∃ d : F, ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = d • 1
  · obtain ⟨d, hd⟩ := hs
    refine exists_klein_of_involution h2 _ hneg x diag4 diag4_sq diag4_trace ?_ ?_
    · exact CFSG.Open.StatedAPI.mem_statedSL_of_det diag4_det
    · rw [hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  · push Not at hs
    obtain ⟨U, hUU, hdet, htr, hUM⟩ := sl4_core _ (c : F) hMM hs
    exact exists_klein_of_involution h2 _ hneg x U hUU htr
      (CFSG.Open.StatedAPI.mem_statedSL_of_det hdet) hUM

end SL4

section Unitary

variable {K : Type} [Field K]

private def bv (bar : K →+* K) (x : Fin 4 → K) : Fin 4 → K := fun i => bar (x i)

private def herm (bar : K →+* K) (x y : Fin 4 → K) : K := bv bar x ⬝ᵥ y

private theorem bv_add (bar : K →+* K) (x y : Fin 4 → K) :
    bv bar (x + y) = bv bar x + bv bar y := by
  funext i; simp [bv]

private theorem bv_smul (bar : K →+* K) (c : K) (x : Fin 4 → K) :
    bv bar (c • x) = bar c • bv bar x := by
  funext i; simp [bv]

private theorem bv_bv (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x) (x : Fin 4 → K) :
    bv bar (bv bar x) = x := by
  funext i; simp [bv, hbb]

private theorem herm_add_left (bar : K →+* K) (x x' y : Fin 4 → K) :
    herm bar (x + x') y = herm bar x y + herm bar x' y := by
  simp only [herm, bv_add, add_dotProduct]

private theorem herm_add_right (bar : K →+* K) (x y y' : Fin 4 → K) :
    herm bar x (y + y') = herm bar x y + herm bar x y' := by
  simp only [herm, dotProduct_add]

private theorem herm_sub_right (bar : K →+* K) (x y y' : Fin 4 → K) :
    herm bar x (y - y') = herm bar x y - herm bar x y' := by
  simp only [herm, dotProduct_sub]

private theorem herm_smul_left (bar : K →+* K) (c : K) (x y : Fin 4 → K) :
    herm bar (c • x) y = bar c * herm bar x y := by
  simp only [herm, bv_smul, smul_dotProduct, smul_eq_mul]

private theorem herm_smul_right (bar : K →+* K) (c : K) (x y : Fin 4 → K) :
    herm bar x (c • y) = c * herm bar x y := by
  simp only [herm, dotProduct_smul, smul_eq_mul]

private theorem herm_comm (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x) (x y : Fin 4 → K) :
    herm bar y x = bar (herm bar x y) := by
  simp only [herm, bv, dotProduct, map_sum, map_mul, hbb]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem bv_adj (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x)
    (M : Matrix (Fin 4) (Fin 4) K) (x : Fin 4 → K) :
    bv bar (uniDescAdj bar M *ᵥ x) = bv bar x ᵥ* M := by
  funext j
  simp only [bv, uniDescAdj, Matrix.vecMul, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hbb]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem herm_mulVec (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x)
    (M : Matrix (Fin 4) (Fin 4) K) (x y : Fin 4 → K) :
    herm bar x (M *ᵥ y) = herm bar (uniDescAdj bar M *ᵥ x) y := by
  simp only [herm, bv_adj bar hbb, Matrix.dotProduct_mulVec]

private theorem herm_unitary (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x)
    {M : Matrix (Fin 4) (Fin 4) K} (hM : uniDescAdj bar M * M = 1) (x y : Fin 4 → K) :
    herm bar (M *ᵥ x) (M *ᵥ y) = herm bar x y := by
  rw [herm_mulVec bar hbb M (M *ᵥ x) y, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]

private theorem herm_nondeg (bar : K →+* K) {x : Fin 4 → K} (hx : x ≠ 0) :
    ∃ y, herm bar x y ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  refine ⟨Pi.single i 1, ?_⟩
  simp only [herm, dotProduct_single, mul_one]
  exact (map_ne_zero bar).2 hi

private theorem herm_lin2 (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x) (u w : Fin 4 → K)
    (t t' : K) :
    herm bar (u + t • w) (u + t' • w) =
      herm bar u u + t' * herm bar u w + bar t * bar (herm bar u w) +
        bar t * (t' * herm bar w w) := by
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
    herm_comm bar hbb u w]
  ring

private theorem herm_eigen (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x)
    {M : Matrix (Fin 4) (Fin 4) K} (hM : uniDescAdj bar M * M = 1) {a a' : Fin 4 → K}
    {ν ν' : K} (ha : M *ᵥ a = ν • a) (ha' : M *ᵥ a' = ν' • a') :
    herm bar a a' = bar ν * (ν' * herm bar a a') := by
  have h := herm_unitary bar hbb hM a a'
  rw [ha, ha', herm_smul_left, herm_smul_right] at h
  exact h.symm

private theorem herm_orth (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x) (h2 : (2 : K) ≠ 0)
    {M : Matrix (Fin 4) (Fin 4) K} (hM : uniDescAdj bar M * M = 1) {ν : K}
    (hν : bar ν * ν = 1) {a b : Fin 4 → K} (ha : M *ᵥ a = ν • a) (hb : M *ᵥ b = (-ν) • b) :
    herm bar a b = 0 := by
  have h := herm_eigen bar hbb hM ha hb
  have h' : (2 : K) * herm bar a b = 0 := by
    linear_combination h - (herm bar a b) * hν
  exact (mul_eq_zero.1 h').resolve_left h2

private def rk1 (bar : K →+* K) (e : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  (herm bar e e)⁻¹ • vecMulVec e (bv bar e)

private theorem uniDescAdj_add' (bar : K →+* K) (A B : Matrix (Fin 4) (Fin 4) K) :
    uniDescAdj bar (A + B) = uniDescAdj bar A + uniDescAdj bar B := by
  ext i j; simp [uniDescAdj]

private theorem uniDescAdj_sub' (bar : K →+* K) (A B : Matrix (Fin 4) (Fin 4) K) :
    uniDescAdj bar (A - B) = uniDescAdj bar A - uniDescAdj bar B := by
  ext i j; simp [uniDescAdj]

private theorem uniDescAdj_smul' (bar : K →+* K) (c : K) (A : Matrix (Fin 4) (Fin 4) K) :
    uniDescAdj bar (c • A) = bar c • uniDescAdj bar A := by
  ext i j; simp [uniDescAdj]

private theorem uniDescAdj_vecMulVec (bar : K →+* K) (a b : Fin 4 → K) :
    uniDescAdj bar (vecMulVec a b) = vecMulVec (bv bar b) (bv bar a) := by
  ext i j; simp [uniDescAdj, vecMulVec_apply, bv, mul_comm]

private theorem star_rk1 (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x) (e : Fin 4 → K) :
    uniDescAdj bar (rk1 bar e) = rk1 bar e := by
  have h1 : bar (herm bar e e) = herm bar e e := (herm_comm bar hbb e e).symm
  unfold rk1
  rw [uniDescAdj_smul', uniDescAdj_vecMulVec, bv_bv bar hbb, map_inv₀, h1]

private theorem mul_rk1 (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x)
    {M : Matrix (Fin 4) (Fin 4) K} (hM : uniDescAdj bar M * M = 1) (e : Fin 4 → K) :
    M * rk1 bar e = rk1 bar (M *ᵥ e) * M := by
  have hN : herm bar (M *ᵥ e) (M *ᵥ e) = herm bar e e := herm_unitary bar hbb hM e e
  have hv : bv bar (M *ᵥ e) ᵥ* M = bv bar e := by
    rw [← bv_adj bar hbb, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  unfold rk1
  rw [Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.smul_mul, Matrix.vecMulVec_mul, hv, hN]

private theorem rk1_smul (bar : K →+* K) {κ : K} (hκ : κ ≠ 0) (e : Fin 4 → K) :
    rk1 bar (κ • e) = rk1 bar e := by
  have hκ' : bar κ ≠ 0 := (map_ne_zero bar).2 hκ
  have e1 : (bar κ)⁻¹ * bar κ = 1 := inv_mul_cancel₀ hκ'
  have e2 : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ
  unfold rk1
  rw [herm_smul_left, herm_smul_right, bv_smul, vecMulVec_smul, smul_vecMulVec]
  simp only [smul_smul]
  congr 1
  rw [mul_inv, mul_inv]
  linear_combination ((herm bar e e)⁻¹ * (κ⁻¹ * κ)) * e1 + (herm bar e e)⁻¹ * e2

private theorem comm_of_eigen (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x)
    {M : Matrix (Fin 4) (Fin 4) K} (hM : uniDescAdj bar M * M = 1) {e₀ e₁ : Fin 4 → K}
    {κ₀ κ₁ : K} (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (h0 : M *ᵥ e₀ = κ₀ • e₀)
    (h1 : M *ᵥ e₁ = κ₁ • e₁) :
    M * (rk1 bar e₀ + rk1 bar e₁) = (rk1 bar e₀ + rk1 bar e₁) * M := by
  rw [mul_add, add_mul, mul_rk1 bar hbb hM, mul_rk1 bar hbb hM, h0, h1, rk1_smul bar hκ₀,
    rk1_smul bar hκ₁]

private theorem comm_of_swap (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x)
    {M : Matrix (Fin 4) (Fin 4) K} (hM : uniDescAdj bar M * M = 1) {e₀ e₁ : Fin 4 → K}
    {κ₀ κ₁ : K} (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (h0 : M *ᵥ e₀ = κ₀ • e₁)
    (h1 : M *ᵥ e₁ = κ₁ • e₀) :
    M * (rk1 bar e₀ + rk1 bar e₁) = (rk1 bar e₀ + rk1 bar e₁) * M := by
  rw [mul_add, add_mul, mul_rk1 bar hbb hM, mul_rk1 bar hbb hM, h0, h1, rk1_smul bar hκ₀,
    rk1_smul bar hκ₁, add_comm]

private theorem su4_pair (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x) {e₀ e₁ : Fin 4 → K}
    (h0 : herm bar e₀ e₀ ≠ 0) (h1 : herm bar e₁ e₁ ≠ 0) (h01 : herm bar e₀ e₁ = 0)
    {M : Matrix (Fin 4) (Fin 4) K}
    (hcomm : M * (rk1 bar e₀ + rk1 bar e₁) = (rk1 bar e₀ + rk1 bar e₁) * M) :
    ∃ U : Matrix (Fin 4) (Fin 4) K, U * U = 1 ∧ U.det = 1 ∧ U.trace = 0 ∧ U * M = M * U ∧
      uniDescAdj bar U * U = 1 := by
  have hpr : ∀ e : Fin 4 → K, rk1 bar e = vecMulVec e ((herm bar e e)⁻¹ • bv bar e) := by
    intro e; unfold rk1; rw [vecMulVec_smul]
  have h10 : herm bar e₁ e₀ = 0 := by rw [herm_comm bar hbb e₀ e₁, h01, map_zero]
  have h00 : ((herm bar e₀ e₀)⁻¹ • bv bar e₀) ⬝ᵥ e₀ = 1 := by
    rw [smul_dotProduct, smul_eq_mul]
    exact inv_mul_cancel₀ h0
  have h11 : ((herm bar e₁ e₁)⁻¹ • bv bar e₁) ⬝ᵥ e₁ = 1 := by
    rw [smul_dotProduct, smul_eq_mul]
    exact inv_mul_cancel₀ h1
  have h01' : ((herm bar e₀ e₀)⁻¹ • bv bar e₀) ⬝ᵥ e₁ = 0 := by
    rw [smul_dotProduct, smul_eq_mul]
    show (herm bar e₀ e₀)⁻¹ * herm bar e₀ e₁ = 0
    rw [h01, mul_zero]
  have h10' : ((herm bar e₁ e₁)⁻¹ • bv bar e₁) ⬝ᵥ e₀ = 0 := by
    rw [smul_dotProduct, smul_eq_mul]
    show (herm bar e₁ e₁)⁻¹ * herm bar e₁ e₀ = 0
    rw [h10, mul_zero]
  rw [hpr, hpr] at hcomm
  have hU : pairU e₀ ((herm bar e₀ e₀)⁻¹ • bv bar e₀) e₁ ((herm bar e₁ e₁)⁻¹ • bv bar e₁) =
      1 - (rk1 bar e₀ + rk1 bar e₁) - (rk1 bar e₀ + rk1 bar e₁) := by
    unfold pairU
    rw [← hpr, ← hpr]
  have hstar : uniDescAdj bar
      (pairU e₀ ((herm bar e₀ e₀)⁻¹ • bv bar e₀) e₁ ((herm bar e₁ e₁)⁻¹ • bv bar e₁)) =
      pairU e₀ ((herm bar e₀ e₀)⁻¹ • bv bar e₀) e₁ ((herm bar e₁ e₁)⁻¹ • bv bar e₁) := by
    rw [hU, uniDescAdj_sub', uniDescAdj_sub', uniDescAdj_add', uniDescAdj_one,
      star_rk1 bar hbb, star_rk1 bar hbb]
  refine ⟨pairU e₀ ((herm bar e₀ e₀)⁻¹ • bv bar e₀) e₁ ((herm bar e₁ e₁)⁻¹ • bv bar e₁),
    pairU_mul_self h00 h11 h01' h10', pairU_det h00 h11 h01', pairU_trace h00 h11,
    pairU_comm hcomm, ?_⟩
  rw [hstar]
  exact pairU_mul_self h00 h11 h01' h10'

private theorem exists_vec_ne (M : Matrix (Fin 4) (Fin 4) K) (d : K) (h : M ≠ d • 1) :
    ∃ x : Fin 4 → K, M *ᵥ x - d • x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  exact sub_eq_zero.1 (hcon _)

private theorem su4_iso (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x) (h2 : (2 : K) ≠ 0)
    {M : Matrix (Fin 4) (Fin 4) K} (hM : uniDescAdj bar M * M = 1) {ν : K}
    (hν : bar ν * ν = 1) (hMν : M * M = (ν * ν) • 1) (hns : M ≠ (-ν) • 1) :
    ∃ a : Fin 4 → K, M *ᵥ a = ν • a ∧ herm bar a a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν
  have hMM : ∀ x : Fin 4 → K, M *ᵥ (M *ᵥ x) = (ν * ν) • x := by
    intro x
    rw [Matrix.mulVec_mulVec, hMν, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hplus : ∀ y : Fin 4 → K, M *ᵥ (M *ᵥ y - (-ν) • y) = ν • (M *ᵥ y - (-ν) • y) := by
    intro y
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMM]
    module
  have hminus : ∀ y : Fin 4 → K, M *ᵥ (M *ᵥ y - ν • y) = (-ν) • (M *ᵥ y - ν • y) := by
    intro y
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMM]
    module
  obtain ⟨x₀, hx₀⟩ := exists_vec_ne M (-ν) hns
  obtain ⟨a₀, ha₀, hne⟩ : ∃ a₀ : Fin 4 → K, M *ᵥ a₀ = ν • a₀ ∧ a₀ ≠ 0 :=
    ⟨M *ᵥ x₀ - (-ν) • x₀, hplus x₀, hx₀⟩
  obtain ⟨y, hy⟩ := herm_nondeg bar hne
  obtain ⟨a₁, ha₁, b, hb, hdec⟩ : ∃ a₁ : Fin 4 → K, M *ᵥ a₁ = ν • a₁ ∧
      ∃ b : Fin 4 → K, M *ᵥ b = (-ν) • b ∧ a₁ - b = (2 * ν) • y :=
    ⟨M *ᵥ y - (-ν) • y, hplus y, M *ᵥ y - ν • y, hminus y, by module⟩
  have hpm : herm bar a₀ b = 0 := herm_orth bar hbb h2 hM hν ha₀ hb
  have hs : herm bar a₀ a₁ ≠ 0 := by
    intro h
    have h' : herm bar a₀ ((2 * ν) • y) = 0 := by
      rw [← hdec, herm_sub_right, h, hpm, sub_zero]
    rw [herm_smul_right] at h'
    exact mul_ne_zero (mul_ne_zero h2 hν0) hy h'
  have he : M *ᵥ (a₀ + (herm bar a₀ a₁)⁻¹ • a₁) = ν • (a₀ + (herm bar a₀ a₁)⁻¹ • a₁) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, ha₀, ha₁]
    module
  have h00 := hcon a₀ ha₀
  have h11 := hcon a₁ ha₁
  have hee := hcon _ he
  rw [herm_lin2 bar hbb, h00, h11] at hee
  have e1 : (herm bar a₀ a₁)⁻¹ * herm bar a₀ a₁ = 1 := inv_mul_cancel₀ hs
  have e2 : bar ((herm bar a₀ a₁)⁻¹) * bar (herm bar a₀ a₁) = 1 := by
    rw [← map_mul, e1, map_one]
  exact h2 (by linear_combination hee - e1 - e2)

private theorem su4_geom (bar : K →+* K) (hbb : ∀ x, bar (bar x) = x) (h2 : (2 : K) ≠ 0)
    (hsq : ∀ l : K, bar l * l = 1 → IsSquare l)
    {M : Matrix (Fin 4) (Fin 4) K} (hM : uniDescAdj bar M * M = 1) {c : K}
    (hc : M * M = c • 1) (hns : ∀ d : K, M ≠ d • 1) :
    ∃ e₀ e₁ : Fin 4 → K, herm bar e₀ e₀ ≠ 0 ∧ herm bar e₁ e₁ ≠ 0 ∧ herm bar e₀ e₁ = 0 ∧
      M * (rk1 bar e₀ + rk1 bar e₁) = (rk1 bar e₀ + rk1 bar e₁) * M := by
  have hMMv : ∀ x : Fin 4 → K, M *ᵥ (M *ᵥ x) = c • x := by
    intro x
    rw [Matrix.mulVec_mulVec, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcn : bar c * c = 1 := by
    have e1 : herm bar (Pi.single 0 1 : Fin 4 → K) (Pi.single 0 1) = 1 := by
      simp [herm, bv]
    have h1 : herm bar (c • (Pi.single 0 1 : Fin 4 → K)) (c • Pi.single 0 1) =
        herm bar (Pi.single 0 1) (Pi.single 0 1) := by
      rw [← hMMv, herm_unitary bar hbb hM, herm_unitary bar hbb hM]
    rw [herm_smul_left, herm_smul_right, e1] at h1
    linear_combination h1
  obtain ⟨μ, hμ⟩ := hsq c hcn
  have hMμ : M * M = (μ * μ) • 1 := by rw [hc, hμ]
  have hMMμ : ∀ x : Fin 4 → K, M *ᵥ (M *ᵥ x) = (μ * μ) • x := by
    intro x
    rw [Matrix.mulVec_mulVec, hMμ, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [hμ] at hcn
    simp at hcn
  have hnμ : bar μ * μ = 1 ∨ bar μ * μ = -1 := by
    have h1 : (bar μ * μ) * (bar μ * μ) = bar c * c := by
      rw [hμ, map_mul]; ring
    rw [hcn] at h1
    exact mul_self_eq_one_iff.1 h1
  have hnμ0 : -μ ≠ 0 := neg_ne_zero.2 hμ0
  have hEp : ∀ x : Fin 4 → K, M *ᵥ (M *ᵥ x - (-μ) • x) = μ • (M *ᵥ x - (-μ) • x) := by
    intro x
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMMμ]
    module
  have hEm : ∀ x : Fin 4 → K, M *ᵥ (M *ᵥ x - μ • x) = (-μ) • (M *ᵥ x - μ • x) := by
    intro x
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMMμ]
    module
  rcases hnμ with hn1 | hn1
  ·
    obtain ⟨a, ha, hna⟩ := su4_iso bar hbb h2 hM hn1 hMμ (hns _)
    obtain ⟨b, hb, hnb⟩ := su4_iso bar hbb h2 hM (ν := -μ)
      (by rw [map_neg, neg_mul_neg]; exact hn1) (by rw [neg_mul_neg]; exact hMμ)
      (by rw [neg_neg]; exact hns μ)
    exact ⟨a, b, hna, hnb, herm_orth bar hbb h2 hM hn1 ha hb,
      comm_of_eigen bar hbb hM hμ0 hnμ0 ha hb⟩
  ·
    have hpp : ∀ u u' : Fin 4 → K, M *ᵥ u = μ • u → M *ᵥ u' = μ • u' → herm bar u u' = 0 := by
      intro u u' hu hu'
      have h := herm_eigen bar hbb hM hu hu'
      have h' : (2 : K) * herm bar u u' = 0 := by
        linear_combination h + (herm bar u u') * hn1
      exact (mul_eq_zero.1 h').resolve_left h2
    have hmm : ∀ u u' : Fin 4 → K, M *ᵥ u = (-μ) • u → M *ᵥ u' = (-μ) • u' →
        herm bar u u' = 0 := by
      intro u u' hu hu'
      have h := herm_eigen bar hbb hM hu hu'
      rw [map_neg] at h
      have h' : (2 : K) * herm bar u u' = 0 := by
        linear_combination h + (herm bar u u') * hn1
      exact (mul_eq_zero.1 h').resolve_left h2
    obtain ⟨x₀, hx₀⟩ := exists_vec_ne M (-μ) (hns _)
    obtain ⟨a₀, ha₀, hne⟩ : ∃ a₀ : Fin 4 → K, M *ᵥ a₀ = μ • a₀ ∧ a₀ ≠ 0 :=
      ⟨M *ᵥ x₀ - (-μ) • x₀, hEp x₀, hx₀⟩
    obtain ⟨y, hy⟩ := herm_nondeg bar hne
    obtain ⟨a₁, ha₁, b, hb, hdec⟩ : ∃ a₁ : Fin 4 → K, M *ᵥ a₁ = μ • a₁ ∧
        ∃ b : Fin 4 → K, M *ᵥ b = (-μ) • b ∧ a₁ - b = (2 * μ) • y :=
      ⟨M *ᵥ y - (-μ) • y, hEp y, M *ᵥ y - μ • y, hEm y, by module⟩
    have h0a := hpp a₀ a₁ ha₀ ha₁
    have haa := hpp a₀ a₀ ha₀ ha₀
    have hbb' := hmm b b hb hb
    have hs : herm bar a₀ b ≠ 0 := by
      intro h
      have h' : herm bar a₀ ((2 * μ) • y) = 0 := by
        rw [← hdec, herm_sub_right, h0a, h, sub_zero]
      rw [herm_smul_right] at h'
      exact mul_ne_zero (mul_ne_zero h2 hμ0) hy h'
    have e1 : (herm bar a₀ b)⁻¹ * herm bar a₀ b = 1 := inv_mul_cancel₀ hs
    have e2 : bar ((herm bar a₀ b)⁻¹) * bar (herm bar a₀ b) = 1 := by
      rw [← map_mul, e1, map_one]
    have hM0 : M *ᵥ (a₀ + (herm bar a₀ b)⁻¹ • b) =
        μ • (a₀ + (-(herm bar a₀ b)⁻¹) • b) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, ha₀, hb]
      module
    have hM1 : M *ᵥ (a₀ + (-(herm bar a₀ b)⁻¹) • b) =
        μ • (a₀ + (herm bar a₀ b)⁻¹ • b) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, ha₀, hb]
      module
    refine ⟨a₀ + (herm bar a₀ b)⁻¹ • b, a₀ + (-(herm bar a₀ b)⁻¹) • b, ?_, ?_, ?_,
      comm_of_swap bar hbb hM hμ0 hμ0 hM0 hM1⟩
    · rw [herm_lin2 bar hbb, haa, hbb']
      intro h
      exact h2 (by linear_combination h - e1 - e2)
    · rw [herm_lin2 bar hbb, haa, hbb', map_neg]
      intro h
      exact h2 (by linear_combination -h - e1 - e2)
    · rw [herm_lin2 bar hbb, haa, hbb']
      linear_combination -e1 + e2

end Unitary

section SU4

private theorem diag4_star {K : Type} [Field K] (bar : K →+* K) :
    uniDescAdj bar (diag4 : Matrix (Fin 4) (Fin 4) K) = diag4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniDescAdj, diag4, Matrix.diagonal]

private theorem neg_one_star {K : Type} [Field K] (bar : K →+* K) :
    uniDescAdj bar (-1 : Matrix (Fin 4) (Fin 4) K) = -1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [uniDescAdj]
  · simp [uniDescAdj, Matrix.one_apply, h, Ne.symm h]

theorem centralSquareFour_statedSU4 {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type}
    [Field K] [Finite K] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    CentralSquareFour ↥(CFSG.Open.StatedSU 4 (p ^ f) K) := by
  intro x hx
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      simp at this
    · exact hf
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hbar : ∀ y : K, hU.bar y = y ^ (p ^ f) := hU.bar_apply
  have hbb : ∀ y : K, hU.bar (hU.bar y) = y := hU.bar_bar
  have hq_odd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 :=
    CFSG.GH74.L5U5.two_ne_zero_of_odd_card (by rw [hK]; exact hq_odd.pow)
  have hmem : ∀ A : GL (Fin 4) K, A ∈ StatedSU 4 (p ^ f) K ↔
      (A : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
        uniDescAdj hU.bar (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 :=
    uniDesc_mem_statedSU_iff hU.bar hbar hbb
  have hZ : Subgroup.center (StatedProj (StatedSU 4 (p ^ f) K)) = ⊥ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_center_bot_pu hK (by norm_num) (by simp)
  have hxx : ((x * x : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K := by
    have hmk : (QuotientGroup.mk (x * x) : StatedProj (StatedSU 4 (p ^ f) K)) ∈
        Subgroup.center (StatedProj (StatedSU 4 (p ^ f) K)) := by
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective h
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx z]
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmk
    exact hmk
  rw [StatedScalars, MonoidHom.mem_range] at hxx
  obtain ⟨c, hc⟩ := hxx
  have hMM : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (c : K) • 1 := by
    have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Subgroup.coe_mul,
      Units.val_mul] at this
    rw [← this, Matrix.smul_one_eq_diagonal]
  obtain ⟨-, hMstar⟩ := (hmem _).1 x.2
  have hsq : ∀ l : K, hU.bar l * l = 1 → IsSquare l := by
    intro l hl
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at hl
    haveI : Fintype K := Fintype.ofFinite K
    have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    rw [FiniteField.isSquare_iff hchar hl0]
    have hcard : Fintype.card K = (p ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
    obtain ⟨m, hm⟩ := hq_odd
    have hl' : l ^ (p ^ f + 1) = 1 := by
      rw [pow_succ, ← hbar l]; exact hl
    have key : (p ^ f) ^ 2 = 2 * (m * (p ^ f + 1)) + 1 := by
      rw [hm]; ring
    have hdiv : (p ^ f) ^ 2 / 2 = m * (p ^ f + 1) := by
      rw [key]
      generalize m * (p ^ f + 1) = X
      omega
    rw [hcard, hdiv, pow_mul', hl', one_pow]
  have hneg : (-1 : GL (Fin 4) K) ∈ StatedSU 4 (p ^ f) K := by
    refine (hmem _).2 ⟨by simp [Matrix.det_neg] <;> norm_num, ?_⟩
    simp only [Units.val_neg, Units.val_one]
    rw [neg_one_star]
    simp
  by_cases hs : ∃ d : K, ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = d • 1
  · obtain ⟨d, hd⟩ := hs
    refine exists_klein_of_involution h2 _ hneg x diag4 diag4_sq diag4_trace ?_ ?_
    · refine (hmem _).2 ⟨diag4_det, ?_⟩
      show uniDescAdj hU.bar diag4 * diag4 = 1
      rw [diag4_star]
      exact diag4_sq
    · rw [hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  · push Not at hs
    obtain ⟨e₀, e₁, h0, h1, h01, hcomm⟩ := su4_geom hU.bar hbb h2 hsq hMstar hMM hs
    obtain ⟨U, hUU, hdet, htr, hUM, hUstar⟩ := su4_pair hU.bar hbb h0 h1 h01 hcomm
    exact exists_klein_of_involution h2 _ hneg x U hUU htr ((hmem _).2 ⟨hdet, hUstar⟩) hUM

end SU4

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
