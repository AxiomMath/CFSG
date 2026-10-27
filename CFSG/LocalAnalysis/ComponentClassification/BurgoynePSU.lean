module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraph
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSL
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUInnerPaired

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.Blueprint

theorem graph_sq {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}
    (hn : 1 ≤ n) (A : uU h n) :
    (uConjAut h hn A * uFieldAut h hn (barEq h)) ^ 2 =
      uConjAut h hn (A * uGlAut h (barEq h) A) := by
  have hbb : barEq h * barEq h = 1 := RingEquiv.ext fun c => h.bar_bar c
  rw [pow_two, mul_assoc, ← mul_assoc (uFieldAut h hn (barEq h)), uFieldAut_mul_uConjAut,
    mul_assoc, ← map_mul, hbb, map_one, mul_one, ← map_mul]

theorem burgoynePropA_PSU (X : Type) [Group X] [Finite X] (hX : IsM4 X) {n p f : ℕ}
    (hp2 : p ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .PSU n p f) (t : X)
    (ht : orderOf t = 2) (Y : Subgroup X) (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) :
    PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · obtain ⟨⟨hp, hf, hn, hq⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hKc, ← pow_mul, mul_comm]⟩
    have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨e1, e2⟩ => hq (by rw [e1, e2])
    have hψ := socleAction_injective hsimple hnab θ
    have hInn : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
        MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ (socleAction θ).range := by
      rintro _ ⟨x, rfl⟩
      exact conj_mem_range_socleAction θ x
    have hinj := conj_injective_of_mulEquiv hsimple hnab θ
    obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut h hn hq' (socleAction θ t)
    have hsq : (uConjAut h (by omega) A * uFieldAut h (by omega) φ) ^ 2 = 1 := by
      rw [← hα, ← map_pow, ← ht, pow_orderOf_eq_one, map_one]
    set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
    rcases uFieldAut_eq_or_of_sq h hn hq' hsq with rfl | hφ
    ·
      rw [map_one, mul_one] at hα hsq
      rw [← map_pow] at hsq
      obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
      have hAA : Am * Am = (c : K) • 1 := by
        have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
        simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar]
          at e
        rw [← pow_two, e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      have hU : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
      have hN : h.norm (c : K) = 1 := by
        have e : ((Am * Am).map h.bar)ᵀ * (Am * Am) = 1 := by
          rw [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ Am Am, hU,
            Matrix.one_mul, hU]
        rw [hAA] at e
        have e1 := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
        simp [Matrix.mul_apply, Matrix.one_apply] at e1
        rw [UnitaryFieldData.norm, mul_comm]
        simpa [Matrix.smul_apply, Matrix.one_apply] using e1
      obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one h hp2 hN
      have hAA' : Am * Am = (l ^ 2) • 1 := by rw [hAA, hlc]
      have hNl : h.norm l * h.norm l = 1 := by
        rw [← hN, ← hlc, UnitaryFieldData.norm, UnitaryFieldData.norm, map_pow]
        ring
      rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
      · have hns : ∀ c : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c := by
          intro c e
          have h1 : uConjAut h (by omega) A = 1 := (uConjAut_eq_one_iff h hn A).2 ⟨c, e⟩
          rw [h1, ← map_one (socleAction θ)] at hα
          have := hψ hα
          rw [this, orderOf_one] at ht
          exact absurd ht (by decide)
        exact innerSplit_propAConclusion h hp2 hn hinj hψ hInn hα hl0 hN1 hAA' hns hY hYO
      · exact innerPaired_propAConclusion h hp2 hn hinj hψ hInn hα hl0 hN1 hAA' hY hYO
    ·
      have hφe : φ = barEq h := RingEquiv.ext hφ
      subst hφe
      rw [graph_sq] at hsq
      obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
      have hAc : Am * Am.map h.bar = (c : K) • 1 := by
        have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
        simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_uGlAut]
          at e
        change ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (barEq h) = _
        rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      refine absurd (eq_bot_of_oddCoreIn hψ ?_ hYO) hY
      rw [hα]
      exact graph_oddCoreIn_eq_bot h hp2 hn hinj hInn hAc
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.U
