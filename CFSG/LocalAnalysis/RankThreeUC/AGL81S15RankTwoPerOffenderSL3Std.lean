module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat

import CFSG.Quasithin.H13.L32AC44b
import CFSG.Quasithin.Vol2.Ch4Sec2CentKLinPerf
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Matrix
open scoped MatrixGroups

theorem natSchur_sl3 {F : Type} [Field F] :
    NatSchur (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F) := by
  intro c hc
  exact CFSG.Quasithin.H13.L32A.C.SL3N.eq_smul_of_comm c fun g v => by
    simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hc g v

theorem natOut_sl3 {F : Type} [Field F] [CharP F 2] :
    NatOut (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F) := by
  intro M hM _
  obtain ⟨d, hd⟩ : ∃ d : F, d = (M : Matrix (Fin 3) (Fin 3) F).det := ⟨_, rfl⟩
  have hdd : d * d = 1 := by
    rw [hd]
    have h := congrArg (fun N : GL (Fin 3) F => (N : Matrix (Fin 3) (Fin 3) F).det) hM
    simpa [Units.val_mul, Matrix.det_mul] using h
  have hd1 : d = 1 := by
    have hsq : d ^ 2 = (1 : F) ^ 2 := by rw [pow_two, hdd]; norm_num
    exact CharTwo.sq_inj.mp hsq
  have hdet : (M : Matrix (Fin 3) (Fin 3) F).det = 1 := by rw [← hd, hd1]
  exact ⟨⟨(M : Matrix (Fin 3) (Fin 3) F), hdet⟩, by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl⟩

theorem sl3_perfStab {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    PerfStab (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F) := by
  intro u
  by_cases hu : u = 0
  · subst hu
    have htop : stabL (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F) 0 = ⊤ := by
      ext g
      simp [stabL]
    rw [htop, ← commutator_def,
      CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (n := 3) (by omega)]
  · have hstab : stabL (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F) u =
        CFSG.Quasithin.H13.Ch4.CentK.stabVec u := by
      ext g
      rw [CFSG.Quasithin.H13.Ch4.CentK.mem_stabVec]
      simp [stabL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    rw [hstab]
    let _ : Fintype F := Fintype.ofFinite F
    have h4' : 4 ≤ Fintype.card F := by
      simpa [Nat.card_eq_fintype_card] using h4
    exact CFSG.Quasithin.H13.Ch4.CentK.stabVec_perfect h4' hu

end CFSG.LocalAnalysis.RankThreeUC.S15
