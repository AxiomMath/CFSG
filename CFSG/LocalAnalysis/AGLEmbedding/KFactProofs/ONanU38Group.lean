module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Arr
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open scoped Matrix

theorem hU : UnitaryFieldData 2 3 GF64 := ⟨Nat.prime_two, by norm_num, by
  rw [GF64.card_eq]
  norm_num⟩

theorem bar_apply_eq (c : GF64) : hU.bar c = barC c := by
  rw [UnitaryFieldData.bar_apply, barC_eq_pow]
  rfl

abbrev SU : Subgroup (GL (Fin 3) GF64) := unitarySU 2 3 GF64 3

abbrev GU : Subgroup (GL (Fin 3) GF64) := unitaryIsom3 hU

@[expose] def detArr3 (A : Array GF64) : GF64 :=
  A.getD 0 0 * (A.getD 4 0 * A.getD 8 0 + A.getD 5 0 * A.getD 7 0) +
  A.getD 1 0 * (A.getD 3 0 * A.getD 8 0 + A.getD 5 0 * A.getD 6 0) +
  A.getD 2 0 * (A.getD 3 0 * A.getD 7 0 + A.getD 4 0 * A.getD 6 0)

theorem det_toMat3 (A : Array GF64) : (toMat3 A).det = detArr3 A := by
  rw [Matrix.det_fin_three]
  simp only [toMat3, Matrix.of_apply, detArr3]
  have h2 : (2 : GF64) = 0 := two_eq_zero
  have hneg : ∀ a : GF64, -a = a := fun a => by
    have : a + a = 0 := by rw [← two_mul, h2, zero_mul]
    exact neg_eq_of_add_eq_zero_right this
  simp only [sub_eq_add_neg, hneg]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

@[expose] def isSUArr (A : Array GF64) : Bool :=
  A.size == 9 && detArr3 A == 1 && mulArr3 (conjTrArr3 A) A == oneArr3

theorem exists_su_of_isSUArr {A : Array GF64} (h : isSUArr A = true) :
    ∃ g : SU, ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) = toMat3 A := by
  simp only [isSUArr, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hsz, hdet⟩, hmul⟩ := h
  have hM : ((toMat3 A).map hU.bar)ᵀ * toMat3 A = 1 := by
    have h1 := congrArg toMat3 hmul
    rw [toMat3_mulArr3, toMat3_conjTrArr3, toMat3_oneArr3] at h1
    have : (toMat3 A).map hU.bar = (toMat3 A).map barC :=
      Matrix.ext fun i j => bar_apply_eq _
    rw [this]
    exact h1
  have hdet' : (toMat3 A).det = 1 := by rw [det_toMat3, hdet]
  have hinv : toMat3 A * ((toMat3 A).map hU.bar)ᵀ = 1 :=
    mul_eq_one_comm.1 hM
  let g : GL (Fin 3) GF64 := ⟨toMat3 A, ((toMat3 A).map hU.bar)ᵀ, hinv, hM⟩
  refine ⟨⟨g, (mem_unitarySU_iff hU).2 ⟨hdet', hM⟩⟩, rfl⟩

theorem coe_suField_sigma2 (g : SU) :
    ((suField hU sigma2Equiv g : SU) : GL (Fin 3) GF64).val =
      (g : GL (Fin 3) GF64).val.map sigma2 := by
  rw [coe_suField]
  rfl

end CFSG.AGLEmbedding.ChevOuter.U38
