module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52
public import CFSG.LocalAnalysis.GLTheoremA.CatB.O8p2
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Sporadic.Co2Smith

namespace Sp62Model

abbrev ι3 : Type := Fin 3 ⊕ Fin 3

abbrev J3 : Matrix ι3 ι3 (ZMod 2) := fromBlocks 0 1 (-1) 0

def mkSp3 (M N : Matrix ι3 ι3 (ZMod 2)) (h1 : M * N = 1) (h2 : N * M = 1)
    (hs : Mᵀ * J3 * M = J3) : Sp62 :=
  ⟨⟨M, N, h1, h2⟩, CFSG.Open.StatedAPI.mem_statedSp_iff.2 hs⟩

def yMat : Matrix ι3 ι3 (ZMod 2) :=
  fromBlocks !![0, 0, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0]
    !![1, 0, 0; 0, 0, 0; 0, 0, 0] 1

def sMat : Matrix ι3 ι3 (ZMod 2) := fromBlocks 1 !![0, 0, 0; 0, 1, 0; 0, 0, 0] 0 1

theorem yMat_cube : yMat * (yMat * yMat) = 1 := by decide
theorem yMat_cube' : (yMat * yMat) * yMat = 1 := by decide
theorem yMat_symp : yMatᵀ * J3 * yMat = J3 := by decide
theorem sMat_sq : sMat * sMat = 1 := by decide
theorem sMat_symp : sMatᵀ * J3 * sMat = J3 := by decide
theorem yMat_comm : yMat * sMat = sMat * yMat := by decide
theorem yMat_ne : yMat ≠ 1 := by decide
theorem sMat_ne : sMat ≠ 1 := by decide

def ySp : Sp62 := mkSp3 yMat (yMat * yMat) yMat_cube yMat_cube' yMat_symp

def sSp : Sp62 := mkSp3 sMat sMat sMat_sq sMat_sq sMat_symp

theorem sp62_exists_order3_normalizes_two : ∃ y : Sp62, orderOf y = 3 ∧
    ∃ W : Subgroup Sp62, IsPGroup 2 W ∧ W ≠ ⊥ ∧ y ∈ Subgroup.normalizer (W : Set Sp62) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : ySp ^ 3 = 1 := Subtype.ext (Units.ext (by
    simp only [pow_succ, pow_zero, one_mul, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one,
      Units.val_one]
    exact yMat_cube'))
  have hy1 : ySp ≠ 1 := fun h => yMat_ne (congrArg (fun g : Sp62 => ((g : GL ι3 (ZMod 2)) : Matrix ι3 ι3 (ZMod 2))) h)
  have hs2 : sSp ^ 2 = 1 := Subtype.ext (Units.ext (by
    simp only [pow_succ, pow_zero, one_mul, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one,
      Units.val_one]
    exact sMat_sq))
  have hs1 : sSp ≠ 1 := fun h => sMat_ne (congrArg (fun g : Sp62 => ((g : GL ι3 (ZMod 2)) : Matrix ι3 ι3 (ZMod 2))) h)
  have hc : Commute ySp sSp := Subtype.ext (Units.ext yMat_comm)
  refine ⟨ySp, orderOf_eq_prime hy3 hy1, Subgroup.zpowers sSp,
    isPGroup_zpowers_of_pow_eq_one hs2, ?_, mem_normalizer_zpowers_of_commute hc⟩
  intro h
  have : sSp ∈ (⊥ : Subgroup Sp62) := h ▸ Subgroup.mem_zpowers sSp
  exact hs1 (Subgroup.mem_bot.1 this)


end Sp62Model

@[expose] def HasThreeTwo (A : Type*) [Group A] : Prop :=
  ∃ y : A, orderOf y = 3 ∧
    ∃ W : Subgroup A, IsPGroup 2 W ∧ W ≠ ⊥ ∧ y ∈ Subgroup.normalizer (W : Set A)

theorem HasThreeTwo.of_mulEquiv {A B : Type*} [Group A] [Group B] (ε : A ≃* B)
    (h : HasThreeTwo B) : HasThreeTwo A := by
  obtain ⟨y, hy, W, hW, hWne, hyW⟩ := h
  refine ⟨ε.symm y, by rw [MulEquiv.orderOf_eq]; exact hy, W.map ε.symm.toMonoidHom,
    hW.map ε.symm.toMonoidHom, ?_, ?_⟩
  · intro h
    apply hWne
    have := (Subgroup.map_eq_bot_iff_of_injective (f := ε.symm.toMonoidHom) W ε.symm.injective).1 h
    exact this
  · rw [Subgroup.mem_normalizer_iff] at hyW ⊢
    intro x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have := hyW (ε x)
    simpa using this

theorem l94TypeHyAt_holds (G : Type) [Group G] [Finite G] : L94TypeHyAt G := by
  intro L hcat hZ
  have eZ : PSimple 3 L ≃* PQuot 3 L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with h | h | h | h
  · obtain ⟨e'⟩ := bridge_sp6two ⟨i, h, ⟨e⟩⟩
    exact HasThreeTwo.of_mulEquiv (eZ.symm.trans e') Sp62Model.sp62_exists_order3_normalizes_two
  · obtain ⟨e'⟩ := bridge_u4two ⟨i, h, ⟨e⟩⟩
    exact HasThreeTwo.of_mulEquiv (eZ.symm.trans e') U42.psp43_exists_order3_normalizes_two
  · obtain ⟨e'⟩ := bridge_d4two ⟨i, h, ⟨e⟩⟩
    exact HasThreeTwo.of_mulEquiv (eZ.symm.trans e') O8p2.om8_exists_order3_normalizes_two
  · obtain ⟨e'⟩ := bridge_u5two ⟨i, h, ⟨e⟩⟩
    exact HasThreeTwo.of_mulEquiv (eZ.symm.trans e') U52.su52_exists_order3_normalizes_two

end CFSG.LocalAnalysis.GLTheoremA.CatB
