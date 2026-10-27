module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenPair
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.WitnessTools
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterBetaAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP.Fus
open scoped commutatorElement
open CFSG.AGLEmbedding.Norton.MON11_13

theorem commutatorElement_inv_inv_of_commute {G : Type} [Group G] {x y : G}
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) : ⁅x⁻¹, y⁻¹⁆ = ⁅x, y⁆ := by
  set z := ⁅x, y⁆ with hz
  have h1 : x * y = z * y * x := by
    rw [hz, commutatorElement_def]; group
  have hc : y⁻¹ * z = z * y⁻¹ := (hzy.inv_right).eq.symm
  rw [commutatorElement_def, inv_inv, inv_inv]
  calc x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by simp only [mul_assoc]
    _ = x⁻¹ * y⁻¹ * (z * y * x) := by rw [h1]
    _ = x⁻¹ * (y⁻¹ * z) * y * x := by simp only [mul_assoc]
    _ = x⁻¹ * (z * y⁻¹) * y * x := by rw [hc]
    _ = x⁻¹ * z * x := by group
    _ = z := by rw [mul_assoc, hzx.eq, ← mul_assoc, inv_mul_cancel, one_mul]

theorem thirteen_cubic_det :
    (((1 : ℕ) : ZMod 13) * ((12 : ℕ) : ZMod 13) - 1) *
      (((1 : ℕ) : ZMod 13) * ((12 : ℕ) : ZMod 13) - 1) -
        ((1 : ℕ) : ZMod 13) ^ 2 * ((0 : ℕ) : ZMod 13) * ((0 : ℕ) : ZMod 13) ≠ 0 := by
  decide

theorem kernelTrivialAt_thirteen_Gmat 
    [Finite ↥CFSG.Monster.Generated.Gmat]
    (hS : ¬ 13 ^ 4 ∣ Nat.card ↥CFSG.Monster.Generated.Gmat) :
    KernelTrivialAt ↥CFSG.Monster.Generated.Gmat 13 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨x, y, h, hx, hy, hz1, hzx, hzy, hh, hhx, hhy⟩ := thirteen_heisenberg_inversion
  have hinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  have hx12 : x ^ 12 = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact hx
  have hy12 : y ^ 12 = y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact hy
  have hz : h * ⁅x, y⁆ * h = ⁅x, y⁆ := by
    have key := map_commutatorElement (MulAut.conj h) x y
    simp only [MulAut.conj_apply, hinv, hhx, hhy] at key
    rw [commutatorElement_inv_inv_of_commute hzx hzy] at key
    exact key
  exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.kernelTrivialAt_of_cubic_heisenberg (p := 13) (x := x) (y := y) (h := h) hx hy hz1 hzx hzy hS
    (a := 12) (b := 0) (c := 0) (d := 12) (k := 0) (l := 0) (μ := 1)
    (by rw [hinv, hhx, hx12]; simp) (by rw [hinv, hhy, hy12]; simp)
    (by rw [hinv, pow_one]; exact hz) thirteen_cubic_det

theorem kernelTrivialAt_thirteen_of_mulEquiv_Gmat
    {T : Type} [Group T] [Finite T] (e : T ≃* ↥CFSG.Monster.Generated.Gmat)
    (hS : ¬ 13 ^ 4 ∣ Nat.card T) : KernelTrivialAt T 13 := by
  haveI : Finite ↥CFSG.Monster.Generated.Gmat := Finite.of_equiv T e.toEquiv
  rw [Nat.card_congr e.toEquiv] at hS
  exact kernelTrivialAt_of_mulEquiv e (kernelTrivialAt_thirteen_Gmat hS)

theorem monsterBetaData_of_thirteen_cubic :
    CFSG.AGLEmbedding.MonsterBetaData := by
  have :IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) := carrier_M_simple
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := CFSG.Blueprint.NativeSporadic.Carrier .M) (MulEquiv.refl _)
  exact monsterBetaData_of_monster13 CFSG.Open.Open.monster_y443_derived_card
      (Or.inl (hasNoncommPair_thirteen_of_mulEquiv_Gmat ε))

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
