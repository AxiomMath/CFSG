module

public import Mathlib.GroupTheory.Frattini
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.RankThree.GroupTheory.SteinbergBKFrattiniOuterPrimeBound
import CFSG.GH74.Generic.S45.AutCard

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

private theorem card_dvd_card_centralizer_mul_card_mulAut_of_normal {X : Type*} [Group X]
    [Finite X] (N : Subgroup X) [N.Normal] :
    Nat.card X ∣ Nat.card (Subgroup.centralizer (N : Set X)) * Nat.card (MulAut N) := by
  have hcard : Nat.card (Subgroup.normalizer (N : Set X)) = Nat.card X := by
    rw [Subgroup.normalizer_eq_top N, Subgroup.card_top]
  rw [← hcard, ← CFSG.GH74.Generic.S45.card_range_normalizerMonoidHom_mul N,
    mul_comm (Nat.card (Subgroup.centralizer (N : Set X)))]
  exact mul_dvd_mul_right (Subgroup.card_subgroup_dvd_card _) _

theorem exists_card_mulAut_dvd_of_isPGroup {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P) :
    ∃ r s : ℕ, p ^ r ≤ Nat.card P ∧
      Nat.card (MulAut P) ∣ p ^ s * ∏ i : Fin r, (p ^ r - p ^ (i : ℕ)) := by
  obtain ⟨r, hr⟩ := (hP.to_quotient (frattini P)).exists_card_eq
  obtain ⟨s, hs⟩ := CFSG.RankThree.GroupTheory.SteinbergBK.card_mulAut_dvd_pow_mul_card_GL hP hr
  refine ⟨r, s, ?_, ?_⟩
  · rw [← hr]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  · rwa [Matrix.card_GL_field, ZMod.card] at hs

theorem exists_card_dvd_of_centralizer_pCore_le {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime]
    (hC : Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X) :
    ∃ r s : ℕ, p ^ r ≤ Nat.card (CFSG.pCore p X) ∧
      Nat.card X ∣ p ^ s * ∏ i : Fin r, (p ^ r - p ^ (i : ℕ)) := by
  have := CFSG.pCore_normal (p := p) (G := X)
  have hPp : IsPGroup p (CFSG.pCore p X) := CFSG.pCore_isPGroup
  obtain ⟨r, s, hr, hs⟩ := exists_card_mulAut_dvd_of_isPGroup hPp
  obtain ⟨a, ha⟩ := (hPp.to_le hC).exists_card_eq
  refine ⟨r, a + s, hr, ?_⟩
  refine (card_dvd_card_centralizer_mul_card_mulAut_of_normal (CFSG.pCore p X)).trans ?_
  rw [ha, pow_add, mul_assoc]
  exact mul_dvd_mul_left _ hs

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
