module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AU
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AN
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AL
public import CFSG.LocalAnalysis.EvenBN.GMSK.Statement

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

structure Y6YData {Y : Type} [Group Y] (τ : Y) (J M : Subgroup Y) : Prop where
  tau_order : orderOf τ = 2
  J_simple : IsSimpleGroup ↥J
  J_nonab : ¬ IsMulCommutative ↥J
  J_norm : centralizer ({τ} : Set Y) ≤ normalizer (J : Set Y)
  J_cent : centralizer (J : Set Y) ⊓ centralizer ({τ} : Set Y) = zpowers τ
  J_perf : ∀ B : Subgroup Y, B ≤ centralizer ({τ} : Set Y) → Group.IsPerfect ↥B → B ≤ J
  J_SL : ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ 3 ∧
    Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin 2) k)
  J_aut : ∀ α : MulAut ↥J, α ^ 4 = 1 → α ^ 2 = 1
  M_equiv : Nonempty (↥M ≃* (Fin 3 → Multiplicative (ZMod 4)))
  M_inv : ∀ m ∈ M, τ * m * τ⁻¹ = m⁻¹

variable {Y : Type} [Group Y] {τ : Y} {J M : Subgroup Y}

theorem y6f4a_four_dvd_card_of_sl
    (hJ : ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ 3 ∧
      Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin 2) k)) : 4 ∣ Nat.card ↥J := by
  obtain ⟨k, hF, hFin, hk, ⟨e⟩⟩ := hJ
  letI : Field k := hF
  letI : Fintype k := hFin
  have hcard : Nat.card ↥J = Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) :=
    Nat.card_congr e.toEquiv
  rw [hcard, Matrix.card_SL_field (𝔽 := k) 2, hk, Fin.prod_univ_two]
  norm_num

theorem y6f4a_solvableRadical_eq_bot_of_data [Finite Y]
    (hO : CFSG.Open.standardComponentOddCore Y = ⊥) (hY : Y6YData τ J M) :
    CFSG.solvableRadical Y = ⊥ :=
  y6f4a_solvableRadical_eq_bot hO fun Q hQ h2 =>
    y6f4a_normal_two_eq_bot hY.tau_order hY.J_simple hY.J_nonab hY.J_norm hY.J_cent
      (y6f4a_tau_not_central hY.M_equiv hY.M_inv) hQ h2

theorem y6f4a_stdLinearData [Finite Y] (hY : Y6YData τ J M) :
    CFSG.LocalAnalysis.EvenBN.GMSK.StdLinearData Y J 3 ∧
      ∀ S : Sylow 2 ↥(centralizer (J : Set Y)), Nat.card S = 2 := by
  have hqs : CFSG.Open.IsQuasisimple ↥J := by
    exact y6f4a_isQuasisimple_of_simple hY.J_simple hY.J_nonab
  have hτJ : τ ∈ centralizer (J : Set Y) := by
    have hmem : τ ∈ centralizer (J : Set Y) ⊓ centralizer ({τ} : Set Y) := by
      rw [hY.J_cent]
      exact Subgroup.mem_zpowers τ
    exact (Subgroup.mem_inf.mp hmem).1
  have h4 : 4 ∣ Nat.card ↥J := y6f4a_four_dvd_card_of_sl hY.J_SL
  have hstd := y6f4a_standard_of_invol (X := Y) (A := J) hY.tau_order hqs hτJ hY.J_norm
    hY.J_cent hY.J_perf h4
  refine ⟨?_, hstd.2⟩
  unfold CFSG.LocalAnalysis.EvenBN.GMSK.StdLinearData
  exact ⟨by norm_num, hstd.1, y6f4a_not_normal hstd.2 hY.M_equiv hY.J_aut, hY.J_SL⟩

end CFSG.OddStandard.HigherRank.YamadaG23
