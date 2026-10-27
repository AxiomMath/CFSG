module

public import CFSG.ClassicalInvolution.Q3.Q3PPKleinAt
import CFSG.ClassicalInvolution.Asc77.AscMuTabG2
import CFSG.ClassicalInvolution.Asc77.AscMuTabTD4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77

section Abstract

theorem kleinData_of_data (c : CompData) (hcenter : Subgroup.center c.G = ⊥)
    (hconj : ∀ R ∈ c.fund, ∀ g : c.G, conjSub g R ∈ c.fund)
    (hdata : ∀ R ∈ c.fund, ∃ u d : c.G, IsUniqueInvolution R u ∧ d * d = 1 ∧ d ≠ 1 ∧ d ≠ u ∧
      u * d = d * u)
    (hinv : ∀ x y : c.G, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → ∃ g, g * x * g⁻¹ = y) :
    KleinData c where
  center := hcenter
  unique_inv := by
    intro R hR a ha b hb ha2 hb2 ha1 hb1
    obtain ⟨u, d, hu, -⟩ := hdata R hR
    exact ((hu.unique a ha ha2).resolve_left ha1).trans
      ((hu.unique b hb hb2).resolve_left hb1).symm
  conj_fund := hconj
  klein := by
    intro R hR r hr hr2 hr1
    obtain ⟨u, d, hu, hd2, hd1, hdu, hud⟩ := hdata R hR
    have hru : r = u := (hu.unique r hr hr2).resolve_left hr1
    subst hru
    have hprod2 : (r * d) * (r * d) = 1 := by
      calc (r * d) * (r * d) = (r * r) * (d * d) := by
            calc (r * d) * (r * d) = r * (d * r) * d := by group
              _ = r * (r * d) * d := by rw [← hud]
              _ = (r * r) * (d * d) := by group
        _ = 1 := by rw [hr2, hd2, one_mul]
    have hprod1 : r * d ≠ 1 := by
      intro h
      apply hdu
      calc d = (r * r) * d := by rw [hr2, one_mul]
        _ = r * (r * d) := by group
        _ = r := by rw [h, mul_one]
    obtain ⟨g', hg'⟩ := hinv r d hr2 hd2 hr1 hd1
    obtain ⟨g'', hg''⟩ := hinv r (r * d) hr2 hprod2 hr1 hprod1
    exact ⟨d, g', g'', hg'.symm, hg''.symm, hud.symm, hdu⟩

theorem mul_comm_of_orderFour {G : Type} [Group G] {R : Subgroup G} {u j d : G}
    (hu : IsUniqueInvolution R u) (hj : j ∈ R) (hj4 : orderOf j = 4) (hjd : j * d = d * j) :
    u * d = d * u := by
  have hj2sq : (j * j) * (j * j) = 1 := by
    have h4 : j ^ 4 = 1 := by rw [← hj4]; exact pow_orderOf_eq_one j
    calc (j * j) * (j * j) = j ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4
  have hj2ne : j * j ≠ 1 := by
    intro h
    have h2 : orderOf j ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hj4] at h2
    omega
  have hju : j * j = u := (hu.unique _ (R.mul_mem hj hj) hj2sq).resolve_left hj2ne
  calc u * d = (j * j) * d := by rw [hju]
    _ = j * (j * d) := by group
    _ = j * (d * j) := by rw [hjd]
    _ = (j * d) * j := by group
    _ = (d * j) * j := by rw [hjd]
    _ = d * (j * j) := by group
    _ = d * u := by rw [hju]

end Abstract


section Models

theorem kleinData_g2 {n : ℕ} (hadm : StatedLieAdmissible .G2 n 3 1) :
    KleinData (CompData.model .G2 n) := by
  have hn : n = 0 := hadm.2.2.1
  subst hn
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 one_ne_zero]
    exact (Nat.Prime.odd_of_ne_two Nat.prime_three hp2).pow
  refine kleinData_of_data _ ?_ ?_ ?_ ?_
  · exact RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inl rfl) 0 le_rfl
  · intro R hR g
    exact RouteD.conjSub_mem_fundamentalSubgroups hR g
  · intro R hR
    obtain ⟨c, j, d, hc, hj, hj4, hd, hd1, hdc, hjd⟩ :=
      MuTab.g2_exists_orderFour (p := 3) (e := 1) hp2 le_rfl hR
    exact ⟨c, d, hc, hd, hd1, hdc, mul_comm_of_orderFour hc hj hj4 hjd⟩
  · intro x y hx hy hx1 hy1
    exact g2_involutions_conj hodd hx hy hx1 hy1

theorem kleinData_trialityD4 {n : ℕ} (hadm : StatedLieAdmissible .trialityD4 n 3 1) :
    KleinData (CompData.model .trialityD4 n) := by
  have hn : n = 0 := hadm.2.2
  subst hn
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  refine kleinData_of_data _ ?_ ?_ ?_ ?_
  · exact RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0 le_rfl
  · intro R hR g
    exact RouteD.conjSub_mem_fundamentalSubgroups hR g
  · intro R hR
    obtain ⟨c, j, d, hc, hj, hj4, hd, hd1, hdc, hjd⟩ :=
      MuTab.td4_exists_orderFour (p := 3) (e := 1) hp2 hadm hR
    exact ⟨c, d, hc, hd, hd1, hdc, mul_comm_of_orderFour hc hj hj4 hjd⟩
  · intro x y hx hy hx1 hy1
    exact trialityD4_involutions_conj (p := 3) (e := 1) hp2 le_rfl hx hy hx1 hy1

end Models

end CFSG.ClassicalInvolution.Q3.Q3PP
