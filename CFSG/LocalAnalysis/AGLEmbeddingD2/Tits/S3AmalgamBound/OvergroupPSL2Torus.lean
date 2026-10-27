module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_3_split

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

theorem three_dvd_of_mul_eq {z g N : ℕ} (hg : g = 1 ∨ g = 2) (hzg : z * g = N) (h3 : 3 ∣ N) :
    3 ∣ z := by
  have hc : Nat.Coprime 3 g := by rcases hg with rfl | rfl <;> norm_num
  exact hc.dvd_of_dvd_mul_right (hzg ▸ h3)

theorem exists_torus_element {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3) :
    ∃ (z g : ℕ) (t : PSL2MatrixGroup F), 3 ∣ z ∧ 0 < g ∧ g ≤ 2 ∧
      (z * g = Nat.card F - 1 ∨ z * g = Nat.card F + 1) ∧ orderOf t = z := by
  have hq3 : ¬ 3 ∣ Nat.card F := by
    rw [hF]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hgpos : 0 < Nat.gcd (Nat.card F - 1) 2 := Nat.gcd_pos_of_pos_right _ (by norm_num)
  have hgle : Nat.gcd (Nat.card F - 1) 2 ≤ 2 := Nat.gcd_le_right _ (by norm_num)
  have hg12 : Nat.gcd (Nat.card F - 1) 2 = 1 ∨ Nat.gcd (Nat.card F - 1) 2 = 2 := by omega
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hmul1 : (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 * Nat.gcd (Nat.card F - 1) 2 =
      Nat.card F - 1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hmod : Nat.card F % 3 = 1 ∨ Nat.card F % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · obtain ⟨U, w, hUc, hUcard, -⟩ := huppert_II_8_3_split_torus_reflection_data hF
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
    have hz : Nat.card U * Nat.gcd (Nat.card F - 1) 2 = Nat.card F - 1 := by
      rw [hUcard, hmul1]
    exact ⟨Nat.card U, Nat.gcd (Nat.card F - 1) 2, (u : PSL2MatrixGroup F),
      three_dvd_of_mul_eq hg12 hz (by omega), hgpos, hgle, Or.inl hz,
      by rw [Subgroup.orderOf_coe, hu]⟩
  · obtain ⟨S, w, hSc, hScard, -⟩ := huppert_II_8_4_nonsplit_torus_reflection_data hF
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
    have hdvd : Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F + 1 := by
      rcases hg12 with h | h
      · rw [h]; exact one_dvd _
      · have h2 : 2 ∣ Nat.card F - 1 := h ▸ Nat.gcd_dvd_left _ _
        rw [h]; omega
    have hz : Nat.card S * Nat.gcd (Nat.card F - 1) 2 = Nat.card F + 1 := by
      rw [hScard]; exact Nat.div_mul_cancel hdvd
    exact ⟨Nat.card S, Nat.gcd (Nat.card F - 1) 2, (u : PSL2MatrixGroup F),
      three_dvd_of_mul_eq hg12 hz (by omega), hgpos, hgle, Or.inr hz,
      by rw [Subgroup.orderOf_coe, hu]⟩

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2
