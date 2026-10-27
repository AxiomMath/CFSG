module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Stage2.Final.ModelLUData
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5

namespace CFSG.GH74.Ivk413

theorem factorization_two_of_mod_four {m : ℕ} (h : m % 4 = 2) : m.factorization 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * (2 * k + 1) := ⟨m / 4, by omega⟩
  rw [Nat.factorization_mul (by norm_num) (by omega)]
  simp [Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * k + 1)]

theorem factorization_two_of_mod_eight {m : ℕ} (h : m % 8 = 4) : m.factorization 2 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 ^ 2 * (2 * k + 1) := ⟨m / 8, by omega⟩
  rw [Nat.factorization_mul (by norm_num) (by omega), Nat.factorization_pow]
  simp [Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * k + 1)]

variable {F : Type} [Field F]

theorem ratio_of_zsTwo [Finite F] {M : ModelData F} (hG : GoodModel M) (hZ : ZsTwo M) {m : ℕ}
    (hm : Nat.card ↥M.U2 = Nat.card ↥M.H2 * m) (hm4 : m % 4 = 2) :
    (Nat.card ↥(Cg M) / Nat.card ↥(K1 M ⊔ K2 M)).factorization 2 = 2 := by
  have hpos : 0 < Nat.card ↥(K1 M ⊔ K2 M) := Nat.card_pos
  rw [card_Cg_eq hG hZ hm, Nat.mul_div_cancel _ hpos,
    Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
    factorization_two_of_mod_four hm4]
  simp [Nat.Prime.factorization_self Nat.prime_two]

theorem ratio_of_zs4 [Finite F] {M : ModelData F} (hG : GoodModel M)
    (hZ4 : Nat.card ↥(Zs M) = 4) {m : ℕ}
    (hm : Nat.card ↥M.U2 = Nat.card ↥M.H2 * m) (hm8 : m % 8 = 4) :
    (Nat.card ↥(Cg M) / Nat.card ↥(K1 M ⊔ K2 M)).factorization 2 = 2 := by
  have hpos : 0 < Nat.card ↥(K1 M ⊔ K2 M) := Nat.card_pos
  rw [card_Cg_eq_four hG hZ4 hm, Nat.mul_div_cancel _ hpos]
  exact factorization_two_of_mod_eight hm8

theorem ratio_lin [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) (hodd : Nat.card F % 2 = 1)
    (hq : Nat.card F % 8 ≠ 1) :
    (Nat.card ↥(Cg (ModelData.lin F)) /
      Nat.card ↥(K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F))).factorization 2 = 2 := by
  have hG := goodModel_lin h2 h5
  have hU : Nat.card ↥(ModelData.lin F).U2 =
      Nat.card ↥(ModelData.lin F).H2 * (Nat.card F - 1) := card_U2_lin
  by_cases h4 : Nat.card F % 4 = 3
  · exact ratio_of_zsTwo hG (zsTwo_lin h4) hU (by omega)
  · have h8 : Nat.card F % 8 = 5 := by omega
    obtain ⟨i, hii⟩ := exists_i_of_card (F := F) h4
    have hi4 : i ^ 4 = 1 := pow_four_of_sq hii
    have hi : sc4 i ∈ (ModelData.lin F).K4 := ((ModelData.lin F).mem_K4 _).2
      ⟨Subgroup.mem_top _, by
        rw [det_sc4]
        have := congrArg (fun u : Fˣ => (u : F)) hi4
        simpa using this⟩
    exact ratio_of_zs4 hG (card_Zs_four h2 hii hi) hU (by omega)

theorem ratio_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hodd : p ^ f % 2 = 1)
    (hq : p ^ f % 8 ≠ 7) :
    (Nat.card ↥(Cg (ModelData.uni hF)) /
      Nat.card ↥(K1 (ModelData.uni hF) ⊔ K2 (ModelData.uni hF))).factorization 2 = 2 := by
  have hG := goodModel_uni hF hp2 h5
  have hU := card_U2_uni hF hp2
  by_cases h4 : p ^ f % 4 = 1
  · exact ratio_of_zsTwo hG (zsTwo_uni hF h4) hU (by omega)
  · have h8 : p ^ f % 8 = 3 := by omega
    have hcardF : Nat.card F % 4 ≠ 3 := by
      rw [hF, Nat.pow_mod, show p ^ f % 4 = 3 by omega]
      norm_num
    obtain ⟨i, hii⟩ := exists_i_of_card hcardF
    have hi4 := pow_four_of_sq hii
    have hiq : i ^ (p ^ f + 1) = 1 := by
      obtain ⟨m, hm⟩ : ∃ m, p ^ f + 1 = 4 * m := ⟨(p ^ f + 1) / 4, by omega⟩
      rw [hm, pow_mul, hi4, _root_.one_pow]
    have hi : sc4 i ∈ (ModelData.uni hF).K4 :=
      sc4_mem_of_sc2_mem ((sc2_mem_uni_iff hF i).2 hiq) (by rw [hii]; simp)
    exact ratio_of_zs4 hG (card_Zs_four hG.two_ne_zero hii hi) hU (by omega)

end CFSG.GH74.Ivk413
