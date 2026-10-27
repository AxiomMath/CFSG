module

public import CFSG.GH74.GLS.Stage2.Final.ModelLUData

public section

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.GLS.LU.Local CFSG.Blueprint

theorem luModelLeaf : LUModelLeaf := by
  intro Gs _ _ p f hp hp2 hq S' z' hz'
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  constructor
  · rintro ⟨h8, hL⟩
    obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    have h5 : 5 ≤ Nat.card F := by rw [hF]; exact hq
    have hcases : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 ∨ p ^ f % 8 = 7 := by
      obtain ⟨k, hk⟩ := hqodd
      omega
    have hdata : ∃ (S : Sylow 2 (PG (ModelData.lin F))) (t u : PG (ModelData.lin F)),
        LUModelData (PG (ModelData.lin F)) (Nat.card F) 1 (yP _) S (K1 _) (K2 _) t u := by
      rcases hcases with h | h | h
      · exact luModelData_lin_zs h2 h5 (by rw [hF]; omega)
      · exact luModelData_lin_mu4 h2 h5 (by rw [hF]; omega)
      · exact luModelData_lin_zs h2 h5 (by rw [hF]; omega)
    obtain ⟨S₀, t, u, hd⟩ := hdata
    rw [hF] at hd
    exact luModelData_transfer (show Gs ≃* PG (ModelData.lin F) from e)
      ((centerIs_iff _ _).1 hd.syl.z_cen) h2 S' z' hz' hd
  · rintro ⟨h8, hU⟩
    obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have : Fact p.Prime := ⟨hp⟩
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    have hcases : p ^ f % 8 = 1 ∨ p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 := by
      obtain ⟨k, hk⟩ := hqodd
      omega
    obtain ⟨S₀, t, u, hd⟩ : ∃ (S : Sylow 2 (PG (ModelData.uni hF))) (t u : PG (ModelData.uni hF)),
        LUModelData (PG (ModelData.uni hF)) (p ^ f) (-1) (yP _) S (K1 _) (K2 _) t u := by
      rcases hcases with h | h | h
      · exact luModelData_uni_zs hF hp2 hq (by omega)
      · exact luModelData_uni_mu4 hF hp2 hq h
      · exact luModelData_uni_zs hF hp2 hq (by omega)
    exact luModelData_transfer (show Gs ≃* PG (ModelData.uni hF) from e)
      ((centerIs_iff _ _).1 hd.syl.z_cen) h2 S' z' hz' hd

end CFSG.GH74.GLS.Stage2.Final
