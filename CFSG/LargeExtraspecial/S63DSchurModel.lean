module

public import CFSG.LargeExtraspecial.S63CD4AData
public import Certificates.Certificate21180

public section

namespace CFSG.LargeExtraspecial.S63

open Subgroup CFSG.Quasithin

theorem d4SplitCheck_eq_true : d4SplitCheck = true := Certificates.certificate21180

theorem parts_of_d4SplitCheck (h : d4SplitCheck = true) :
    mulR (wordR d4Gens d4yWord) (wordR d4Gens d4yInvWord) = oneR ∧
    mulR d4Gens[0]! z0R = mulR z0R d4Gens[0]! ∧
    mulR (wordR d4Gens d4yWord) z0R = mulR z0R (wordR d4Gens d4yWord) ∧
    mulR d4Gens[0]! d4Gens[1]! = mulR d4Gens[1]! d4Gens[0]! ∧
    mulR d4Gens[0]! d4Gens[2]! = mulR d4Gens[2]! d4Gens[0]! ∧
    mulR d4Gens[1]! d4Gens[2]! = mulR d4Gens[2]! d4Gens[1]! ∧
    mulR (mulR (wordR d4Gens d4yWord) d4Gens[0]!) (wordR d4Gens d4yInvWord) = d4Gens[2]! ∧
    mulR (mulR (wordR d4Gens d4yWord) d4Gens[2]!) (wordR d4Gens d4yInvWord) =
      mulR d4Gens[2]! d4Gens[1]! ∧
    mulR (mulR (wordR d4Gens d4yWord) (mulR d4Gens[2]! d4Gens[1]!)) (wordR d4Gens d4yInvWord) =
      mulR d4Gens[2]! d4Gens[0]! ∧
    wordR qGens d4MidQWord = d4Gens[6]! := by
  simp only [d4SplitCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

@[expose] noncomputable def d4y : trialityGroup8 := d4Word d4yWord

theorem eq_of_repE_of_eq {R S : Array ℕ} {a b : trialityGroup8} (hRS : R = S)
    (ha : RepE d4E R a) (hb : RepE d4E S b) : a = b :=
  eq_of_repE d4E_injective (hRS ▸ ha) hb


theorem d4Split :
    d4y * d4z = d4z * d4y ∧ d4GenG 0 * d4z = d4z * d4GenG 0 ∧
      Commute (d4GenG 0) (d4GenG 1) ∧ Commute (d4GenG 0) (d4GenG 2) ∧
      Commute (d4GenG 1) (d4GenG 2) ∧ d4y * d4GenG 0 * d4y⁻¹ = d4GenG 2 ∧
      d4y * d4GenG 2 * d4y⁻¹ = d4GenG 2 * d4GenG 1 ∧
      d4y * (d4GenG 2 * d4GenG 1) * d4y⁻¹ = d4GenG 2 * d4GenG 0 ∧ d4GenG 6 ∈ d4Q := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := parts_of_d4SplitCheck d4SplitCheck_eq_true
  have hy : RepE d4E (wordR d4Gens d4yWord) d4y := repE_d4Word (by decide)
  have hy' : RepE d4E (wordR d4Gens d4yInvWord) (d4Word d4yInvWord) := repE_d4Word (by decide)
  have hyinv : d4Word d4yInvWord = d4y⁻¹ := by
    have h := repE_mul hy hy'
    rw [h1] at h
    exact eq_inv_of_mul_eq_one_right (eq_of_repE d4E_injective h repE_one)
  rw [hyinv] at hy'
  have g0 := repE_d4Gens (k := 0) (by norm_num)
  have g1 := repE_d4Gens (k := 1) (by norm_num)
  have g2 := repE_d4Gens (k := 2) (by norm_num)
  have g6 := repE_d4Gens (k := 6) (by norm_num)
  refine ⟨eq_of_repE_of_eq h3 (repE_mul hy repE_z0R) (repE_mul repE_z0R hy),
    eq_of_repE_of_eq h2 (repE_mul g0 repE_z0R) (repE_mul repE_z0R g0),
    eq_of_repE_of_eq h4 (repE_mul g0 g1) (repE_mul g1 g0),
    eq_of_repE_of_eq h5 (repE_mul g0 g2) (repE_mul g2 g0),
    eq_of_repE_of_eq h6 (repE_mul g1 g2) (repE_mul g2 g1),
    eq_of_repE_of_eq h7 (repE_mul (repE_mul hy g0) hy') g2,
    eq_of_repE_of_eq h8 (repE_mul (repE_mul hy g2) hy') (repE_mul g2 g1),
    eq_of_repE_of_eq h9 (repE_mul (repE_mul hy (repE_mul g2 g1)) hy') (repE_mul g2 g0), ?_⟩
  have hq : RepE d4E (wordR qGens d4MidQWord) (d4MidQWord.map qGH).prod :=
    repE_wordR fun k hk => repE_qGens (by
      rw [qGens_size]
      simp only [d4MidQWord, List.mem_cons, List.not_mem_nil, or_false] at hk
      omega)
  rw [← eq_of_repE_of_eq h10 hq g6]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  refine subset_closure ⟨k, ?_, rfl⟩
  simp only [d4MidQWord, List.mem_cons, List.not_mem_nil, or_false] at hk
  show k < qGens.size
  rw [qGens_size]
  omega

end CFSG.LargeExtraspecial.S63
