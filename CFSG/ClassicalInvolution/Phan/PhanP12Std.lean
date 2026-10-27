module

public import CFSG.ClassicalInvolution.Phan.PhanP11Edge

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalInvolution.Phan

section Bundle

variable {p e : ℕ} [Fact p.Prime]

structure StdModel (p e : ℕ) [Fact p.Prime] where
  ε : GaloisField p e
  hε : ε ≠ 0
  h4 : (4 : GaloisField p e) ≠ 0
  nonsq : ¬ IsSquare (-ε)
  S : PhanFamilyD4 (GaloisField p (2 * e)) p e (spinGroup (quadPlus 4 (GaloisField p e)))
  good : GoodFamily S
  fund : (S.ι 0).range ∈ fundamentalSubgroups .POmegaPlus
    (plusDatum 4 (GaloisField p e) (by norm_num))
  spec : ModelSpec S ε hε h4

theorem StdModel.card_K (hq : 5 ≤ p ^ e) : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  exact card_galoisField_two_mul p e he

theorem two_ne_zero_gf (hp2 : p ≠ 2) (k : ℕ) : (2 : GaloisField p k) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : GaloisField p k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (GaloisField p k) p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h')

variable (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)

include hp2 hq in
theorem StdModel.ptStep0 : PtStep0 M.S :=
  ptStep0_of_model (StdModel.card_K hq) M.good M.spec hq (two_ne_zero_gf hp2 e)
    (two_ne_zero_gf hp2 (2 * e))

include hp2 hq in
theorem StdModel.ptEdge : PtEdge M.S :=
  ptEdge_of_model (StdModel.card_K hq) M.good M.spec hq (two_ne_zero_gf hp2 e)
    (two_ne_zero_gf hp2 (2 * e)) M.nonsq

end Bundle

section Exists

variable {p e : ℕ} [Fact p.Prime]

theorem nonempty_stdModel (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) : Nonempty (StdModel p e) := by
  obtain ⟨ε, hε, h4, hεs, S, hg, hf, hS⟩ := exists_model_family hp2 hq
  exact ⟨⟨ε, hε, h4, hεs, S, hg, hf, hS⟩⟩

noncomputable def stdModel (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) : StdModel p e :=
  (nonempty_stdModel hp2 hq).some

end Exists

end CFSG.ClassicalInvolution.PhanP
