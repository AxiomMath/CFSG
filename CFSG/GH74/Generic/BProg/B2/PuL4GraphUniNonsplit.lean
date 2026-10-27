module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace PuL4GraphUniNonsplit

section Certified


theorem false_of_uni_nonsplit {N : Type} [Group N] [Finite N] {H L : Subgroup N} {t : N}
    (hs : ShapeInCent H t L) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : 3 < p ^ f) {E' : Type} [Field E'] [Finite E'] (hE' : Nat.card E' = (p ^ f) ^ 2)
    {X : Type} [Group X] (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) E')
    (eLX : ↥L ≃* X) : False := by
  have hE2 : Nat.card E' = p ^ (2 * f) := by rw [hE', ← pow_mul, mul_comm]
  have h4 : 4 ≤ p ^ (2 * f) := by
    rw [mul_comm, pow_mul]
    exact le_trans hq (Nat.le_self_pow (by norm_num) _)
  exact PumpupTableOmega3.false_of_psl2_component hs hp hp2
    (PumpupTableOmega3.lieModel_psl2_of_equiv hp (by omega) h4 hE2 (eLX.trans e))

end Certified

end PuL4GraphUniNonsplit

end CFSG.GH74.Generic.BProg.B2
