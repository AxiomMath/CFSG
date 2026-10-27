module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltModel

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Equiv

theorem altDg_mul_altDg {p : ℕ} [Fact p.Prime] (l m l' m' : (ZMod p)ˣ) :
    altDg l m * altDg l' m' = altDg (l * l') (m * m') := by
  refine Equiv.ext fun ⟨k, s⟩ => ?_
  fin_cases s <;> simp [altDg_apply, Perm.mul_apply, mul_assoc]

theorem altSwp_mul_altDg {p : ℕ} [Fact p.Prime] (l m : (ZMod p)ˣ) :
    (altSwp : Perm (ZMod p × Fin 2)) * altDg l m = altDg m l * altSwp := by
  refine Equiv.ext fun ⟨k, s⟩ => ?_
  fin_cases s <;> simp [altSwp, altDg_apply, Perm.mul_apply, prodCongrRight_apply]

theorem altSwp_mul_altSwp {p : ℕ} [Fact p.Prime] :
    (altSwp : Perm (ZMod p × Fin 2)) * altSwp = 1 := by
  refine Equiv.ext fun ⟨k, s⟩ => ?_
  fin_cases s <;> simp [altSwp, Perm.mul_apply, prodCongrRight_apply]

theorem altDg_one_one {p : ℕ} [Fact p.Prime] : altDg (1 : (ZMod p)ˣ) 1 = 1 := by
  refine Equiv.ext fun ⟨k, s⟩ => ?_
  fin_cases s <;> simp [altDg_apply]

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
