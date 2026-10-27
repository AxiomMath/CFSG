module

public import CFSG.LieType.ChevTwo.OppCl.Defs
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.BorelTits.OrthogonalModels
import CFSG.LieType.ChevTwo.OppCl.AutLiftsSp
import CFSG.LieType.ChevTwo.OppCl.AutLiftsOrth
import CFSG.LieType.ChevTwo.OppCl.AutLiftsUnitary

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section Induced

variable (F : Type) [Field F] [Finite F] [CharP F 2] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
include hp2

theorem induced_PSp (r : ℕ) (hr : 3 ≤ r)
    (R : Subgroup (MulAut (StatedProj (StatedSp r F)))) (hR : IsPGroup p R) :
    ∀ α ∈ R, ∃ s : Equiv.Perm (Fin r ⊕ Fin r → F), s ∈ semilinGroup F (Fin r ⊕ Fin r → F) ∧
      SemiIso (spForm r F) s ∧
      Induces (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) F).subgroupOf (StatedSp r F)))
        (natRep (StatedSp r F)) s α :=
  fun α _ => induced_PSp_aux hr α

theorem induced_PSp_two (hF : 4 ≤ Nat.card F)
    (R : Subgroup (MulAut (StatedProj (StatedSp 2 F)))) (hR : IsPGroup p R) :
    ∀ α ∈ R, ∃ s : Equiv.Perm (Fin 2 ⊕ Fin 2 → F), s ∈ semilinGroup F (Fin 2 ⊕ Fin 2 → F) ∧
      SemiIso (spForm 2 F) s ∧
      Induces (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)))
        (natRep (StatedSp 2 F)) s α := by
  intro α hα
  obtain ⟨k, hk⟩ := hR ⟨α, hα⟩
  exact induced_PSp_two_aux (((Fact.out : p.Prime).odd_of_ne_two hp2).pow) α
    (congrArg Subtype.val hk)

theorem induced_PSU (f : ℕ) (hK : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 3 ≤ n)
    (hq : 2 < 2 ^ f ∨ 4 ≤ n)
    (R : Subgroup (MulAut (StatedProj (StatedSU n (2 ^ f) F)))) (hR : IsPGroup p R) :
    ∀ α ∈ R, ∃ s : Equiv.Perm (Fin n → F), s ∈ semilinGroup F (Fin n → F) ∧
      SemiIso (unitaryForm 2 f hK n) s ∧
      Induces (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (2 ^ f) F)))
        (natRep (StatedSU n (2 ^ f) F)) s α :=
  fun α _ => induced_PSU_aux F f hK n hn hq α

theorem induced_POmegaPlus (n : ℕ) (hn : 5 ≤ n)
    (R : Subgroup (MulAut (StatedProj (StatedOmega (StatedQuadPlus n F))))) (hR : IsPGroup p R) :
    ∀ α ∈ R, ∃ s : Equiv.Perm (Fin n ⊕ Fin n → F), s ∈ semilinGroup F (Fin n ⊕ Fin n → F) ∧
      SemiIsoQ (quadPlusForm n F) s ∧
      Induces (QuotientGroup.mk'
        ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedOmega (StatedQuadPlus n F))))
        (natRep (StatedOmega (StatedQuadPlus n F))) s α :=
  fun α _ => induced_POmegaPlus_aux F n hn α

theorem induced_POmegaMinus (n : ℕ) (hn : 4 ≤ n) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (R : Subgroup (MulAut (StatedProj (StatedOmega (StatedQuadMinus n F b c)))))
    (hR : IsPGroup p R) :
    ∀ α ∈ R, ∃ s : Equiv.Perm (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
      s ∈ semilinGroup F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ∧
      SemiIsoQ (quadMinusForm n F b c hirr) s ∧
      Induces (QuotientGroup.mk'
        ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).subgroupOf
          (StatedOmega (StatedQuadMinus n F b c))))
        (natRep (StatedOmega (StatedQuadMinus n F b c))) s α :=
  fun α _ => induced_POmegaMinus_aux F n hn b c hirr α

end Induced

end CFSG.LieType.ChevTwo.OppCl
