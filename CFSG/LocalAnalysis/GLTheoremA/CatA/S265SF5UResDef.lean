module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGPin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormP)

@[expose] def QSFamF5URes : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 5 S B T x D K → catalogIs (PSimple 5 K) (tyFUni 5) → Subgroup.center ↥K = ⊥ →
      (∀ (m : ℕ) (F : Type) [Field F] (hF : UnitaryFieldData 2 m F),
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
          primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) →
        ¬ 25 ∣ 2 ^ m + 1) →
      QSConcl 5 S B D K

@[expose] def QSF5UCls : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL 5 S B T x D K → catalogIs (PSimple 5 K) (tyFUni 5) → Subgroup.center ↥K = ⊥ →
      (∀ (m : ℕ) (F : Type) [Field F] (hF : UnitaryFieldData 2 m F),
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
          primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) →
        ¬ 25 ∣ 2 ^ m + 1) →
      ∀ lab : GLALabel, InnLabelOf B S lab → GLAInLambda2 lab →
        3 ≤ rk2Mult lab (rk2Ord 5 lab.n) →
        (lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨
          lab.tag = .twD) → False

@[expose] def E8FiveMaxRank : Prop :=
  ∀ (F : Type) [Field F] [Finite F], 5 ∣ Nat.card F * Nat.card F + 1 →
    ∀ E : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .E8 F), IsElemAbelian 5 E →
      Nat.card E = 5 ^ 3 →
      ∃ E' : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .E8 F), E ≤ E' ∧
        IsElemAbelian 5 E' ∧ Nat.card E' = 5 ^ 4

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
