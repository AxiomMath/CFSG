module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Inner
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Lift
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicIso4
public import CFSG.GH74.Generic.BProg.B2.GenLocU3
public import CFSG.GH74.Generic.S1.UniClassify

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Subgroup Matrix

open GenLocU4Basic

namespace GenLocU4Fam

variable {K : Type} [Field K] [Finite K]

@[expose] def Su4OuterStmt (K : Type) [Field K] [Finite K] (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → Nat.card K = (p ^ f) ^ 2 → p ^ f % 4 = 1 →
    ∀ {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)), IsRank23 A →
      (∃ a : A, ¬ IsInnerDiagU4 (α a)) → SectionalTwoRankLE ↥(innJoin α) 4 → gammaAct α = ⊤

theorem su4Gen_of_classes {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) (hExt : GenLocU4Inner.Su4ExtStmt K p f)
    (hQuat : GenLocU4Inner.Su4QuatStmt K p f) (hOut : Su4OuterStmt K p f) : Su4GenStmt K (p ^ f) :=
  fun α hA hsect => by
    by_cases hin : ∀ c, IsInnerDiagU4 (α c)
    · exact GenLocU4Inner.gammaAct_su4_inner_of_classes hp hp2 hK hq hExt hQuat α hA hin
    · exact hOut hp hp2 hK hq α hA (not_forall.1 hin) hsect

theorem genLoc4_su4_of_classes {J : Type} [Group J] {q : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (hExt : ∀ p f : ℕ, GenLocU4Inner.Su4ExtStmt F p f)
    (hQuat : ∀ p f : ℕ, GenLocU4Inner.Su4QuatStmt F p f) (hOut : ∀ p f : ℕ, Su4OuterStmt F p f)
    (e : J ≃* ↥(StatedSU 4 q F)) : GenLoc4 J := by
  obtain ⟨p, f, hu, rfl, hp2⟩ := Generic.S1.exists_unitaryFieldData hF hq
  have hSU : Su4GenStmt F (p ^ f) := su4Gen_of_classes hu.prime hp2 hF hq (hExt p f) (hQuat p f) (hOut p f)
  exact GenLoc4.of_mulEquiv e.symm (fun _ _ _ α hA hsect => Or.inl (hSU α hA hsect))

theorem genLoc4_psu4_of_classes {J : Type} [Group J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ^ f % 4 = 1) (hJ : LieModel J .PSU 4 p f)
    (hExt : ∀ (F : Type) [Field F] [Finite F], GenLocU4Inner.Su4ExtStmt F p f)
    (hQuat : ∀ (F : Type) [Field F] [Finite F], GenLocU4Inner.Su4QuatStmt F p f)
    (hOut : ∀ (F : Type) [Field F] [Finite F], Su4OuterStmt F p f) : GenLoc4 J := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := GenLocU3.stated_PSU hJ
  exact GenLoc4.of_mulEquiv e₀.symm
    (genLoc4_projectiveSU4 hp hp2 hF (su4Gen_of_classes hp hp2 hF hq (hExt F) (hQuat F) (hOut F)))

end GenLocU4Fam

end CFSG.GH74.Generic.BProg.B2
