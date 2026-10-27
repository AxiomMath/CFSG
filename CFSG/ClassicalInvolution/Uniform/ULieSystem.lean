module

public import CFSG.ClassicalInvolution.Uniform.UInduction
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.LieType CFSG.LieType.Universal
open scoped MatrixGroups

@[expose, reducible] noncomputable def compModel (p : ℕ) [Fact p.Prime] (e : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Q3.CompData :=
  ⟨(modelUniv t n p e Fact.out).K, fundamentalSubgroups t (modelUniv t n p e Fact.out).D⟩

@[expose] def CompValid (p f : ℕ) [Fact p.Prime] (c : Q3.CompData) : Prop :=
  (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e ∧
      (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) ∧ c = compModel p e t n) ∨
    (p ^ f = 3 ∧ (c = Q3.CompData.sl23 ∨ c = Q3.CompData.m11))

structure LieSystemDataU (p f : ℕ) [Fact p.Prime] (ι : Type) (X : Type) [Group X]
    (Φ : Set (Subgroup X)) where
  kind : ι → Q3.CompData
  valid : ∀ i, CompValid p f (kind i)
  hom : ∀ i, (kind i).G →* X
  ker_le_center : ∀ i, (hom i).ker ≤ Subgroup.center _
  commute : ∀ i j, i ≠ j → ∀ x y, hom i x * hom j y = hom j y * hom i x
  generate : ⨆ i, (hom i).range = ⊤
  fundamental : ∀ L ∈ Φ, ∃ i, ∃ R ∈ (kind i).fund, L = R.map (hom i)
  meets : ∀ i, ∃ R ∈ (kind i).fund, R.map (hom i) ∈ Φ
  card_eq : p ^ f = 3 → ∀ L ∈ Φ, Nat.card L = 24

@[expose] def LieSystemU (p f : ℕ) [Fact p.Prime] (X : Type) [Group X]
    (Φ : Set (Subgroup X)) : Prop :=
  ∃ (ι : Type) (_ : Finite ι), Nonempty (LieSystemDataU p f ι X Φ)

section Facades

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

def LieSystemDataU.ofQ3 (D : Q3.LieSystemData3 ι X Φ) : LieSystemDataU 3 1 ι X Φ where
  kind := D.kind
  valid i := by
    rcases D.valid i with ⟨t, n, ht, hadm, hc⟩ | hc | hc
    · exact Or.inl ⟨t, n, 1, ht, hadm, Or.inl rfl, hc⟩
    · exact Or.inr ⟨by norm_num, Or.inl hc⟩
    · exact Or.inr ⟨by norm_num, Or.inr hc⟩
  hom := D.hom
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate
  fundamental := D.fundamental
  meets := D.meets
  card_eq _ := D.card_eq

def LieSystemDataU.toQ3 (D : LieSystemDataU 3 1 ι X Φ) :
    Q3.LieSystemData3 ι X Φ where
  kind := D.kind
  valid i := by
    rcases D.valid i with ⟨t, n, e, ht, hadm, he, hc⟩ | ⟨-, hc | hc⟩
    · have he1 : e = 1 := by
        rcases he with he | ⟨-, he⟩
        · exact he
        · omega
      subst he1
      exact Or.inl ⟨t, n, ht, hadm, hc⟩
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)
  hom := D.hom
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate
  fundamental := D.fundamental
  meets := D.meets
  card_eq := D.card_eq rfl

theorem lieSystemU_three_iff :
    LieSystemU 3 1 X Φ ↔ Q3.LieSystem3 X Φ := by
  refine ⟨fun ⟨ι, hι, ⟨D⟩⟩ => ⟨ι, hι, ⟨D.toQ3⟩⟩, fun ⟨ι, hι, ⟨D⟩⟩ => ⟨ι, hι, ⟨.ofQ3 D⟩⟩⟩

variable {p f : ℕ} [Fact p.Prime]

noncomputable def LieSystemDataU.ofGeneric (h3 : p ^ f ≠ 3) (D : LieSystemData p f X Φ) :
    LieSystemDataU p f (Fin D.card) X Φ where
  kind i := compModel p (D.exp i) (D.tag i) (D.rank i)
  valid i := Or.inl ⟨D.tag i, D.rank i, D.exp i, D.isFundTag i, D.admissible i, D.exp_eq i, rfl⟩
  hom := D.hom
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate
  fundamental := D.fundamental
  meets := D.meets
  card_eq h := absurd h h3

theorem lieSystemU_of_lieSystem (h3 : p ^ f ≠ 3) (h : LieSystem p f X Φ) : LieSystemU p f X Φ := by
  obtain ⟨D⟩ := h
  exact ⟨Fin D.card, inferInstance, ⟨.ofGeneric h3 D⟩⟩

end Facades

section Conclusion

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] {Λ : Set (Subgroup Y)}

theorem LieSystemModU.toLieSystemU (h : LieSystemModU (.sl2 p f) Λ) :
    LieSystemU p f (Y ⧸ classicalInvolutionOddCore Y) (oddQuotientFamily Λ) := by
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_one_of_pow_eq_three Fact.out h3
    exact lieSystemU_three_iff.mpr ((lieSystemModU_sl2_of_eq_three h3).mp h)
  · exact lieSystemU_of_lieSystem h3 ((lieSystemModU_sl2_of_ne_three h3).mp h)

end Conclusion

end CFSG.ClassicalInvolution.Uniform
