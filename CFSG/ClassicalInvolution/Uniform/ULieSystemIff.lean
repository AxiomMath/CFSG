module

public import CFSG.ClassicalInvolution.Uniform.ULieSystem

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.LieType CFSG.LieType.Universal
open scoped MatrixGroups

section Cast

variable {X : Type} [Group X] {c c' : Q3.CompData}

def castHom (h : c = c') (φ : c.G →* X) : c'.G →* X := by
  subst h
  exact φ

theorem castHom_ker_le_center (h : c = c') (φ : c.G →* X) (hφ : φ.ker ≤ Subgroup.center c.G) :
    (castHom h φ).ker ≤ Subgroup.center c'.G := by
  subst h
  exact hφ

theorem exists_castHom_eq (h : c = c') (φ : c.G →* X) (x : c'.G) :
    ∃ y : c.G, castHom h φ x = φ y := by
  subst h
  exact ⟨x, rfl⟩

theorem range_castHom (h : c = c') (φ : c.G →* X) : (castHom h φ).range = φ.range := by
  subst h
  rfl

theorem exists_map_castHom (h : c = c') (φ : c.G →* X) {R : Subgroup c.G} (hR : R ∈ c.fund) :
    ∃ R' ∈ c'.fund, R'.map (castHom h φ) = R.map φ := by
  subst h
  exact ⟨R, hR, rfl⟩

end Cast

section Reindex

variable {p f : ℕ} [Fact p.Prime] {ι ι' : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

def LieSystemDataU.reindex (e : ι' ≃ ι) (D : LieSystemDataU p f ι X Φ) :
    LieSystemDataU p f ι' X Φ where
  kind j := D.kind (e j)
  valid j := D.valid (e j)
  hom j := D.hom (e j)
  ker_le_center j := D.ker_le_center (e j)
  commute i j hij x y := D.commute (e i) (e j) (e.injective.ne hij) x y
  generate := (Equiv.iSup_comp (g := fun i => (D.hom i).range) e).trans D.generate
  fundamental L hL := by
    have key : ∀ P : ι → Prop, (∃ i, P i) → ∃ j, P (e j) :=
      fun P ⟨i, hi⟩ => ⟨e.symm i, by rw [e.apply_symm_apply]; exact hi⟩
    exact key (fun i => ∃ R ∈ (D.kind i).fund, L = R.map (D.hom i)) (D.fundamental L hL)
  meets j := D.meets (e j)
  card_eq h := D.card_eq h

end Reindex

section Generic

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}

structure ModelSpec (p f : ℕ) [Fact p.Prime] (c : Q3.CompData) : Type where
  tag : CFSG.Assembly.LowTwoRank.StatedLieTag
  rank : ℕ
  exp : ℕ
  isFundTag : IsFundTag tag
  admissible : CFSG.Assembly.LowTwoRank.StatedLieAdmissible tag rank p exp
  exp_eq : exp = f ∨ (tag = .trialityD4 ∧ 3 * exp = f)
  eq : c = compModel p exp tag rank

theorem CompValid.nonempty_modelSpec (h3 : p ^ f ≠ 3) {c : Q3.CompData} (h : CompValid p f c) :
    Nonempty (ModelSpec p f c) := by
  rcases h with ⟨t, n, e, ht, hadm, he, hc⟩ | ⟨h3', -⟩
  · exact ⟨⟨t, n, e, ht, hadm, he, hc⟩⟩
  · exact absurd h3' h3

noncomputable def LieSystemDataU.toGeneric {n : ℕ} (h3 : p ^ f ≠ 3)
    (D : LieSystemDataU p f (Fin n) X Φ) : LieSystemData p f X Φ :=
  let σ : ∀ i, ModelSpec p f (D.kind i) := fun i => ((D.valid i).nonempty_modelSpec h3).some
  { card := n
    tag := fun i => (σ i).tag
    rank := fun i => (σ i).rank
    exp := fun i => (σ i).exp
    hom := fun i => castHom (σ i).eq (D.hom i)
    isFundTag := fun i => (σ i).isFundTag
    admissible := fun i => (σ i).admissible
    exp_eq := fun i => (σ i).exp_eq
    ker_le_center := fun i => castHom_ker_le_center _ _ (D.ker_le_center i)
    commute := fun i j hij x y => by
      obtain ⟨x', hx⟩ := exists_castHom_eq (σ i).eq (D.hom i) x
      obtain ⟨y', hy⟩ := exists_castHom_eq (σ j).eq (D.hom j) y
      rw [hx, hy]
      exact D.commute i j hij x' y'
    generate := by
      have h : ∀ i, (castHom (σ i).eq (D.hom i)).range = (D.hom i).range :=
        fun i => range_castHom _ _
      exact (iSup_congr h).trans D.generate
    fundamental := fun L hL => by
      obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
      obtain ⟨R', hR', hRR⟩ := exists_map_castHom (σ i).eq (D.hom i) hR
      exact ⟨i, R', hR', hLR.trans hRR.symm⟩
    meets := fun i => by
      obtain ⟨R, hR, hΦ⟩ := D.meets i
      obtain ⟨R', hR', hRR⟩ := exists_map_castHom (σ i).eq (D.hom i) hR
      exact ⟨R', hR', hRR ▸ hΦ⟩ }

theorem lieSystemU_iff_lieSystem (h3 : p ^ f ≠ 3) :
    LieSystemU p f X Φ ↔ LieSystem p f X Φ := by
  refine ⟨fun ⟨ι, hι, ⟨D⟩⟩ => ?_, lieSystemU_of_lieSystem h3⟩
  have := hι
  exact ⟨((D.reindex (Finite.equivFin ι).symm).toGeneric h3)⟩

end Generic

section Conclusion

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] {Λ : Set (Subgroup Y)}

theorem lieSystemModU_iff_lieSystemU :
    LieSystemModU (.sl2 p f) Λ ↔
      LieSystemU p f (Y ⧸ classicalInvolutionOddCore Y) (oddQuotientFamily Λ) := by
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_one_of_pow_eq_three Fact.out h3
    rw [lieSystemModU_sl2_of_eq_three h3]
    exact lieSystemU_three_iff.symm
  · rw [lieSystemModU_sl2_of_ne_three h3]
    exact (lieSystemU_iff_lieSystem h3).symm

end Conclusion

end CFSG.ClassicalInvolution.Uniform
