module

public import CFSG.ClassicalInvolution.Phan.PhanH1Good
public import CFSG.ClassicalInvolution.Phan.PhanH7Model
public import CFSG.ClassicalInvolution.Phan.PhanH8Gen
public import CFSG.ClassicalInvolution.Phan.PhanB12Geometry
import CFSG.ClassicalInvolution.Phan.PhanB21Exists
import CFSG.ClassicalInvolution.Asc77.AscB3CG

public section

namespace CFSG.ClassicalInvolution.PhanB3.H

open CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort twShort_sup_longBlock)
open scoped MatrixGroups

section Connected

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G]

theorem phanSystem_connected_of_sup (S : PhanFamilyB3 C G)
    (h : (S.ι 0).range ⊔ (S.ι 1).range ⊔ (S.ι 2).range = ⊤) : (phanSystem S).Connected := by
  have hle : ∀ j, (S.ι j).range ≤ parab S Set.univ := by
    rintro j _ ⟨A, rfl⟩
    exact Lsup_le_parab Set.univ (ι_mem_Lsup (Set.mem_univ j) A)
  have hg : parab S Set.univ = ⊤ :=
    eq_top_iff.mpr (by rw [← h]; exact sup_le (sup_le (hle 0) (hle 1)) (hle 2))
  intro x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : (a⁻¹ * b : G) ∈ parab S Set.univ := by rw [hg]; trivial
  rw [mem_parab_iff] at h1
  have h3 : a • ((a⁻¹ * b : G) : G ⧸ torusSub S) ∈
      (phanSystem S).residue Set.univ (a • ((1 : G) : G ⧸ torusSub S)) :=
    (phanSystem_isMorphism_smul (S := S) a).mapsTo_residue Set.univ ((1 : G) : G ⧸ torusSub S) h1
  rw [smul_mk, smul_mk, mul_one, mul_inv_cancel_left] at h3
  obtain ⟨γ, hγ, -, hend⟩ := h3
  exact ⟨γ, hγ, hend⟩

end Connected

section Model

variable {p f : ℕ} [Fact p.Prime] {h2 : (2 : GaloisField p f) ≠ 0}

theorem ModelB3.weak (M : ModelB3 p f h2) :
    WeakPhanB3 (GaloisField p (2 * f)) p f h2 M.U where
  comm := M.comm
  unitary := M.unitary
  symplectic := ⟨M.D.θ, M.D.θ_inj, rfl, rfl⟩
  disj := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact M.disj01
      | exact M.disj02
      | exact M.disj12
      | (rw [inf_comm]; exact M.disj01)
      | (rw [inf_comm]; exact M.disj02)
      | (rw [inf_comm]; exact M.disj12)

theorem ModelB3.sup_eq_top (M : ModelB3 p f h2) (hn1 : ¬ IsSquare (-1 : GaloisField p f)) :
    M.U 0 ⊔ M.U 1 ⊔ M.U 2 = ⊤ := by
  have h := sup_theta_eq_top M.D hn1 M.map_eq
  have hY : (longBlock (GaloisField p f) 2 1).range ⊔ (twShort h2).range = ⊤ := by
    rw [sup_comm]
    exact twShort_sup_longBlock h2
  have hY' : (longBlock (GaloisField p f) 2 1).range.map M.D.θ ⊔
      (twShort h2).range.map M.D.θ = M.D.θ.range := by
    rw [← Subgroup.map_sup, hY, ← MonoidHom.range_eq_map]
  show M.R₀ ⊔ (longBlock (GaloisField p f) 2 1).range.map M.D.θ ⊔
    (twShort h2).range.map M.D.θ = ⊤
  rw [sup_assoc, hY']
  exact h

theorem ModelB3.exists_family (M : ModelB3 p f h2)
    {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2}
    (C : B2Coord hK (GaloisField p f) h2) (hq : 5 ≤ p ^ f) (hmod : p ^ f % 4 = 3) :
    ∃ E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f))),
      GoodFamily E ∧ (∀ i, (E.ι i).range = M.U i) :=
  WeakPhanB3.exists_good C hq hmod M.weak

theorem ModelB3.connected (M : ModelB3 p f h2) {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2}
    {C : B2Coord hK (GaloisField p f) h2}
    (E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f))))
    (hE : ∀ i, (E.ι i).range = M.U i) (hn1 : ¬ IsSquare (-1 : GaloisField p f)) :
    (phanSystem E).Connected :=
  phanSystem_connected_of_sup E (by rw [hE 0, hE 1, hE 2]; exact M.sup_eq_top hn1)

@[expose] def PhanB3StdSimplyTwoConnected (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → p ^ f % 4 = 3 →
    ∀ (hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2) (h2 : (2 : GaloisField p f) ≠ 0)
      (C : B2Coord hK (GaloisField p f) h2) (M : ModelB3 p f h2)
      (E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))),
      GoodFamily E → (∀ i, (E.ι i).range = M.U i) → (phanSystem E).SimplyTwoConnected

theorem exists_good_connected_familyB3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hmod : p ^ f % 4 = 3)
    (hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2) (h2 : (2 : GaloisField p f) ≠ 0) :
    ∃ (C : B2Coord hK (GaloisField p f) h2)
      (S : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))),
      GoodFamily S ∧ (S.ι 0).range ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups
        .POmegaOdd (oddDatum 3 (GaloisField p f)) ∧ (phanSystem S).Connected := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨M⟩ := exists_modelB3 hp2 hq hmod h2
  obtain ⟨C⟩ := b2Coord_exists p f hmod hK h2 hf
  obtain ⟨E, hgood, hrange⟩ := M.exists_family C hq hmod
  refine ⟨C, E, hgood, ?_, M.connected E hrange (not_isSquare_neg_one hmod)⟩
  rw [hrange 0]
  exact longestFundamental_subset .POmegaOdd _ M.mem_longest

theorem phanB3Geometry_of_simplyTwoConnected (hsc : PhanB3StdSimplyTwoConnected p f) :
    PhanB3Geometry p f := by
  intro hp2 hq hmod hK h2
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨M⟩ := exists_modelB3 hp2 hq hmod h2
  obtain ⟨C⟩ := b2Coord_exists p f hmod hK h2 hf
  obtain ⟨E, hgood, hrange⟩ := M.exists_family C hq hmod
  refine ⟨C, E, hgood, ?_, M.connected E hrange (not_isSquare_neg_one hmod),
    hsc hp2 hq hmod hK h2 C M E hgood hrange⟩
  rw [hrange 0]
  exact longestFundamental_subset .POmegaOdd _ M.mem_longest

end Model

end CFSG.ClassicalInvolution.PhanB3.H
