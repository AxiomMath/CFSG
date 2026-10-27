module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

theorem commutator_self_eq_of_commutator_top {G : Type*} [Group G] {A : Subgroup G}
    (h : commutator ↥A = ⊤) : ⁅A, A⁆ = A := by
  have h1 : ⁅A, A⁆ = Subgroup.map A.subtype ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h1, ← commutator_def, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

section Descent

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosure K L]

theorem langDescent_untw (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) (D : LangDatum τ L)
    (hΦ : D.Φ = Units.map (entrywiseHom Fr)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) :
    LangDescent D p ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype) := by
  classical
  have hfix : ∀ x, x ∈ D.fix ↔ x ∈ adjointGroup τ L ∧ Units.map (entrywiseHom Fr) x = x :=
    fun x => by rw [LangDatum.mem_fix, hΦ]
  set ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype with hι
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype]
  have hle : ι.range ≤ D.fix := by
    rw [hrange]
    rintro _ ⟨y, hy, rfl⟩
    exact (hfix _).2 ⟨baseChangeGL_mem_adjointGroup _ hy,
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr y⟩
  have hfin : Finite D.fix := by
    refine finite_of_entries_mem_range (K := K) D.fix fun g hg a b => ?_
    obtain ⟨-, hgF⟩ := (hfix _).1 hg
    have hcoord := congrArg (fun A : ModGL τ L =>
      (A : Module.End L (RootModule τ L)) (Finsupp.single b 1) a) hgF
    simp only [Units.coe_map] at hcoord
    change entrywise Fr _ (Finsupp.single b 1) a = _ at hcoord
    rw [entrywise_single, Finsupp.mapRange_apply, hFr] at hcoord
    exact mem_range_algebraMap_of_pow_card_eq hcoord
  have hrat := fun (P : Subgroup (ModGL τ L)) (hPX : P ≤ D.fix) (hP : IsPGroup p P) =>
    (finite_fixed_subgroup_rational d hτ Fr hFr D.fix (fun x hx => ((hfix x).1 hx).1)
      (fun x hx => ((hfix x).1 hx).2)).2 p hp hp3 P hPX hP
  have hidx := (finite_fixed_subgroup_rational d hτ Fr hFr D.fix (fun x hx => ((hfix x).1 hx).1)
      (fun x hx => ((hfix x).1 hx).2)).1
  have hperfI : ⁅ι.range, ι.range⁆ = ι.range := by
    rw [hrange, ← Subgroup.map_commutator, commutator_self_eq_of_commutator_top hperf]
  have hd3 : d ≤ 3 := by rcases hτ with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hd0 : 0 < d := by rcases hτ with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  refine ⟨hfin, hle, fun P hPX hP => hrange ▸ hrat P hPX hP, ?_⟩
  exact commutator_eq_of_perfect_of_relIndex_le_three hle hperfI
    (hrange ▸ (Nat.le_of_dvd hd0 hidx).trans hd3)

end Descent

end CFSG.HardMathSupport.Timmesfeld.LangTorus
