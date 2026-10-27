module

public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SeitzGeneration.HyperPlaneCube
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP

variable {S : Type*} [Group S] [Finite S] {p : ℕ}

theorem le_seitzHyperGamma_of_closure_fixed (hp : p.Prime) {D E : Subgroup (MulAut S)}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) {x : MulAut S} (hxE : x ∈ E)
    (hxD : x ∉ D) {J : Subgroup S} (hJx : J ≤ fixedSubgroup x)
    (hJg : J ≤ Subgroup.closure {k | k ∈ J ∧ ∃ b ∈ E ⊓ D, b ≠ 1 ∧ b k = k}) :
    J ≤ seitzHyperGamma p E := by
  refine hJg.trans ((Subgroup.closure_le _).2 ?_)
  rintro k ⟨hk, b, hb, hb1, hbk⟩
  have hxb : x ∉ Subgroup.zpowers b := fun h => hxD (Subgroup.zpowers_le.2 hb.2 h)
  have hFE : Subgroup.closure ({b, x} : Set (MulAut S)) ≤ E :=
    (Subgroup.closure_le E).2 (Set.insert_subset_iff.2 ⟨hb.1, Set.singleton_subset_iff.2 hxE⟩)
  have hrel := relIndex_closure_pair_of_not_mem hp hE hEc hb.1 hxE hb1 hxb
  have hst : Subgroup.closure ({b, x} : Set (MulAut S)) ≤ MulAction.stabilizer (MulAut S) k := by
    rw [Subgroup.closure_le]
    refine Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩
    · exact MulAction.mem_stabilizer_iff.2 hbk
    · exact MulAction.mem_stabilizer_iff.2 (hJx hk)
  have hkF : k ∈ fixedPoints (Subgroup.closure ({b, x} : Set (MulAut S))) :=
    fun φ hφ => MulAction.mem_stabilizer_iff.1 (hst hφ)
  exact (le_iSup₂_of_le (f := fun (F : Subgroup (MulAut S)) (_ : F ≤ E ∧ F.relIndex E = p) =>
    fixedPoints F) _ ⟨hFE, hrel⟩ le_rfl) hkF

theorem seitzHyperGamma_eq_top_of_overgroups (hp : p.Prime) {D E : Subgroup (MulAut S)}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hED : ¬ E ≤ D) (hA : E ⊓ D ≠ ⊥)
    (hJ : ∀ x ∈ E, x ∉ D → ∃ J : Subgroup S, J ≤ fixedSubgroup x ∧
      J ≤ Subgroup.closure {k | k ∈ J ∧ ∃ b ∈ E ⊓ D, b ≠ 1 ∧ b k = k} ∧
      (∀ a ∈ E ⊓ D, (∀ k ∈ J, a k = k) → a = 1) ∧
      ∀ H : Subgroup S, J ≤ H → H ≤ fixedSubgroup x ∨ H = ⊤) :
    seitzHyperGamma p E = ⊤ := by
  obtain ⟨x, hxE, hxD⟩ : ∃ x ∈ E, x ∉ D := by
    by_contra h
    push Not at h
    exact hED fun y hy => h y hy
  obtain ⟨a, haED, ha1⟩ : ∃ a ∈ E ⊓ D, a ≠ 1 := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
    exact ⟨a, ha, fun h => ha1 (Subtype.ext h)⟩
  have hxaE : x * a ∈ E := E.mul_mem hxE haED.1
  have hxaD : x * a ∉ D := fun h => hxD (by simpa using D.mul_mem h (D.inv_mem haED.2))
  obtain ⟨J₁, hJ₁x, hJ₁g, -, hJ₁m⟩ := hJ x hxE hxD
  obtain ⟨J₂, hJ₂x, hJ₂g, hJ₂f, -⟩ := hJ (x * a) hxaE hxaD
  rcases hJ₁m _ (le_seitzHyperGamma_of_closure_fixed hp hE hEc hxE hxD hJ₁x hJ₁g) with hle | htop
  · refine absurd (hJ₂f a haED fun k hk => ?_) ha1
    have h1 : x k = k := hle (le_seitzHyperGamma_of_closure_fixed hp hE hEc hxaE hxaD hJ₂x hJ₂g hk)
    have h2 : x (a k) = k := hJ₂x hk
    exact x.injective (h2.trans h1.symm)
  · exact htop

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
