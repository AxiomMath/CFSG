module

public import CFSG.Assembly.Defs
public import CFSG.Open.FusionDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.LocalAnalysis.ABGTheoremB.Basic

public section

namespace CFSG.Foundations.SteinbergCA

open scoped commutatorElement

theorem sSup_eq_closure_biUnion {G : Type*} [Group G] (s : Set (Subgroup G)) :
    sSup s = Subgroup.closure (⋃ L ∈ s, (L : Set G)) := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    exact fun x hx => Subgroup.subset_closure (Set.mem_biUnion hL hx)
  · rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨L, hL, hxL⟩ := Set.mem_iUnion₂.mp hx
    exact le_sSup hL hxL

theorem quasisimple_iff (Q : Type*) [Group Q] :
    (CFSG.IsQuasisimple Q ↔ Group.IsPerfect Q ∧ IsSimpleGroup (Q ⧸ Subgroup.center Q) ∧
      ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a) ∧
    (CFSG.IsQuasisimple Q ↔ CFSG.Assembly.IsQuasisimple Q) ∧
    (CFSG.IsQuasisimple Q ↔ CFSG.Open.IsQuasisimple Q) ∧
    (CFSG.IsQuasisimple Q ↔ CFSG.GorensteinWalter.IsQuasisimple Q) := by
  have hasm : CFSG.IsQuasisimple Q ↔ CFSG.Assembly.IsQuasisimple Q := by
    constructor
    · rintro ⟨hperf, hsimple, -⟩
      exact ⟨Group.isPerfect_def.mp hperf, hsimple⟩
    · rintro ⟨hcomm, hsimple⟩
      refine ⟨Group.isPerfect_def.mpr hcomm, hsimple, ?_⟩
      by_contra hab
      push Not at hab
      have hle : commutator Q ≤ Subgroup.center Q := by
        rw [commutator_def, Subgroup.commutator_le]
        intro x _ y _
        rw [← QuotientGroup.eq_one_iff]
        change (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1
        rw [map_commutatorElement, commutatorElement_def,
          hab ((QuotientGroup.mk' (Subgroup.center Q)) x), mul_inv_cancel_right,
          mul_inv_cancel]
      rw [hcomm] at hle
      obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))
  refine ⟨Iff.rfl, hasm, hasm, hasm.trans ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩⟩
  obtain ⟨-, hsimple⟩ := h
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨x, y, fun hxy => hne (by rw [hxy])⟩

theorem pLocal_iff {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) :
    (CFSG.IsPLocal p H ↔
      ∃ P : Subgroup G, P ≠ ⊥ ∧ IsPGroup p P ∧ H = Subgroup.normalizer (P : Set G)) ∧
    (CFSG.IsPLocal p H ↔ CFSG.ABGTheoremB.IsPLocal p H) ∧
    (CFSG.IsPLocal 2 H ↔ CFSG.Assembly.IsTwoLocal H) ∧
    (CFSG.IsPLocal 2 H ↔ CFSG.Open.IsTwoLocal H) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem pLayer_eq_closure (X : Type*) [Group X] (p : ℕ) :
    CFSG.pLayer X p =
        Subgroup.closure (⋃ L ∈ {L : Subgroup X | CFSG.IsPComponent p L}, (L : Set X)) ∧
      ((∀ L : Subgroup X, ¬ CFSG.IsPComponent p L) → CFSG.pLayer X p = ⊥) := by
  refine ⟨sSup_eq_closure_biUnion _, fun h => ?_⟩
  have hempty : {L : Subgroup X | CFSG.IsPComponent p L} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr h
  change sSup {L : Subgroup X | CFSG.IsPComponent p L} = ⊥
  rw [hempty, sSup_empty]

theorem stronglyClosedIn_iff {G : Type*} [Group G] (S : Subgroup G) {A : Set G}
    (hAS : A ⊆ S) :
    (CFSG.IsStronglyClosedIn S A ↔ ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ A) ∧
    (CFSG.IsStronglyClosedIn S A ↔
      ∀ g : G, (fun a => g⁻¹ * a * g) '' A ∩ (S : Set G) ⊆ A) ∧
    (CFSG.IsStronglyClosedIn S A ↔ CFSG.Open.fusionStronglyClosed A S) := by
  have h1 : CFSG.IsStronglyClosedIn S A ↔
      ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ A :=
    ⟨fun h => h.2, fun h => ⟨hAS, h⟩⟩
  refine ⟨h1, h1.trans ⟨fun h g => ?_, fun h a ha g hg => ?_⟩, h1⟩
  · rintro _ ⟨⟨a, ha, rfl⟩, hS⟩
    exact h a ha g hS
  · exact h g ⟨⟨a, ha, rfl⟩, hg⟩

theorem solvableRadical_eq_closure (G : Type*) [Group G] :
    CFSG.solvableRadical G = Subgroup.closure
      (⋃ N ∈ {N : Subgroup G | N.Normal ∧ Group.IsSolvable N}, (N : Set G)) :=
  sSup_eq_closure_biUnion _

theorem omega₁_eq_closure (H : Type*) [Group H] (p : ℕ) :
    CFSG.omega₁ H (p := p) = Subgroup.closure {x : H | x ^ p = 1} ∧
      ∀ x : H, x ^ p = 1 ↔ orderOf x ∣ p := by
  refine ⟨?_, fun x => orderOf_dvd_iff_pow_eq_one.symm⟩
  simp only [CFSG.omega₁, CFSG.omega, pow_one]

theorem omega₁_eq_sInf (P : Type*) [Group P] (p : ℕ) :
    CFSG.omega₁ P (p := p) = Subgroup.closure {x : P | x ^ p = 1} ∧
      CFSG.omega₁ P (p := p) = sInf {K : Subgroup P | {x : P | x ^ p = 1} ⊆ K} ∧
      (Subsingleton P → CFSG.omega₁ P (p := p) = ⊥) := by
  have h1 := (omega₁_eq_closure P p).1
  refine ⟨h1, ?_, fun _ => Subsingleton.elim _ _⟩
  rw [h1]
  apply le_antisymm
  · exact le_sInf fun K hK => (Subgroup.closure_le K).mpr hK
  · exact sInf_le Subgroup.subset_closure

end CFSG.Foundations.SteinbergCA
