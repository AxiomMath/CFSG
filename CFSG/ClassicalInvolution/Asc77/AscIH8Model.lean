module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD
open scoped commutatorElement MatrixGroups

theorem ih8_isFundTag_mf {t : StatedLieTag} (h : Generic.IsFundTag t) : ModelFacts.IsFundTag t := by
  cases t <;> trivial

structure Ih8Model (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (t : StatedLieTag) (k e : ℕ) where
  isFundTag : Generic.IsFundTag t
  admissible : StatedLieAdmissible t k p e
  exp_eq : e = f ∨ (t = .trialityD4 ∧ 3 * e = f)
  ψ : (modelUniv t k p e Fact.out).K →* G
  ker_le_center : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K
  surj : Function.Surjective ψ
  cls : Set (Subgroup (modelUniv t k p e Fact.out).K)
  cls_sub : cls ⊆ fundamentalSubgroups t (modelUniv t k p e Fact.out).D
  mem_iff : ∀ L, L ∈ Ω ↔ ∃ R ∈ cls, L = R.map ψ
  cls_conj : ∀ R ∈ cls, ∀ g, conjSub g R ∈ cls

noncomputable def OmegaLie.toIh8Model {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} (D : OmegaLie p f Ω) (hcard : D.card = 1)
    (i : Fin D.card) (hconj : ConjInvariant Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, IsClassicalMember p f L z) (hne : Ω.Nonempty) :
    Ih8Model p f Ω (D.tag i) (D.rank i) (D.exp i) where
  isFundTag := D.isFundTag i
  admissible := D.admissible i
  exp_eq := D.exp_eq i
  ψ := D.hom i
  ker_le_center := D.ker_le_center i
  surj := D.hom_surjective_of_simple hconj hcl hne i
  cls := D.cls i
  cls_sub := fun _ hR => hR.1
  mem_iff := fun _ => D.mem_iff_exists_cls hcard i
  cls_conj := fun _ hR g => D.cls_conj hconj i hR g

namespace Ih8Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {t : StatedLieTag}
  {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem map_mem {R : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) :
    R.map M.ψ ∈ Ω :=
  (M.mem_iff _).mpr ⟨R, hR, rfl⟩

theorem cls_nonempty (hne : Ω.Nonempty) : M.cls.Nonempty := by
  obtain ⟨L, hL⟩ := hne
  obtain ⟨R, hR, -⟩ := (M.mem_iff L).mp hL
  exact ⟨R, hR⟩

theorem exp_eq_f (hD4 : t ≠ .trialityD4) : e = f := by
  rcases M.exp_eq with h | ⟨h, -⟩
  · exact h
  · exact absurd h hD4

theorem fund_subset_cls (hne : Ω.Nonempty) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    fundamentalSubgroups t (modelUniv t k p e Fact.out).D ⊆ M.cls := by
  obtain ⟨R₀, hR₀⟩ := M.cls_nonempty hne
  intro R hR
  obtain ⟨g, hg⟩ := ModelFacts.fundamentalSingleClass t k p e Fact.out
    (ih8_isFundTag_mf M.isFundTag) M.admissible hG2 hD4 R₀ (M.cls_sub hR₀) R hR
  rw [hg]
  exact M.cls_conj R₀ hR₀ g

theorem fund_eq_cls (hne : Ω.Nonempty) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    fundamentalSubgroups t (modelUniv t k p e Fact.out).D = M.cls :=
  Set.Subset.antisymm (M.fund_subset_cls hne hG2 hD4) M.cls_sub

theorem fund_perfect (hp2 : p ≠ 2) (hD4 : t ≠ .trialityD4) (hq : 5 ≤ p ^ f) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D, R ≤ ⁅R, R⁆ := by
  have h4 : 4 ≤ p ^ e := by rw [M.exp_eq_f hD4]; omega
  exact Gaps.fundPerfect_modelUniv hp2 M.isFundTag M.admissible h4

theorem cls_perfect (hp2 : p ≠ 2) (hD4 : t ≠ .trialityD4) (hq : 5 ≤ p ^ f)
    {R : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) : R ≤ ⁅R, R⁆ :=
  M.fund_perfect hp2 hD4 hq R (M.cls_sub hR)

theorem cls_equiv_sl2 (hp2 : p ≠ 2) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) :
    Nonempty (R ≃* SL(2, GaloisField p e)) :=
  ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2
    M.isFundTag M.admissible hG2 hD4 (M.cls_sub hR)

theorem natCard_galoisField_odd (hp2 : p ≠ 2) : Odd (Nat.card (GaloisField p e)) := by
  have he : e ≠ 0 := by have := M.admissible.2.1; omega
  rw [GaloisField.card p e he]
  exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow

theorem four_le_natCard_galoisField (hD4 : t ≠ .trialityD4) (hq : 5 ≤ p ^ f) :
    4 ≤ Nat.card (GaloisField p e) := by
  have he : e ≠ 0 := by have := M.admissible.2.1; omega
  rw [GaloisField.card p e he, M.exp_eq_f hD4]
  omega

variable [Finite G]

theorem oddCore_eq_bot (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) :
    oddCoreOf (R.map M.ψ) = ⊥ := by
  obtain ⟨e'⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  obtain ⟨z, hz⟩ := hΩ.classical _ (M.map_mem hR)
  exact ih8_oddCoreOf_map_eq_bot M.ψ (M.natCard_galoisField_odd hp2)
    (M.four_le_natCard_galoisField hD4 hq) e' ⟨z, hz.mem, hz.orderOf_eq_two⟩

end Ih8Model

end CFSG.ClassicalInvolution.Asc77
