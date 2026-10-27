module

public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived

public section

namespace CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K] [Finite K]

theorem spLinearAutGroup_normal_of_semilinear_top {r : ℕ} (hr : 1 ≤ r)
    (hgen : spSemilinearAutGroup r K = ⊤) : (spLinearAutGroup r K).Normal := by
  have hDn := (standard_outer_quotient (K := K) (r := r) hr).2.2.1
  refine ⟨fun d hd γ => ?_⟩
  have hγ : γ ∈ spSemilinearAutGroup r K := hgen ▸ Subgroup.mem_top γ
  have hd' : d ∈ spSemilinearAutGroup r K := hgen ▸ Subgroup.mem_top d
  exact Subgroup.mem_subgroupOf.mp
    (hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩)

theorem commutator_le_spLinearAutGroup_of_generator {r : ℕ}
    (hD : (spLinearAutGroup r K).Normal) {g : MulAut (StatedProj (StatedSp r K))}
    (hg : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ k : ℤ, g ^ k * α ∈ spLinearAutGroup r K) :
    commutator (MulAut (StatedProj (StatedSp r K))) ≤ spLinearAutGroup r K := by
  haveI := hD
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  exact CFSG.RankThree.PartOne.OutStructure.commutator_mem_of_cyclic_quotient g hg a b

theorem innAutDerived_statedSp_le_spLinearAutGroup {r : ℕ} (hr : 2 ≤ r)
    (hne : r = 2 → 2 < Nat.card K) :
    innAutDerived (StatedProj (StatedSp r K)) ≤ spLinearAutGroup r K := by
  haveI : NeZero r := ⟨by omega⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hID : inner (StatedProj (StatedSp r K)) ≤ spLinearAutGroup r K :=
    (standard_outer_quotient (K := K) (r := r) (by omega)).1
  rw [innAutDerived]
  refine sup_le hID ?_
  rcases eq_or_ne r 2 with rfl | hr2
  · by_cases htwo : (2 : K) = 0
    ·
      obtain ⟨m, hℓ, hcard⟩ := FiniteField.card (K := K) (ringChar K)
      have hchar : ringChar K = 2 := by
        refine (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (ringChar.dvd (R := K) htwo)
      haveI : CharP K 2 := ringChar.of_eq hchar
      rw [hchar] at hcard
      have hcard2 : Nat.card K = 2 ^ (m : ℕ) := by
        rw [Nat.card_eq_fintype_card]
        exact hcard
      obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
        finite_field_automorphism_fixed_field_cardinality Nat.prime_two m.pos hcard2
      obtain ⟨-, -, -, -, hcyc, -⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
          (K := K) m.pos hFr hord hzp
      haveI : IsCyclic (Outer (StatedProj (StatedSp 2 K))) := hcyc
      have hcomm : commutator (MulAut (StatedProj (StatedSp 2 K))) ≤
          inner (StatedProj (StatedSp 2 K)) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance
      exact hcomm.trans hID
    ·
      obtain ⟨hgen, -⟩ :=
        CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two (K := K) htwo
      have hD := spLinearAutGroup_normal_of_semilinear_top (K := K) (r := 2) (by omega) hgen
      obtain ⟨g, -, hgE⟩ := (standard_outer_quotient (K := K) (r := 2) (by omega)).2.2.2.2.1
      have hg : ∀ α : MulAut (StatedProj (StatedSp 2 K)),
          ∃ k : ℤ, g ^ k * α ∈ spLinearAutGroup 2 K :=
        fun α => hgE α (hgen ▸ Subgroup.mem_top α)
      exact commutator_le_spLinearAutGroup_of_generator hD hg
  ·
    have hr3 : 3 ≤ r := by omega
    obtain ⟨hgen, -⟩ := automorphism_generation (K := K) hr3
    have hD := spLinearAutGroup_normal_of_semilinear_top (K := K) (r := r) (by omega) hgen
    obtain ⟨g, -, hgE⟩ := (standard_outer_quotient (K := K) (r := r) (by omega)).2.2.2.2.1
    have hg : ∀ α : MulAut (StatedProj (StatedSp r K)),
        ∃ k : ℤ, g ^ k * α ∈ spLinearAutGroup r K :=
      fun α => hgE α (hgen ▸ Subgroup.mem_top α)
    exact commutator_le_spLinearAutGroup_of_generator hD hg

end CFSG.ComponentClassification.OuterAutomorphisms

end
