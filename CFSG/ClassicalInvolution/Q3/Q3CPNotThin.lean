module

public import CFSG.ClassicalInvolution.Q3.Q3CPNbhdAll

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {G : Type} [Group G] [Finite G]


theorem not_thin_of_mem {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (he : IsEdge3 Ω K₁ K₂ z₁ z₂) (hzX : z₁ ∈ nbrSpan3 Ω K₁) :
    ¬ nbrSpan3 Ω K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 Ω K₁) := by
  intro hthin
  have hK₁ : IsClassicalMember3 K₁ z₁ := he.cls₁
  have hK₂ : IsClassicalMember3 K₂ z₂ := he.cls₂
  have hz1sq : z₁ * z₁ = 1 := hK₁.isCentralInvolution.sq
  have hz2sq : z₂ * z₂ = 1 := hK₂.isCentralInvolution.sq
  have hK₂nbr : K₂ ∈ nbrs3 Ω K₁ := by
    refine ⟨he.mem₂, fun h => he.ne ?_, he.comm⟩
    rw [h] at hK₂
    exact involution_unique3 hK₁ hK₂
  have hK₂X : K₂ ≤ nbrSpan3 Ω K₁ := le_nbrSpan3 hK₂nbr
  have hz₂X : z₂ ∈ nbrSpan3 Ω K₁ := hK₂X hK₂.mem
  set ρ := QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrSpan3 Ω K₁)) with hρ
  have htop : modOddIn (nbrSpan3 Ω K₁) K₂ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hx : (x : G) ∈ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 Ω K₁) := hthin x.2
    have hK₂P : K₂ ≤ ((modOddIn (nbrSpan3 Ω K₁) K₂).comap ρ).map (nbrSpan3 Ω K₁).subtype :=
      fun k hk => ⟨⟨k, hK₂X hk⟩, ⟨⟨k, hK₂X hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩
    have hOP : Balance.oddCoreIn (nbrSpan3 Ω K₁) ≤
        ((modOddIn (nbrSpan3 Ω K₁) K₂).comap ρ).map (nbrSpan3 Ω K₁).subtype := by
      rintro _ ⟨n, hn, rfl⟩
      refine ⟨n, ?_, rfl⟩
      show ρ n ∈ modOddIn (nbrSpan3 Ω K₁) K₂
      have hρn : ρ n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [hρn]
      exact Subgroup.one_mem _
    obtain ⟨x', hx', hxx'⟩ := sup_le hK₂P hOP hx
    have hx'x : x' = x := Subtype.ext hxx'
    rw [← hx'x]
    exact hx'
  have hKcl : IsClassicalMember3 (modOddIn (nbrSpan3 Ω K₁) K₂) (ρ ⟨z₂, hz₂X⟩) :=
    (hK₂.subgroupOf hK₂X).map_oddQuotient
  have hz1ne : ρ ⟨z₁, hzX⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution _ hzX hz1sq hK₁.ne_one
  have hz1sqX : ρ ⟨z₁, hzX⟩ * ρ ⟨z₁, hzX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z₁, hzX⟩ : ↥(nbrSpan3 Ω K₁)) * ⟨z₁, hzX⟩ = 1 := Subtype.ext hz1sq
    rw [this, map_one]
  have hcen : ∀ x : ↥(nbrSpan3 Ω K₁) ⧸ classicalInvolutionOddCore ↥(nbrSpan3 Ω K₁),
      x * ρ ⟨z₁, hzX⟩ = ρ ⟨z₁, hzX⟩ * x := by
    intro x
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (nbrSpan3_le_centralizer Ω K₁ x'.2) z₁
      hK₁.mem).symm
  have hcz : Subgroup.centralizer ({ρ ⟨z₁, hzX⟩} : Set
      (↥(nbrSpan3 Ω K₁) ⧸ classicalInvolutionOddCore ↥(nbrSpan3 Ω K₁))) = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (hcen x)
  have hKz : IsClassicalMember3 (modOddIn (nbrSpan3 Ω K₁) K₂) (ρ ⟨z₁, hzX⟩) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨orderOf_eq_prime (by rw [pow_two]; exact hz1sqX) hz1ne, ?_, ?_, hKcl.nonempty_equiv⟩
    · rw [htop]
      exact Subgroup.mem_top _
    · rw [htop, hcz]
      exact IsSubnormal.refl _
  have h12 : ρ ⟨z₁, hzX⟩ = ρ ⟨z₂, hz₂X⟩ := involution_unique3 hKz hKcl
  exact Q3Y.mk_involutions_ne hzX hz₂X hz1sq hz2sq he.comm_involutions he.ne h12

theorem typeC3NbhdNotThin_of_noThin (h : Q3Y.TypeC3NoThin) : TypeC3NbhdNotThin := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  exact not_thin_of_mem he (h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he)

end CFSG.ClassicalInvolution.Q3.Q3CP
