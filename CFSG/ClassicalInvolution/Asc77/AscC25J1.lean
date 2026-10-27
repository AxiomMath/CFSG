module

public import CFSG.ClassicalInvolution.Asc77.AscR10T9b
public import CFSG.ClassicalInvolution.Uniform.ULieType
public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25I8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Defs

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Typed9 : Prop :=
  p ^ f = 9 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ t' : G),
    T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → ∀ a : G, a ∈ (S : Subgroup G) →
      a * a = 1 → IsFAut R' a → a * t' = t' * a →
      ∃ (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
        (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
        (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ conjGen (crossIn K' a))
        (a₀ b₀ : ↥(conjGen (crossIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (crossIn K' a))),
        TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
            (conjGen (crossIn K' a))))
          (secImg (conjGen (crossIn K' a)) (crossIn K' a))
          (secImg (conjGen (crossIn K' a)) (conjSub (⟨t', ht'a⟩ :
            ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K' a)))
          (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀ ∧
        (z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) ∨
          SectionOrthTypeU p (f / 2) (conjFamily (crossIn K' a)) (conjGen (crossIn K' a)) 5 true ∨
          SectionOrthTypeU p (f / 2) (conjFamily (crossIn K' a)) (conjGen (crossIn K' a)) 6
            (!piSign p (f / 2)))


end Defs

section Cross

variable {G : Type} [Group G] [Finite G]


theorem conjSub_crossIn_eq {K : Subgroup G} {a c : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G)) (hcK : c ∈ Subgroup.normalizer (K : Set G)) :
    conjSub (⟨c, hc⟩ : ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K a) = crossIn K a := by
  apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
  rw [map_conjSub_crossIn (K := K) (a := a) ⟨c, hc⟩]
  change conjSub c (K ⊓ Subgroup.centralizer ({a} : Set G)) = _
  rw [conjSub_inf_centralizer hc, conjSub_eq_of_mem_normalizer hcK]
  rw [Subgroup.subgroupOf_map_subtype]
  exact (inf_comm _ _).symm.trans (by rw [inf_eq_left.mpr inf_le_right]; exact inf_comm _ _)


end Cross

section Arith

theorem eq_three_two_of_pow_eq_nine {p f : ℕ} (hp : p.Prime) (h : p ^ f = 9) :
    p = 3 ∧ f = 2 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h
  have h3 : p ∣ 3 ^ 2 := by
    have : p ∣ p ^ f := dvd_pow_self p hf
    rw [h] at this
    simpa using this
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ f = 3 ^ 2 by rw [h])⟩


end Arith

end CFSG.ClassicalInvolution.Asc77.C25J
