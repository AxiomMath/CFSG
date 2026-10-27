module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem l2_not_sylow_of_extra {S : Type} [Group S] [Finite S] {A : Subgroup S} {g : S}
    (hgc : ∀ a ∈ A, a * g = g * a) (hgA : g ∉ A) (hg2 : g * g = 1) :
    ¬ IsSylowIn 2 (centIn ⊤ A) A := by
  rintro ⟨hle, -, hrel⟩
  set C : Subgroup S := centIn ⊤ A with hC
  have hleC : A ≤ C := by rw [hC]; exact hle
  have hcommC : ∀ c ∈ C, ∀ a ∈ A, a * c = c * a := by
    intro c hc a ha
    have hc' : c ∈ centralizer (A : Set S) := by
      rw [hC, centIn, Subgroup.mem_inf] at hc
      exact hc.2
    exact (Subgroup.mem_centralizer_iff.mp hc') a ha
  have hgC : g ∈ C := by
    rw [hC, centIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact ⟨trivial, hgc⟩
  let g' : ↥C := ⟨g, hgC⟩
  have hnorm : (A.subgroupOf C).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnc : (n : S) * (c : S) = (c : S) * (n : S) := hcommC c c.2 n hn
    have heq : (↑(c * n * c⁻¹) : S) = (n : S) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hnc, mul_assoc, mul_inv_cancel, mul_one]
    rw [heq]
    exact hn
  haveI : (A.subgroupOf C).Normal := hnorm
  have hq1 : (g' : ↥C ⧸ A.subgroupOf C) ≠ 1 := by
    intro h
    exact hgA (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff g').mp h))
  have hg'2 : g' * g' = 1 := by
    apply Subtype.ext
    change (g : S) * g = 1
    exact hg2
  have hq2 : (g' : ↥C ⧸ A.subgroupOf C) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, hg'2, QuotientGroup.mk_one]
  have horder : orderOf (g' : ↥C ⧸ A.subgroupOf C) = 2 :=
    orderOf_eq_prime hq2 hq1
  have hdvd : 2 ∣ Nat.card (↥C ⧸ A.subgroupOf C) := by
    rw [← horder]
    exact orderOf_dvd_natCard _
  have hrelC : 2 ∣ A.relIndex C := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact hdvd
  exact hrel (hC ▸ hrelC)

end CFSG.OddStandard.HigherRank.YamadaG23
