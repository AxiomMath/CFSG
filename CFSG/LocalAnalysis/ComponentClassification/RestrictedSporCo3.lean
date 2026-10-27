module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
public import CFSG.Sporadic.SmallOddCore.Co3Local

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.SmallOddCore

@[expose] def co3Orders : Set ℕ := {1451520, 95040}

theorem co3M_comps : CompsSatisfy co3M fun Y _ => Nat.card (Y ⧸ center Y) ∈ co3Orders := by
  refine compsSatisfy_of_isQuasisimple co3M_isQuasisimple (isoInvariant_card_quotient_center _) ?_
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center co3M)
  rw [card_co3M, card_co3M_center] at h
  left
  omega

theorem co3M1_comps : CompsSatisfy co3M1 fun Y _ => Nat.card (Y ⧸ center Y) ∈ co3Orders := by
  intro B hB
  have eL : co3L1 ≃* NativeSporadic.M12 :=
    (Subgroup.subgroupOfEquivOfLe co3L_le_M1).trans co3LEquivM12
  have : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hs : IsSimpleGroup co3L1 := eL.isSimpleGroup
  have : co3L1.Normal := co3L1_normal
  have hsolv : Group.IsSolvable (centralizer (co3L1 : Set co3M1)) := by
    rw [co3M1_centralizer_L1]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 co3Z1 := IsPGroup.of_card (n := 1) (by rw [card_co3Z1, pow_one])
    have : Group.IsNilpotent co3Z1 := hp.isNilpotent
    infer_instance
  obtain rfl := eq_of_isComponent_of_simple_normal hs hsolv hB
  right
  show Nat.card (↥co3L1 ⧸ center ↥co3L1) = 95040
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center co3L1)
  rw [co3L1_center, Subgroup.card_bot, mul_one, Nat.card_congr eL.toEquiv, m12_card] at h
  rw [co3L1_center]
  exact h.symm

theorem co3_centralizerIn_comps : ∀ u ∈ co3P, orderOf u = 2 →
    CompsSatisfy (centralizerIn co3P u) fun Y _ => Nat.card (Y ⧸ center Y) ∈ co3Orders := by
  intro u hu ho
  obtain ⟨-, -, -, hcl, -, -⟩ := ctuc_co3_complete_inner_involution_classes
  by_cases hz : ∃ g ∈ co3P, u = g * co3Z * g⁻¹
  · obtain ⟨g, hg, rfl⟩ := hz
    rw [centralizerIn_conj co3P hg, centralizerIn, ← co3M_eq_centralizer]
    exact CompsSatisfy.of_mulEquiv (isoInvariant_card_quotient_center _) (conjEquiv co3M g).symm
      co3M_comps
  · have ht : ∃ g ∈ co3P, u = g * co3Tt * g⁻¹ := by
      by_contra h
      exact hz ((hcl u hu ho).2 h)
    obtain ⟨g, hg, rfl⟩ := ht
    rw [centralizerIn_conj co3P hg, centralizerIn, ← co3M1_eq_centralizer]
    exact CompsSatisfy.of_mulEquiv (isoInvariant_card_quotient_center _) (conjEquiv co3M1 g).symm
      co3M1_comps

theorem co3_inner_comps {G : Type} [Group G] (e : G ≃* NativeSporadic.Co3) (t : G)
    (ht : orderOf t = 2) :
    CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => Nat.card (Y ⧸ center Y) ∈ co3Orders :=
  compsSatisfy_centralizer_of_mulEquiv co3P (isoInvariant_card_quotient_center _)
    co3_centralizerIn_comps (e.trans co3PermEquiv) t ht

end CFSG.ComponentClassification.RestrictedStd.Spor
