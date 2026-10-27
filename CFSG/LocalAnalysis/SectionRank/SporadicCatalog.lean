
module

public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public import CFSG.LocalAnalysis.SectionRank.QuasisimpleCatalog
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.LocalAnalysis.SectionRank.Monster
public import CFSG.LocalAnalysis.SectionRank.Sporadic.B
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co1
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi22
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi23
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi24prime
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HN
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Ly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Suz
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Th
public import CFSG.LocalAnalysis.SectionRank.SporadicCover

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

theorem M12_perfect_odd_cover_trivial
    (π : E →* NativeSporadic.M12) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hcard := CFSG.Sporadic.Mathieu.card_M12
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := M12_sylow3_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (by rw [hcard]; decide) hhx hhy hhz (by decide +revert) Cp
  · exfalso
    rw [hcard, show 95040 = (2 ^ 6 * 3 ^ 3) * [5, 11].prod by norm_num] at hsq
    exact not_sq_dvd_of_factorization hr (Nat.Coprime.mul_right
      (coprime_pow_of_ne hr Nat.prime_two hr2 _) (coprime_pow_of_ne hr Nat.prime_three h3 _))
      _ (by norm_num) (by decide) hsq

theorem M24_perfect_odd_cover_trivial
    (π : E →* NativeSporadic.M24) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hcard := CFSG.Sporadic.Mathieu.card_M24
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := M24_sylow3_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (by rw [hcard]; decide) hhx hhy hhz (by decide +revert) Cp
  · exfalso
    rw [hcard, show 244823040 = (2 ^ 10 * 3 ^ 3) * [5, 7, 11, 23].prod by norm_num] at hsq
    exact not_sq_dvd_of_factorization hr (Nat.Coprime.mul_right
      (coprime_pow_of_ne hr Nat.prime_two hr2 _) (coprime_pow_of_ne hr Nat.prime_three h3 _))
      _ (by norm_num) (by decide) hsq

theorem J4_perfect_odd_cover_trivial
    (hJ4 : J4OrderHyp) (π : E →* NativeSporadic.J4)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    π.ker = ⊥ := by
  have : Finite NativeSporadic.J4 := Finite.of_surjective π hπ
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := J4_sylow3_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (fun h4 => absurd (h4.trans hJ4) (by decide)) hhx hhy hhz (by decide +revert) Cp
  by_cases h11 : r = 11
  · subst h11
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := J4_sylow11_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (fun h4 => absurd (h4.trans hJ4) (by decide)) hhx hhy hhz (by decide +revert) Cp
  · exfalso
    have hsq' := hsq.trans hJ4
    rw [show 86775571046077562880 = (2 ^ 21 * 3 ^ 3 * 11 ^ 3) * [5, 7, 23, 29, 31, 37, 43].prod by
      norm_num] at hsq'
    exact not_sq_dvd_of_factorization hr (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (coprime_pow_of_ne hr Nat.prime_two hr2 _) (coprime_pow_of_ne hr Nat.prime_three h3 _))
      (coprime_pow_of_ne hr (by norm_num) h11 _)) _ (by norm_num) (by decide) hsq'

theorem catalog_sporadic_of
    (hJ4 : J4OrderHyp) : CatalogSporadicHyp := by
  intro L _ _ hL hSQT hodd hrep
  obtain ⟨s, ⟨e⟩⟩ := hrep
  have : Group.IsPerfect L := hL.1
  have hnt : Nontrivial (L ⧸ Subgroup.center L) := by
    have := hL.2.1
    infer_instance
  have htriv : ∀ {S : Type} [Group S] (e' : L ⧸ Subgroup.center L ≃* S),
      (∀ (π : L →* S), Function.Surjective π → π.ker ≤ Subgroup.center L →
        Odd (Nat.card π.ker) → π.ker = ⊥) → CatalogStepConclusion L :=
    fun e' h => (catalogStepConclusion_of_perfect_odd_cover_trivial hSQT hodd e' h).2
  have hex : ∀ {T : Type} [Group T], (∃ E : Subgroup T, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) →
      (L ⧸ Subgroup.center L ≃* T) → CatalogStepConclusion L := fun hT e' =>
    ((central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl hT).false e').elim
  cases s with
  | M11 => exact (four_small_sporadic_odd_cover_step hL hodd (Or.inl rfl) e).1
  | M22 => exact (four_small_sporadic_odd_cover_step hL hodd (Or.inr (Or.inl rfl)) e).1
  | M23 => exact (four_small_sporadic_odd_cover_step hL hodd (Or.inr (Or.inr (Or.inl rfl))) e).1
  | J1 => exact (four_small_sporadic_odd_cover_step hL hodd (Or.inr (Or.inr (Or.inr rfl))) e).1
  | M12 => exact htriv (S := NativeSporadic.M12) e fun π hπ hC h => M12_perfect_odd_cover_trivial π hπ hC h
  | M24 => exact htriv (S := NativeSporadic.M24) e fun π hπ hC h => M24_perfect_odd_cover_trivial π hπ hC h
  | J2 => exact htriv (S := NativeSporadic.J2) e fun π hπ hC h => J2_perfect_odd_cover_trivial π hπ hC h
  | HS => exact htriv (S := NativeSporadic.HS) e fun π hπ hC h => HS_perfect_odd_cover_trivial π hπ hC h
  | He => exact htriv (S := NativeSporadic.He) e fun π hπ hC h => He_perfect_odd_cover_trivial π hπ hC h
  | Ru => exact htriv (S := NativeSporadic.Ru) e fun π hπ hC h => Ru_perfect_odd_cover_trivial π hπ hC h
  | J4 =>
    exact htriv (S := NativeSporadic.J4) e fun π hπ hC h => J4_perfect_odd_cover_trivial hJ4 π hπ hC h
  | J3 => exact ((J3_odd_central_quotient_exclusion hSQT _ le_rfl hodd).false e).elim
  | M => exact ((M_nontrivial_central_quotient_exclusion hSQT _ le_rfl hnt).false e).elim
  | McL => exact hex McL_elementary_three_rank_four e
  | Suz => exact hex Suz_elementary_three_rank_four e
  | ONan => exact hex ON_elementary_three_rank_four e
  | Co1 => exact hex Co1_elementary_three_rank_four e
  | Co2 => exact hex Co2_elementary_three_rank_four e
  | Co3 => exact hex Co3_elementary_three_rank_four e
  | Fi22 => exact hex Fi22_elementary_three_rank_four e
  | Fi23 => exact hex Fi23_elementary_three_rank_four e
  | Fi24Prime => exact hex Fi24prime_elementary_three_rank_four e
  | HN => exact hex HN_elementary_three_rank_four e
  | Ly => exact hex Ly_elementary_three_rank_four e
  | Th => exact hex Th_elementary_three_rank_four e
  | B => exact hex B_elementary_three_rank_four e

end CFSG.SectionRank
