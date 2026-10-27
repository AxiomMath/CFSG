module

public import CFSG.GH74.Filter.Small.RankThree
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.RowsE16
public import CFSG.LocalAnalysis.Mason73.Complement

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow

variable {G : Type} [Group G] [Finite G] {n p f : ℕ}

theorem exists_E16_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) :
    ∃ E : Subgroup G, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  obtain ⟨e⟩ := hP
  let ι : L4Model n →* G := (P : Subgroup G).subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  refine ⟨(E1 (n := n) (by omega)).map ι, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hι, card_E1 hn]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, pow_two, E1_mul_self _ x hx, map_one]

theorem four_le_twoRank_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) : 4 ≤ CFSG.Open.twoRank G := by
  obtain ⟨E, hE16, hE2⟩ := exists_E16_of_l4Sylow hn P hP
  have hE2' : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← pow_two]; exact hE2 x hx
  refine CFSG.SectionRank.le_pRank (by norm_num) le_top
    ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_mul_self hE2' a.2 b.2)⟩⟩, hE2⟩ (k := 4) ?_
  rw [hE16]
  norm_num

theorem false_of_lieModel_psl_two_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSL 2 p f) : False := by
  have h := CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2
    (hL.statedClassicalModel (by decide))
  have := four_le_twoRank_of_l4Sylow hn P hP
  omega

theorem false_of_lieModel_psl_three_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSL 3 p f) : False := by
  have h := CFSG.GH74.Filter.t_PSL_three_odd G p f hp2 (hL.statedClassicalModel (by decide))
  have := four_le_twoRank_of_l4Sylow hn P hP
  omega

theorem false_of_lieModel_psu_three_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSU 3 p f) : False := by
  have h := CFSG.GH74.Filter.t_PSU_three_odd G p f hp2 (hL.statedClassicalModel (by decide))
  have := four_le_twoRank_of_l4Sylow hn P hP
  omega


theorem false_of_lieModel_g2_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2) {r : ℕ}
    (hL : CFSG.Blueprint.LieModel G .G2 r p f) : False := by
  obtain ⟨-, hf, hr0, -⟩ := hL.admissible
  subst hr0
  exact CFSG.EvenSporadicStandard.HNRecog.GH73.not_g2_of_e16 (exists_E16_of_l4Sylow hn P hP) hp
    hp2 hf hL

theorem false_of_lieModel_trialityD4_of_l4Sylow
    (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2) {r : ℕ}
    (hL : CFSG.Blueprint.LieModel G .trialityD4 r p f) : False := by
  obtain ⟨-, hf, hr0⟩ := hL.admissible
  subst hr0
  exact CFSG.EvenSporadicStandard.HNRecog.GH73.not_trialityD4_of_e16
    (exists_E16_of_l4Sylow hn P hP) hp hp2 hf hL

end CFSG.LocalAnalysis.Mason73
