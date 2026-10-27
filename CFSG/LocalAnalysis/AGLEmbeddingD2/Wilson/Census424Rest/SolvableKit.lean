module

public import CFSG.CharacterTheory.Burnside
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.GroupTheory.SteinbergCDCentralQuotientFixed
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTitsCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem centralizer_le_normalizer_zpowers {G : Type*} [Group G] (v : G) :
    Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
  have h1 : Subgroup.centralizer ({v} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure]
    exact (Subgroup.centralizer_closure _).symm
  rw [h1]
  exact Subgroup.centralizer_le_normalizer _

theorem isSolvable_centralizer_of_isSolvable_normalizer {G : Type*} [Group G] (v : G)
    (h : Group.IsSolvable (Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G))) :
    Group.IsSolvable (Subgroup.centralizer ({v} : Set G)) :=
  Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (centralizer_le_normalizer_zpowers v))
    (Subgroup.inclusion_injective _)

theorem isSolvable_of_card_dvd_two_three {H : Type*} [Group H] [Finite H] {a b : ℕ}
    (h : Nat.card H ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem isSolvable_perm_three_prod_alt_four :
    Group.IsSolvable (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) := by
  have h3 : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    isSolvable_of_card_dvd_two_three (a := 1) (b := 1) (by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide)
  have h4' : Group.IsSolvable (Equiv.Perm (Fin 4)) :=
    isSolvable_of_card_dvd_two_three (a := 3) (b := 1) (by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide)
  have h4 : Group.IsSolvable (alternatingGroup (Fin 4)) :=
    Group.isSolvable_of_isSolvable_injective (f := (alternatingGroup (Fin 4)).subtype)
      (alternatingGroup (Fin 4)).subtype_injective
  infer_instance



theorem isSolvable_centralizer_of_normalizer_equiv {G : Type*} [Group G] (v : G)
    (e : Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) :
    Group.IsSolvable (Subgroup.centralizer ({v} : Set G)) :=
  isSolvable_centralizer_of_isSolvable_normalizer v (by
    have := isSolvable_perm_three_prod_alt_four
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
