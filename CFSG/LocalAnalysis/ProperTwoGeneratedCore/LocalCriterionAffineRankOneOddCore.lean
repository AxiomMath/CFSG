module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineRankOneCentral
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne

open BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1

universe u v

theorem odd_core_eq_two_prime_core (F : Type u) [Group F] :
    CFSG.oddCore F = pPrimeCore 2 F := by
  unfold CFSG.oddCore pPrimeCore
  congr 1
  ext N
  exact and_congr Iff.rfl Nat.coprime_two_left.symm

theorem odd_core_card_odd (F : Type u) [Group F] [Finite F] :
    Odd (Nat.card (CFSG.oddCore F)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [odd_core_eq_two_prime_core]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := F))

theorem odd_core_nontrivial_of_rank_one_primitive
    {F : Type u} [Group F] [Finite F]
    {Λ : Type v} [MulAction F Λ] [Finite Λ]
    [MulAction.IsPretransitive F Λ] [FaithfulSMul F Λ]
    (heven : Even (Nat.card F)) (hrank : ¬ TwoRankAtLeastTwo F)
    (hdegree : 3 ≤ Nat.card Λ) (a : Λ)
    (hmax : IsCoatom (MulAction.stabilizer F a)) :
    CFSG.oddCore F ≠ ⊥ := by
  let : Nontrivial Λ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcore
  obtain ⟨t, htorder⟩ := exists_prime_orderOf_dvd_card' (G := F) 2
    (even_iff_two_dvd.mp heven)
  have htne : t ≠ 1 := by
    intro h
    simp [h] at htorder
  have htsq : t ^ 2 = 1 := by
    rw [← htorder]
    exact pow_orderOf_eq_one t
  have hfactor := BenderSuzuki.PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
    hrank (show IsInvolution t from ⟨htne, htsq⟩)
  have hprimecore : pPrimeCore 2 F = ⊥ :=
    (odd_core_eq_two_prime_core F).symm.trans hcore
  have hcentralizer : Subgroup.centralizer ({t} : Set F) = ⊤ := by
    simpa only [hprimecore, bot_sup_eq] using hfactor
  have htcenter : t ∈ Subgroup.center F := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply Subgroup.mem_centralizer_singleton_iff.mp
    rw [hcentralizer]
    exact Subgroup.mem_top g
  have hsmall := central_involution_primitive_degree_le_two a hmax t htcenter htorder
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne
