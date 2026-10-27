module

public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1Group
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Transport

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.RuSz

open Subgroup CFSG.EvenSporadicStandard.RuStd

theorem factorization_two_card_SzB :
    (Nat.card SzB).factorization 2 = 6 := by
  rw [card_SzB]
  have h : (29120 : ℕ) = 2 ^ 6 * 455 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]


theorem card_centK0 {x : Equiv.Perm (Fin 4060)} (hx : x ∈ K0) (h2 : orderOf x = 2) :
    Nat.card ↥(K0 ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4060)))) = 64 := by
  obtain ⟨e₀⟩ := exists_mulEquiv_K0
  let e : K0 ≃* SzB := e₀.symm
  let x' : K0 := ⟨x, hx⟩
  have hx' : orderOf x' = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  have hz : orderOf (e x') = 2 := by rw [MulEquiv.orderOf_eq]; exact hx'
  obtain ⟨P, -, hCP, -⟩ :=
    ((CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers (a := 1)
      (K := GaloisField 2 3) le_rfl card_GF).1 (e x') hz)
  have hP : Nat.card ↥(Subgroup.centralizer ({e x'} : Set SzB)) = 64 := by
    rw [hCP, Sylow.card_eq_multiplicity, factorization_two_card_SzB]
    norm_num
  have h1 : Nat.card ↥(Subgroup.centralizer ({x'} : Set K0)) = 64 := by
    rw [← card_centralizer_equiv e x']
    exact hP
  have h2 : K0 ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4060))) =
      (Subgroup.centralizer ({x'} : Set K0)).map K0.subtype := by
    rw [map_centralizer_subtype_eq]
  rw [h2, Subgroup.card_map_of_injective K0.subtype_injective]
  exact h1

end CFSG.EvenSporadicStandard.Induction.RuSz

end
