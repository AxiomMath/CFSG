module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Props
public import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open CFSG CFSG.Open CFSG.Blueprint CFSG.RankThree.PartOne.OutStructure
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

theorem not_outerKlein_of_outPChain {S : Type} [Group S] (σ : MulAut S) (h : OutPChain 2 S) :
    ¬ OuterKlein σ := by
  rintro ⟨α, β, -, -, hα2, hβ2, hcomm, hα, hβ, hαβ⟩
  obtain ⟨D, E, hID, hD2, hpE, hD4⟩ := h
  set I : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hI
  haveI hIn : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.innerNormal S
  have sq2 : ∀ γ : MulAut S, γ ^ (2 ^ 1) = γ * γ := fun γ => by rw [pow_one, sq]
  have hαD : α ^ (2 ^ 1) ∈ D := by
    rw [sq2]
    exact hID hα2
  have hβD : β ^ (2 ^ 1) ∈ D := by
    rw [sq2]
    exact hID hβ2
  have hαE := hpE α ⟨1, hαD⟩
  have hβE := hpE β ⟨1, hβD⟩
  have hsq : (α * β) * (α * β) ∈ I := by
    have e : (α * β) * (α * β) =
        (α * β * α⁻¹ * β⁻¹) * (β * (α * α) * β⁻¹) * (β * β) := by group
    rw [e]
    exact mul_mem (mul_mem hcomm (hIn.conj_mem _ hα2 β)) hβ2
  have hαβ' : α * β ∈ D → False := fun hm =>
    hαβ (hD2 _ hm 1 (by rw [sq2]; exact hsq))
  rcases hD4 α hαE β hβE ⟨1, hαD⟩ ⟨1, hβD⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨k, hk | hk⟩ := Int.even_or_odd' m
    · have hβm : β ^ m ∈ I := by
        rw [hk, zpow_mul, zpow_two]
        exact I.zpow_mem hβ2 k
      have hαD' : α ∈ D := by
        have := D.mul_mem hm (D.inv_mem (hID hβm))
        simpa using this
      exact hα (hD2 α hαD' 1 (by rw [sq2]; exact hα2))
    · have hβm : β ^ m = β * (β * β) ^ k := by
        rw [hk, add_comm, zpow_add, zpow_one, zpow_mul, zpow_two]
      have hαβD : α * β ∈ D := by
        have h1 : α * β ^ m = α * β * (β * β) ^ k := by rw [hβm, mul_assoc]
        have h2 := D.mul_mem hm (D.inv_mem (hID (I.zpow_mem hβ2 k)))
        rw [h1] at h2
        simpa using h2
      exact hαβ' hαβD
  · obtain ⟨k, hk | hk⟩ := Int.even_or_odd' m
    · have hαm : α ^ m ∈ I := by
        rw [hk, zpow_mul, zpow_two]
        exact I.zpow_mem hα2 k
      have hβD' : β ∈ D := by
        have := D.mul_mem hm (D.inv_mem (hID hαm))
        simpa using this
      exact hβ (hD2 β hβD' 1 (by rw [sq2]; exact hβ2))
    · have hαm : α ^ m = α * (α * α) ^ k := by
        rw [hk, add_comm, zpow_add, zpow_one, zpow_mul, zpow_two]
      have hβαD : β * α ∈ D := by
        have h1 : β * α ^ m = β * α * (α * α) ^ k := by rw [hαm, mul_assoc]
        have h2 := D.mul_mem hm (D.inv_mem (hID (I.zpow_mem hα2 k)))
        rw [h1] at h2
        simpa using h2
      have hαβD : α * β ∈ D := by
        have e : α * β = (α * β * α⁻¹ * β⁻¹) * (β * α) := by group
        rw [e]
        exact D.mul_mem (hID hcomm) hβαD
      exact hαβ' hαβD

theorem harrisKleinFree_of_outPChain {t : StatedLieTag} {n p f : ℕ}
    (H : ∀ (S : Type) [Group S], LieModel S t n p f → OutPChain 2 S) :
    HarrisKleinFree t n p f :=
  fun S _ _ hm σ _ _ _ => not_outerKlein_of_outPChain σ (H S hm)

theorem harrisKleinFree_PSp_two_two_two : HarrisKleinFree .PSp 2 2 2 :=
  harrisKleinFree_of_outPChain fun _ _ hm =>
    (outPNice_PSp_two Nat.prime_two
      (CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide))).toChain

theorem harrisKleinFree_PSp_two_two_three : HarrisKleinFree .PSp 2 2 3 :=
  harrisKleinFree_of_outPChain fun _ _ hm =>
    (outPNice_PSp_two Nat.prime_two
      (CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide))).toChain

theorem harrisKleinFree_PSU_four_two_one : HarrisKleinFree .PSU 4 2 1 :=
  harrisKleinFree_of_outPChain fun _ _ hm =>
    (outPNice_PSU Nat.prime_two
      (CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide)) (by decide)).toChain

theorem harrisKleinFree_PSU_five_two_one : HarrisKleinFree .PSU 5 2 1 :=
  harrisKleinFree_of_outPChain fun _ _ hm =>
    (outPNice_PSU Nat.prime_two
      (CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide)) (by decide)).toChain

theorem outPNice_PSU_three_three_two {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 3 3 2) : OutPNice 2 X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 3 2 K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(3 = 3 ∧ 3 ^ 2 = 2) := by norm_num
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := 3)) hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact OutPNice.of_mulEquiv e' (outPNice_primeFormP hU hn3 hq Nat.prime_two (by decide))

theorem harrisKleinFree_PSU_three_three_two : HarrisKleinFree .PSU 3 3 2 :=
  harrisKleinFree_of_outPChain fun _ _ hm =>
    (outPNice_PSU_three_three_two
      (CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide))).toChain

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
