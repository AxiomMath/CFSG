module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.OddFixCore
public import Certificates.Certificate25551

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SmallOddCore.Native (natArr)
open CFSG.EvenSporadicStandard.HSStd (facW tables_spec hsC1_enum wordPerm_mem_hsC1)

theorem oddFix_parts :
    hsOdd1PowA = true ∧ hsOdd1PowB = true ∧ hsOdd1PowAB = true ∧ hsOdd1Quart = true :=
  Certificates.certificate25551

noncomputable abbrev hsOdd1A : Equiv.Perm (Fin 3850) := (hsOdd1WordA.map hsC1Perm).prod

noncomputable abbrev hsOdd1B : Equiv.Perm (Fin 3850) := (hsOdd1WordB.map hsC1Perm).prod

theorem hsOdd1WordA_lt : ∀ j ∈ hsOdd1WordA, j < 2 := by decide

theorem hsOdd1WordB_lt : ∀ j ∈ hsOdd1WordB, j < 2 := by decide

theorem tabRep_hsOdd1A : TabRep hsOdd1TabA hsOdd1A :=
  tabRep_wordTabS tabRep_hsC1Tabs _ fun j hj => by simpa [hsC1Tabs] using hsOdd1WordA_lt j hj

theorem tabRep_hsOdd1B : TabRep hsOdd1TabB hsOdd1B :=
  tabRep_wordTabS tabRep_hsC1Tabs _ fun j hj => by simpa [hsC1Tabs] using hsOdd1WordB_lt j hj

theorem hsOdd1A_mem :
    hsOdd1A ∈ hsC1 :=
  wordPerm_mem_hsC1 hsOdd1WordA_lt

theorem hsOdd1B_mem :
    hsOdd1B ∈ hsC1 :=
  wordPerm_mem_hsC1 hsOdd1WordB_lt

theorem pow_eq_of_wordTabS {m k : ℕ} {a t : Tab} {A T : Equiv.Perm (Fin m)} (ha : TabRep a A)
    (ht : TabRep t T) (h : wordTabS m #[a] (List.replicate k 0) = t) : A ^ k = T := by
  have tw := tabRep_wordTabS (gs := #[a]) (f := fun _ => A)
    (fun j hj => by
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      simpa using ha) (List.replicate k 0) (by simp)
  have := (tw.eq_iff ht).1 h
  rwa [List.map_replicate, List.prod_replicate] at this

theorem hsOdd1A_pow :
    hsOdd1A ^ 5 = 1 := by
  have h := oddFix_parts.1
  simp only [hsOdd1PowA, beq_iff_eq] at h
  exact pow_eq_of_wordTabS tabRep_hsOdd1A TabRep.idTab h

theorem hsOdd1B_pow :
    hsOdd1B ^ 5 = 1 := by
  have h := oddFix_parts.2.1
  simp only [hsOdd1PowB, beq_iff_eq] at h
  exact pow_eq_of_wordTabS tabRep_hsOdd1B TabRep.idTab h

theorem hsOdd1_prod_pow :
    (hsOdd1A * hsOdd1B) ^ 10 = hsT1 := by
  have h := oddFix_parts.2.2.1
  simp only [hsOdd1PowAB, beq_iff_eq] at h
  obtain ⟨-, -, -, -, -, -, tT, -⟩ := tables_spec
  exact pow_eq_of_wordTabS (tabRep_hsOdd1A.comp tabRep_hsOdd1B) tT h

theorem mem_hsC1_or_of_mem_hsR
    {y : Equiv.Perm (Fin 3850)} (hy : y ∈ hsR) (hyt : y * hsT1 = hsT1 * y) :
    y ∈ hsC1 ∨ facW⁻¹ * y ∈ hsC1 := by
  by_cases hyP : y ∈ hsP
  · exact Or.inl (mem_inf.2 ⟨hyP, mem_centralizer_singleton_iff.2 hyt⟩)
  · obtain ⟨hwR, hwP, hwt, -⟩ := tables_spec
    obtain ⟨hU2, -, -, hmap, -⟩ := hs_normalizing_model
    have hUn : ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP := fun p hp => by
      rw [← hmap]
      exact ⟨p, hp, rfl⟩
    have hc : facW⁻¹ * y ∈ hsP := HypOne.index_two_of_normalizing hU2 hUn facW hwR hwP y hy hyP
    have hcomm : Commute (facW⁻¹ * y) hsT1 :=
      (Commute.inv_left (show Commute facW hsT1 from hwt)).mul_left (show Commute y hsT1 from hyt)
    exact Or.inr (mem_inf.2 ⟨hc, mem_centralizer_singleton_iff.2 hcomm⟩)

theorem hs_odd1 :
    ∀ y ∈ hsR, y * hsOdd1A = hsOdd1A * y → y * hsOdd1B = hsOdd1B * y → y ^ 4 = 1 := by
  intro y hy hA hB
  have hyt : y * hsT1 = hsT1 * y := by
    rw [← hsOdd1_prod_pow]
    exact (((show Commute y hsOdd1A from hA).mul_right (show Commute y hsOdd1B from hB)).pow_right
      10).eq
  obtain ⟨-, -, hwt, -, tW, -⟩ := tables_spec
  have hgs : ∀ j < hsOdd1Tabs.size, TabRep hsOdd1Tabs[j]!
      (if j = 0 then hsOdd1A else hsOdd1B) := fun j hj => by
    have hj2 : j < 2 := by simpa [hsOdd1Tabs] using hj
    interval_cases j
    · simpa [hsOdd1Tabs] using tabRep_hsOdd1A
    · simpa [hsOdd1Tabs] using tabRep_hsOdd1B
  have hG : ∀ z : Equiv.Perm (Fin 3850), z * hsOdd1A = hsOdd1A * z → z * hsOdd1B = hsOdd1B * z →
      ∀ j < hsOdd1Tabs.size, z * (if j = 0 then hsOdd1A else hsOdd1B) =
        (if j = 0 then hsOdd1A else hsOdd1B) * z := fun z hzA hzB j hj => by
    have hj2 : j < 2 := by simpa [hsOdd1Tabs] using hj
    interval_cases j
    · simpa using hzA
    · simpa using hzB
  obtain ⟨h1, h2⟩ := quartCheck_spec hsC1_enum tW hgs (oddFix_parts.2.2.2)
  rcases mem_hsC1_or_of_mem_hsR hy hyt with hc | hc
  · exact h1 y hc (hG y hA hB)
  · have e : facW * (facW⁻¹ * y) = y := mul_inv_cancel_left _ _
    have := h2 (facW⁻¹ * y) hc (fun j hj => by rw [e]; exact hG y hA hB j hj)
    rwa [e] at this

end CFSG.EvenSporadicStandard.TwoHS
