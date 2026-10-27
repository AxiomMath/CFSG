module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsModel
public import Certificates.Certificate25950

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SmallOddCore.Native (natArr)
open CFSG.EvenSporadicStandard.HSStd (tables_spec)

section Fix

@[expose] def fixCard {n : ℕ} (g : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, if g i = i then 1 else 0

theorem fixCard_conj {n : ℕ} (g x : Equiv.Perm (Fin n)) : fixCard (g * x * g⁻¹) = fixCard x := by
  unfold fixCard
  rw [← Equiv.sum_comp g (fun i => if (g * x * g⁻¹) i = i then 1 else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq]

theorem countP_range_eq_sum (n : ℕ) (p : ℕ → Bool) :
    (List.range n).countP p = ∑ i : Fin n, if p i = true then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Fin.sum_univ_castSucc]
    simp

theorem fixTab_eq {n : ℕ} {T : Tab} {X : Equiv.Perm (Fin n)} (h : TabRep T X) :
    fixTab n T = fixCard X := by
  rw [fixTab, countP_range_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (T[i.val]! == i.val) = true ↔ X i = i := by
    rw [beq_iff_eq, h.apply i]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  by_cases hh : X i = i
  · simp [h1.2 hh, hh]
  · have : ¬ (T[i.val]! == i.val) = true := fun h' => hh (h1.1 h')
    simp [this, hh]

theorem fixTbl_eq {n : ℕ} {T : CFSG.Sporadic.Th.Native.Table} {X : Equiv.Perm (Fin n)}
    (h : CFSG.Sporadic.Th.Rep n T X) : fixTbl n T = fixCard X := by
  rw [fixTbl, countP_range_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (CFSG.Sporadic.Th.Native.ap T i.val == i.val) = true ↔ X i = i := by
    rw [beq_iff_eq, h i.val i.2, CFSG.Sporadic.Th.idx_of_lt X i.2, Equiv.Perm.smul_def]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  by_cases hh : X i = i
  · simp [h1.2 hh, hh]
  · have : ¬ (CFSG.Sporadic.Th.Native.ap T i.val == i.val) = true := fun h' => hh (h1.1 h')
    simp [this, hh]


theorem fixCard_one (n : ℕ) : fixCard (1 : Equiv.Perm (Fin n)) = n := by
  simp [fixCard]

theorem ne_one_of_fixCard_lt {n k : ℕ} {g : Equiv.Perm (Fin n)} (h : fixCard g = k) (hk : k < n) :
    g ≠ 1 := fun h1 => by
  rw [h1, fixCard_one] at h
  omega

theorem orderOf_eq_two_of_sq {G : Type*} [Group G] {a : G} (h : a * a = 1) (h1 : a ≠ 1) :
    orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rwa [sq]) h1

end Fix

section Classes

theorem s6Fix_parts : s6FixOK = true ∧ s6FixCoverOK = true := by
  have h := Certificates.certificate25950.2.2.2
  simpa [s6Fix, Bool.and_eq_true] using h

theorem s6FixOK_parts :
    permOK 3850 (hsCentTbl 12) = true ∧ (natArr (hsCentTbl 12)).size = 3850 ∧
      fixTab 3850 (natArr (hsCentTbl 5)) = 170 ∧ fixTab 3850 (natArr (hsCentTbl 12)) = 30 ∧
      fixTab 3850 s6XTab = 170 ∧ fixTab 3850 (comp 3850 s6XTab (natArr (hsCentTbl 5))) = 170 ∧
      fixTab 3850 (comp 3850 s6XTab s6WTab) = 30 := by
  have h := s6Fix_parts.1
  simpa only [s6FixOK, Bool.and_eq_true, beq_iff_eq, and_assoc] using h


theorem tabRep_hsT2 : TabRep (natArr (hsCentTbl 12)) hsT2 :=
  tabRep_natArr s6FixOK_parts.1 s6FixOK_parts.2.1

theorem fixCard_hsT1 : fixCard hsT1 = 170 := by
  rw [← fixTab_eq (tables_spec.2.2.2.2.2.2.1)]
  exact s6FixOK_parts.2.2.1

theorem fixCard_hsT2 : fixCard hsT2 = 30 := by
  rw [← fixTab_eq tabRep_hsT2]
  exact s6FixOK_parts.2.2.2.1

theorem exists_conj_hsT1_of_fixCard {τ : Equiv.Perm (Fin 3850)} (hτ : τ ∈ hsP)
    (h2 : orderOf τ = 2) (hf : fixCard τ = 170) : ∃ g ∈ hsP, τ = g * hsT1 * g⁻¹ := by
  obtain ⟨-, -, -, -, hcover⟩ := CFSG.Sporadic.SmallOddCore.hs_reps
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ hτ h2
  rcases hr with rfl | rfl
  · exact ⟨g, hg, rfl⟩
  · rw [fixCard_conj, fixCard_hsT2] at hf
    omega

theorem exists_conj_hsT2_of_fixCard {τ : Equiv.Perm (Fin 3850)} (hτ : τ ∈ hsP)
    (h2 : orderOf τ = 2) (hf : fixCard τ = 30) : ∃ g ∈ hsP, τ = g * hsT2 * g⁻¹ := by
  obtain ⟨-, -, -, -, hcover⟩ := CFSG.Sporadic.SmallOddCore.hs_reps
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ hτ h2
  rcases hr with rfl | rfl
  · rw [fixCard_conj, fixCard_hsT1] at hf
    omega
  · exact ⟨g, hg, rfl⟩

end Classes

end CFSG.EvenSporadicStandard.TwoHS
