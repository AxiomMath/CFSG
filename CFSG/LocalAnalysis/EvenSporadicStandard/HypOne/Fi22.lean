module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Classes
public import CFSG.Sporadic.FischerOddCore.Fi22AllInv
public import Certificates.Certificate25641
public import Certificates.Certificate25642
public import Certificates.Certificate25643
public import Certificates.Certificate25644
public import Certificates.Certificate25645
public import Certificates.Certificate25646

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi22

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem fourClassesLarge_P
    {k : ℕ} (hk : k < 6) {capS capC : ℕ}
    {cg sg : Array Table} {ord : ℕ}
    (hord : ord = 2 ^ (Nat.card ↥(centralizerIn fi22P (fi22ExtRep k))).factorization 2)
    (h : sylowFourOK 3510 capS capC (memP (tT k)) cg sg ord = true) :
    FourClassesLarge ↥(centralizerIn fi22P (fi22ExtRep k)) := by
  refine fourClassesLarge_of_sylowFourOK (by norm_num) (fun T g hT hm => ?_) hord h
  rw [memP, Bool.and_eq_true] at hm
  exact mem_centralizerIn.2 ⟨(siftP_iff hT).1 hm.1, (commTT_iff hT (rep_tT hk)).1 hm.2⟩

theorem fourClassesLarge_R
    {k : ℕ} (hk : k < 6) {capS capC : ℕ}
    {cg sg : Array Table} {ord : ℕ}
    (hord : ord = 2 ^ (Nat.card ↥(centralizerIn fi22R (fi22ExtRep k))).factorization 2)
    (h : sylowFourOK 3510 capS capC (memR (tT k)) cg sg ord = true) :
    FourClassesLarge ↥(centralizerIn fi22R (fi22ExtRep k)) := by
  refine fourClassesLarge_of_sylowFourOK (by norm_num) (fun T g hT hm => ?_) hord h
  rw [memR, Bool.and_eq_true] at hm
  exact mem_centralizerIn.2 ⟨(siftR_iff hT).1 hm.1, (commTT_iff hT (rep_tT hk)).1 hm.2⟩

theorem fourClassesLarge_rows :
    (∀ v ∈ fi22P, orderOf v = 2 → FourClassesLarge ↥(centralizerIn fi22P v)) ∧
      ∀ v ∈ fi22R, orderOf v = 2 → FourClassesLarge ↥(centralizerIn fi22R v) := by
  have hP0 := Certificates.certificate25641
  have hP1 := Certificates.certificate25642
  have hP2 := Certificates.certificate25643
  have hR0 := Certificates.certificate25644
  have hR1 := Certificates.certificate25645
  have hR2 := Certificates.certificate25646
  obtain ⟨-, -, hR3, hR4, hR5⟩ := Certificates.certificate25640
  have fP : ∀ k < 3, FourClassesLarge ↥(centralizerIn fi22P (fi22ExtRep k)) := by
    intro k hk
    interval_cases k
    · exact hP0
    · exact hP1
    · exact hP2
  have fR : ∀ k < 6, FourClassesLarge ↥(centralizerIn fi22R (fi22ExtRep k)) := by
    intro k hk
    interval_cases k
    · exact hR0
    · exact hR1
    · exact hR2
    · exact hR3
    · exact hR4
    · exact hR5
  refine ⟨fourClassesLarge_centralizerIn_of_reps fi22P ((List.range 3).map fi22ExtRep) cover_P
      fun r hr => ?_, fourClassesLarge_centralizerIn_of_reps fi22R ((List.range 6).map fi22ExtRep)
      cover_R fun r hr => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    exact fP k (List.mem_range.1 hk)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    exact fR k (List.mem_range.1 hk)

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.Fi22 := by
  obtain ⟨hP, hR⟩ := fourClassesLarge_rows
  exact hypothesisOne_of_outTwo fi22PermEquiv center_fi22P fi22_autModel fi22RAut card_fi22R_le
    (fun τ hτ h2 => CTUC_Fi22_all_involution_fixed_subgroups_odd_core_trivial τ hτ h2) hP hR

theorem fi22ExtRep_mem_R
    {k : ℕ} (hk : 3 ≤ k) (hk6 : k < 6) :
    fi22ExtRep k ∈ fi22R := by
  have := (CTUC_Fi22_all_extension_involutions_covered.2.1 (k - 3) (by omega)).1
  rwa [show 3 + (k - 3) = k by omega] at this

theorem foursGroupCondition_native :
    CFSG.EvenSmallLie.FoursGroupCondition NativeSporadic.Fi22 := by
  have hw := Certificates.certificate25640.2.1
  obtain ⟨l3, hl3, hl3'⟩ := hw 3 (by norm_num) (by norm_num)
  obtain ⟨l4, hl4, hl4'⟩ := hw 4 (by norm_num) (by norm_num)
  obtain ⟨l5, hl5, hl5'⟩ := hw 5 (by norm_num) (by norm_num)
  have m3 : fi22ExtRep 3 ∈ fi22R := fi22ExtRep_mem_R (by norm_num) (by norm_num)
  have m4 : fi22ExtRep 4 ∈ fi22R := fi22ExtRep_mem_R (by norm_num) (by norm_num)
  have m5 : fi22ExtRep 5 ∈ fi22R := fi22ExtRep_mem_R (by norm_num) (by norm_num)
  refine foursGroupCondition_of_outTwo fi22PermEquiv center_fi22P fi22P_le_R fi22RAut
    (fun x p => fi22ConjHom_apply x p) [⟨_, m3⟩, ⟨_, m4⟩, ⟨_, m5⟩]
    (fun τ hτ hτP => ?_) (fun ρ hρ => ?_)
  · obtain ⟨k, hk3, hk6, g, hg, e⟩ := cover_outer τ.2 hτ hτP
    interval_cases k
    · exact ⟨⟨_, m3⟩, List.mem_cons_self, g, hg, e⟩
    · exact ⟨⟨_, m4⟩, by simp, g, hg, e⟩
    · exact ⟨⟨_, m5⟩, by simp, g, hg, e⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl
    · exact ⟨l3, hl3, hl3'⟩
    · exact ⟨l4, hl4, hl4'⟩
    · exact ⟨l5, hl5, hl5'⟩

theorem hypothesisOne_of_isSporadic
    {Y : Type} [Group Y]
    (h : IsSporadic Y .Fi22) : HypothesisOne Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hypothesisOne_native

theorem foursGroupCondition_of_isSporadic
    {Y : Type}
    [Group Y] (h : IsSporadic Y .Fi22) : CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_mulEquiv e.symm foursGroupCondition_native

end CFSG.EvenSporadicStandard.HypOne.Fi22
