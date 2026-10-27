module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3Check
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjWS
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J3

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.RankThree.Native

theorem j3P_le_R : j3P ≤ j3R := by
  show j3P ≤ j3P ⊔ zpowers j3u
  exact le_sup_left

theorem j3u_mem_R : j3u ∈ j3R := by
  show j3u ∈ j3P ⊔ zpowers j3u
  exact mem_sup_right (mem_zpowers _)

theorem j3AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .J3) ↥j3R (j3P.subgroupOf j3R) := by
  obtain ⟨e, he, -⟩ := ctuc_j3_full_automorphism_permutation_model
  exact autModel_of_conj j3P_le_R j3PermEquiv.symm e he

theorem j3_normal : (j3P.subgroupOf j3R).Normal := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  exact h

theorem card_j3R : Nat.card j3R = 100465920 := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  exact h

theorem j3StrongPerm_mem {k : ℕ}
    (hk : k < 5) : j3StrongPerm k ∈ j3P := by
  have hc : k < j3Chain.strongCount := by
    rw [CERT_J3_matrix_action_data.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hk
  have h := RawSchreierDatum.strong_get_mem_originalSubgroup j3Chain j3Chain_valid.1 ⟨k, hc⟩
  rw [j3Chain_strong_get, ← j3P_eq_original] at h
  exact h

theorem mem_j3P_of_inXL
    {si xe : Array ℕ} {ws : List (List ℕ)} (hsi : si.size = 5)
    (hinv : (allLt 5 fun k =>
      eqA 6156 (compA 6156 (si.map (CFSG.KC.Census.unpackP 6156 13))[k]! j3StrongArrs[k]!)
        (idA 6156)) = true)
    (hval : (allLt (j3Letters si).size fun k => validA 6156 (j3Letters si)[k]!) = true)
    (hxs : xsOK 6156 (j3Letters si) (xe.map (CFSG.KC.Census.unpackP 6156 13)) ws = true)
    {a : Array ℕ} (hv : validA 6156 a = true)
    (ha : inXL 6156 (xe.map (CFSG.KC.Census.unpackP 6156 13)) a = true) :
    permOfArr 6156 a ∈ j3P := by
  refine (closure_le j3P).2 ?_ (mem_closure_of_inXL hval hxs hv ha)
  rintro _ ⟨k, hk, rfl⟩
  have hsz : (j3Letters si).size = 10 := by simp [j3Letters, hsi, j3StrongArrs]
  have hk : k < 10 := by
    have := hk
    simp only [Set.mem_setOf_eq, hsz] at this
    exact this
  have hs5 : j3StrongArrs.size = 5 := by simp [j3StrongArrs]
  rcases Nat.lt_or_ge k 5 with h5 | h5
  · have e : (j3Letters si)[k]! = j3StrongArrs[k]! := by
      rw [j3Letters, getElem!_pos _ k (by simp [hsi, hs5]; omega),
        getElem!_pos j3StrongArrs k (by omega), Array.getElem_append_left]
    change permOfArr 6156 (j3Letters si)[k]! ∈ j3P
    rw [e]
    exact j3StrongPerm_mem h5
  · have hj : k - 5 < 5 := by omega
    have e : (j3Letters si)[k]! = (si.map (CFSG.KC.Census.unpackP 6156 13))[k - 5]! := by
      rw [j3Letters, getElem!_pos _ k (by simp [hsi, hs5]; omega),
        getElem!_pos _ (k - 5) (by simp [hsi]; omega), Array.getElem_append_right (by omega)]
      simp [hs5]
    change permOfArr 6156 (j3Letters si)[k]! ∈ j3P
    rw [e, permOfArr_eq_of_rep (rep_inv_of_comp (rep_j3StrongPerm hj) (allLt_spec hinv hj))]
    exact inv_mem (j3StrongPerm_mem hj)

theorem j3_yCensus : YCensus (j3P.subgroupOf j3R) (fun _ => False) := by
  obtain ⟨_, _, _, _, h⟩ := j3_check
  simp only [j3CheckW, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hu, hsi⟩, hinv⟩, hval⟩, hxs⟩, hc⟩, hgen⟩, hlen⟩ := h
  have hrep : Rep 6156 j3UArr j3u := (rep_permOfArr hu).1
  exact yCensus_pair_conjW_sound (m := 392445) j3P_le_R j3_normal j3PS_lt
    (fun a hv ha => mem_j3P_of_inXL hsi hinv hval hxs hv ha) hrep j3u_mem_R hc hgen
    (by rw [hlen]; norm_num [card_j3R]) (by decide)

theorem sporadicCaseOdd_J3 (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .J3 :=
  sporadicCaseOdd_of_yCensus h32 h33 j3AutModel j3_yCensus

end CFSG.ComponentClassification.RankTwoSporadic.J3
