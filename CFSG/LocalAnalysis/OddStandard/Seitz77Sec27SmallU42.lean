module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27SmallAut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import Certificates.Data.Seitz77Sec27SmallU42
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.KGroups.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier CFSG.Certificates

theorem centLenA_enumA {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (τ : Equiv.Perm (Fin n)) :
    centLenA n (enumA Q) (toA τ) =
      Nat.card ↥(Q.originalSubgroup ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin n)))) := by
  rw [card_inf_centralizer Q hQ τ, enumA_eq, centLenA, List.filter_map, List.length_map]
  congr 2
  funext g
  simp only [Function.comp_apply]
  exact eqA_eq_decide (rep_compA (rep_toA g) (rep_toA τ)) (rep_compA (rep_toA τ) (rep_toA g))

theorem toA_mem_enumA' {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup) : toA g ∈ enumA Q := by
  rw [enumA_eq]
  exact List.mem_map.2 ⟨g, (mem_elemsT Q hQ g).2 hg, rfl⟩

theorem u42CensusCheck_sound
    (h : Certificates.Seitz77Sec27.u42CensusCheck = true) :
    ∀ t ∈ QA45.originalSubgroup, t * t = 1 → t ≠ 1 →
      5 ∣ Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 45))) ⊓ QA45.originalSubgroup) →
        t ∉ QP45.originalSubgroup ∧ 2 ^ 5 ∣ Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 45))) ⊓ QA45.originalSubgroup) := by
  unfold Certificates.Seitz77Sec27.u42CensusCheck Certificates.Seitz77Sec27.u42CensusCheckL at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hP, hA⟩ := h
  intro t ht ht2 ht1 h5
  have hc : centLenA 45 (enumA QA45) (toA t) =
      Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 45))) ⊓ QA45.originalSubgroup) := by
    rw [centLenA_enumA QA45 QA45_ok t, inf_comm]
  have hinv : isInvolA 45 (toA t) = true := by
    rw [isInvolA_rep (rep_toA t)]
    simp [pow_two, ht2, ht1]
  have hmemA : toA t ∈ enumA QA45 := toA_mem_enumA' QA45 QA45_ok ht
  have h5' : 5 ∣ centLenA 45 (enumA QA45) (toA t) := hc ▸ h5
  refine ⟨fun htP => ?_, hc ▸ ?_⟩
  · have := List.all_eq_true.1 hP (toA t) (toA_mem_enumA' QP45 QP45_ok htP)
    rw [hinv] at this
    simp [h5'] at this
  · have := List.all_eq_true.1 hA (toA t) hmemA
    rw [hinv] at this
    simpa [h5'] using this

end CFSG.OddStandard.Seitz77
