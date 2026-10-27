module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open CFSG.Sporadic.Schreier (j3P)

set_option linter.unusedSectionVars false

theorem card_centralizer_j3P_of_five_dvd {y : Equiv.Perm (Fin 6156)} (hy : y ∈ j3P)
    (hy3 : orderOf y = 3)
    (h5 : 5 ∣ Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
      Subgroup (Equiv.Perm (Fin 6156)))) :
    Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
      Subgroup (Equiv.Perm (Fin 6156))) = 1080 := by
  obtain ⟨k0, hk0, c, hc, e', he', hyeq⟩ := j3t_fusion hy hy3
  rcases hc with rfl | rfl
  · have hA3 : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2
    rw [hyeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hA3 he',
      ← j3t_caseA.1, j3t_caseA.2]
  · exfalso
    have hB3 : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2
    rw [hyeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hB3 he',
      ← j3t_caseB.1, j3t_caseB.2] at h5
    omega

theorem card_centralizer_of_equiv_J3 {Q : Type*} [Group Q] (e : Q ≃* NativeSporadic.J3) {q : Q}
    (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1)
    (h5 : 5 ∣ Nat.card (centralizer ({e q} : Set NativeSporadic.J3))) :
    Nat.card (centralizer ({q} : Set Q)) = 1080 := by
  have h5c : 5 ∣ Nat.card (centralizer ({e q} : Set (NativeSporadic.Carrier .J3))) := h5
  have hcard1 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
    Item228CensusProof.j3CarrierEquiv (e q)
  have hcard2 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
    (e.trans Item228CensusProof.j3CarrierEquiv) q
  obtain ⟨y, hyy⟩ : ∃ y : Equiv.Perm (Fin 6156),
      y = ((e.trans Item228CensusProof.j3CarrierEquiv) q : ↥j3P) := ⟨_, rfl⟩
  have hyj : y ∈ j3P := hyy ▸ ((e.trans Item228CensusProof.j3CarrierEquiv) q).2
  have hy3 : orderOf y = 3 := by
    have h3 : y ^ 3 = 1 := by
      have := congrArg (fun z : ↥j3P => (z : Equiv.Perm (Fin 6156)))
        (show (e.trans Item228CensusProof.j3CarrierEquiv) q ^ 3 = 1 from
          (map_pow (e.trans Item228CensusProof.j3CarrierEquiv) q 3).symm.trans
            ((congrArg (e.trans Item228CensusProof.j3CarrierEquiv) hq3).trans (map_one _)))
      rw [hyy]
      simpa using this
    have h1 : y ≠ 1 := by
      intro h
      apply hq1
      have : (e.trans Item228CensusProof.j3CarrierEquiv) q = 1 := Subtype.ext (hyy ▸ h)
      exact ((map_eq_one_iff _ (e.trans Item228CensusProof.j3CarrierEquiv).injective).1 this)
    exact orderOf_eq_prime h3 h1
  have h5' : 5 ∣ Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
      Subgroup (Equiv.Perm (Fin 6156))) := by
    rw [hyy]
    have e1 : (((e.trans Item228CensusProof.j3CarrierEquiv) q : ↥j3P) : Equiv.Perm (Fin 6156)) =
        ((Item228CensusProof.j3CarrierEquiv (e q) : ↥j3P) : Equiv.Perm (Fin 6156)) := rfl
    rw [e1, ← hcard1]; exact h5c
  have := card_centralizer_j3P_of_five_dvd hyj hy3 h5'
  rw [hcard2, ← hyy]
  exact this

theorem card_centralizer_j3P_dichotomy {y : Equiv.Perm (Fin 6156)} (hy : y ∈ j3P)
    (hy3 : orderOf y = 3) :
    Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
      Subgroup (Equiv.Perm (Fin 6156))) = 1080 ∨
    Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
      Subgroup (Equiv.Perm (Fin 6156))) = 243 := by
  obtain ⟨k0, hk0, c, hc, e', he', hyeq⟩ := j3t_fusion hy hy3
  rcases hc with rfl | rfl
  · have hA3 : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2
    left
    rw [hyeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hA3 he',
      ← j3t_caseA.1, j3t_caseA.2]
  · have hB3 : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2
    right
    rw [hyeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hB3 he',
      ← j3t_caseB.1, j3t_caseB.2]

theorem card_centralizer_of_equiv_J3_dichotomy {Q : Type*} [Group Q]
    (e : Q ≃* NativeSporadic.J3) {q : Q} (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1) :
    Nat.card (centralizer ({q} : Set Q)) = 1080 ∨ Nat.card (centralizer ({q} : Set Q)) = 243 := by
  have hcard2 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
    (e.trans Item228CensusProof.j3CarrierEquiv) q
  obtain ⟨y, hyy⟩ : ∃ y : Equiv.Perm (Fin 6156),
      y = ((e.trans Item228CensusProof.j3CarrierEquiv) q : ↥j3P) := ⟨_, rfl⟩
  have hyj : y ∈ j3P := hyy ▸ ((e.trans Item228CensusProof.j3CarrierEquiv) q).2
  have hy3 : orderOf y = 3 := by
    have h3 : y ^ 3 = 1 := by
      have := congrArg (fun z : ↥j3P => (z : Equiv.Perm (Fin 6156)))
        (show (e.trans Item228CensusProof.j3CarrierEquiv) q ^ 3 = 1 from
          (map_pow (e.trans Item228CensusProof.j3CarrierEquiv) q 3).symm.trans
            ((congrArg (e.trans Item228CensusProof.j3CarrierEquiv) hq3).trans (map_one _)))
      rw [hyy]
      simpa using this
    have h1 : y ≠ 1 := by
      intro h
      apply hq1
      have : (e.trans Item228CensusProof.j3CarrierEquiv) q = 1 := Subtype.ext (hyy ▸ h)
      exact ((map_eq_one_iff _ (e.trans Item228CensusProof.j3CarrierEquiv).injective).1 this)
    exact orderOf_eq_prime h3 h1
  rw [hcard2, ← hyy]
  exact card_centralizer_j3P_dichotomy hyj hy3

theorem factorization_card_J3_three : (Nat.card NativeSporadic.J3).factorization 3 = 5 := by
  have h : Nat.card NativeSporadic.J3 = Nat.card j3P :=
    Nat.card_congr Item228CensusProof.j3CarrierEquiv.toEquiv
  rw [h]
  exact CFSG.RankThree.PartTwo.KFacts.K426.factorization_card_j3P_three

theorem card_centralizer_of_nonCentral {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3) {q : Q}
    (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1)
    (hnc : ∀ S : Sylow 3 Q, q ∉ (Subgroup.center ↥(S : Subgroup Q)).map (S : Subgroup Q).subtype) :
    Nat.card (centralizer ({q} : Set Q)) = 1080 := by
  rcases card_centralizer_of_equiv_J3_dichotomy e hq3 hq1 with h | h
  · exact h
  · exfalso
    have hQ : (Nat.card Q).factorization 3 = 5 := by
      rw [Nat.card_congr e.toEquiv]; exact factorization_card_J3_three
    have h3 : Nat.card (centralizer ({q} : Set Q)) = 3 ^ (Nat.card Q).factorization 3 := by
      rw [h, hQ]; norm_num
    let S : Sylow 3 Q := Sylow.ofCard (centralizer ({q} : Set Q)) h3
    apply hnc S
    have hS : (S : Subgroup Q) = centralizer ({q} : Set Q) := Sylow.coe_ofCard _ _
    refine ⟨⟨q, ?_⟩, ?_, rfl⟩
    · rw [hS, Subgroup.mem_centralizer_singleton_iff]
    · rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      have hs : (s : Q) ∈ centralizer ({q} : Set Q) := hS ▸ s.2
      exact (Subgroup.mem_centralizer_singleton_iff.1 hs)

theorem five_dvd_centralizer_of_nonCentral {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* NativeSporadic.J3) {q : Q} (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1)
    (hnc : ∀ S : Sylow 3 Q, q ∉ (Subgroup.center ↥(S : Subgroup Q)).map (S : Subgroup Q).subtype) :
    5 ∣ Nat.card (centralizer ({e q} : Set NativeSporadic.J3)) := by
  have h1080 := card_centralizer_of_nonCentral e hq3 hq1 hnc
  have hcard1 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
    Item228CensusProof.j3CarrierEquiv (e q)
  have hcard2 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
    (e.trans Item228CensusProof.j3CarrierEquiv) q
  have hC : Nat.card (centralizer ({e q} : Set NativeSporadic.J3)) = 1080 := by
    have h3 : Nat.card (centralizer ({e q} : Set (NativeSporadic.Carrier .J3))) =
        Nat.card (centralizer ({q} : Set Q)) := hcard1.trans hcard2.symm
    exact h3.trans h1080
  rw [hC]
  norm_num

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
