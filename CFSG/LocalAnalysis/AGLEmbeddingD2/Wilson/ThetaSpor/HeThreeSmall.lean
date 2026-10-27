
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeCheckBase

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

open CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert

theorem bigDataA :
    BigData 35 4 heThreeWordsA heThreeSigmaA heThreeDeltaA 77 := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨hl, hg⟩, ⟨hi, hf, -⟩⟩ := heThree_bigA
  exact ⟨h1, h2, h3, h4, h5, h6, hl, hg, hi, hf⟩

theorem bigDataB :
    BigData 8 4 heThreeWordsB heThreeSigmaB heThreeDeltaB 8 := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨hl, hg⟩, ⟨hi, hf, -⟩⟩ := heThree_bigB
  exact ⟨h1, h2, h3, h4, h5, h6, hl, hg, hi, hf⟩

theorem toArray_get_left (sigma : List (Array ℕ)) (f : Array ℕ → Array ℕ) (l : ℕ)
    (hl : l < sigma.length) : (sigma ++ sigma.map f).toArray[l]! = sigma[l] := by
  simp [List.getElem!_toArray, List.getElem?_append_left hl, hl]

theorem toArray_get_right (sigma : List (Array ℕ)) (f : Array ℕ → Array ℕ) (l : ℕ)
    (hl : sigma.length ≤ l) (hl2 : l < 2 * sigma.length) :
    (sigma ++ sigma.map f).toArray[l]! = f (sigma[l - sigma.length]'(by omega)) := by
  have h1 : l - sigma.length < sigma.length := by omega
  simp [List.getElem!_toArray, List.getElem?_append_right hl, h1]

theorem lettersIn_sigma {m k : ℕ} {sigma : List (Array ℕ)} (hlen : sigma.length = k)
    (hperm : ∀ j < k, permChk m (sigma.getD j #[]) = true) {G : Subgroup (Equiv.Perm (Fin m))}
    (hG : ∀ j < k, permOrId m (sigma.getD j #[]) ∈ G) :
    LettersIn G (sigma ++ sigma.map (invCand m)).toArray := by
  intro l hl
  have hl' : l < 2 * k := by simpa [hlen, two_mul] using hl
  by_cases hlk : l < k
  · have hl1 : l < sigma.length := hlen ▸ hlk
    refine ⟨permOrId m (sigma.getD l #[]), hG l hlk, fun x => ?_⟩
    rw [toArray_get_left sigma _ l hl1]
    have e : sigma[l] = sigma.getD l #[] := (List.getD_eq_getElem _ _ hl1).symm
    rw [e]
    exact (permChk_spec (hperm l hlk)).1 x
  · have hl1 : sigma.length ≤ l := hlen ▸ not_lt.1 hlk
    have hj : l - k < k := by omega
    have hj1 : l - sigma.length < sigma.length := by omega
    refine ⟨(permOrId m (sigma.getD (l - k) #[]))⁻¹, G.inv_mem (hG _ hj), fun x => ?_⟩
    rw [toArray_get_right sigma _ l hl1 (by omega)]
    have e : sigma[l - sigma.length] = sigma.getD (l - k) #[] := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp [hlen]
    rw [e]
    exact (permChk_spec (hperm (l - k) hj)).2 x

theorem heThreeSigmaA_length : heThreeSigmaA.length = 4 := rfl

theorem heThreeSigmaB_length : heThreeSigmaB.length = 4 := rfl

theorem heThreeXA_eq :
    heThreeXA.originalSubgroup =
      Subgroup.closure {g | ∃ j < 4, permOrId 35 (heThreeSigmaA.getD j #[]) = g} := by
  rw [heThreeXA, certificate_originalSubgroup]
  congr 1
  ext g
  simp only [List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    refine ⟨j, heThreeSigmaA_length ▸ hj, ?_⟩
    rw [List.getD_eq_getElem _ _ hj]
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < heThreeSigmaA.length := heThreeSigmaA_length ▸ hj
    exact ⟨_, List.getElem_mem hj', by rw [List.getD_eq_getElem _ _ hj']⟩

theorem heThreeXB_eq :
    heThreeXB.originalSubgroup =
      Subgroup.closure {g | ∃ j < 4, permOrId 8 (heThreeSigmaB.getD j #[]) = g} := by
  rw [heThreeXB, certificate_originalSubgroup]
  congr 1
  ext g
  simp only [List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    refine ⟨j, heThreeSigmaB_length ▸ hj, ?_⟩
    rw [List.getD_eq_getElem _ _ hj]
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < heThreeSigmaB.length := heThreeSigmaB_length ▸ hj
    exact ⟨_, List.getElem_mem hj', by rw [List.getD_eq_getElem _ _ hj']⟩

theorem card_heThreeXA :
    Nat.card heThreeXA.originalSubgroup = 2520 := by
  rw [← heThreeXA.orderCertificate_eq_card heThree_smallA.1, heThree_smallA.2.1]

theorem card_heThreeXB :
    Nat.card heThreeXB.originalSubgroup = 168 := by
  rw [← heThreeXB.orderCertificate_eq_card heThree_smallB.1, heThree_smallB.2.1]

theorem lettersInA :
    LettersIn heThreeXA.originalSubgroup heThreeLettersA :=
  lettersIn_sigma heThreeSigmaA_length (fun j hj => (bigDataA.gens j hj).2.2.2.1) (fun j hj => by
    rw [heThreeXA_eq]
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩)

theorem lettersInB :
    LettersIn heThreeXB.originalSubgroup heThreeLettersB :=
  lettersIn_sigma heThreeSigmaB_length (fun j hj => (bigDataB.gens j hj).2.2.2.1) (fun j hj => by
    rw [heThreeXB_eq]
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩)

theorem preprimitiveA :
    MulAction.IsPreprimitive heThreeXA.originalSubgroup (Fin 35) :=
  isPreprimitive_of_primOK lettersInA heThree_smallA.2.2

theorem preprimitiveB :
    MulAction.IsPreprimitive heThreeXB.originalSubgroup (Fin 8) :=
  isPreprimitive_of_primOK lettersInB heThree_smallB.2.2.1

theorem not_isPrimePow_35 : ¬ IsPrimePow 35 := by
  rw [isPrimePow_iff_unique_prime_dvd]
  rintro ⟨p, ⟨hp, hpd⟩, hu⟩
  have h5 := hu 5 ⟨by norm_num, by norm_num⟩
  have h7 := hu 7 ⟨by norm_num, by norm_num⟩
  omega

theorem radA :
    ∀ K : Subgroup heThreeXA.originalSubgroup, K.Normal → Group.IsSolvable K → K = ⊥ := by
  intro K hn hs
  have := preprimitiveA
  exact eq_bot_of_normal_solvable_of_not_isPrimePow _ not_isPrimePow_35 K

theorem radB :
    ∀ K : Subgroup heThreeXB.originalSubgroup, K.Normal → Group.IsSolvable K → K = ⊥ := by
  intro K hn hs
  have := preprimitiveB
  obtain ⟨g, hg, hg4, hg2⟩ := exists_order_four lettersInB heThree_smallB.2.2.2
  refine eq_bot_of_normal_solvable_of_order_four (n := 8) _ (by norm_num) (u := 21)
    (by decide) ?_ ⟨g, hg⟩ (Subtype.ext (by simpa using hg4)) (fun h => hg2 (by
      simpa using congrArg Subtype.val h)) K
  rw [card_heThreeXB]

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

end
