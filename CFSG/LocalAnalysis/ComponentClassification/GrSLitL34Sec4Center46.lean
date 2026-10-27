module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

theorem l34Lemma46CenterStep_of_inputs (hCF1 : L34CenterNoncyclicFact)
    (hCF2 : L34SylowCentralizerFact) : L34Lemma46CenterStep := by
  intro G _ _ a x J S A hset hcent hZ hrun h3 hexp hcyc s hsS hsZ j hj
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  set P : Subgroup G := S ⊓ J with hPdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hsN : s ∈ normalizer (J : Set G) := hS.1 hsS
  have hsP : ∀ p ∈ P, s * p = p * s := fun p hp => hsZ p (mem_inf.mp hp).1
  obtain ⟨u, huP, hvK, -⟩ := hCF2 G J P s hJper hL34 hP hsN hsP
  have huS : u ∈ S := (mem_inf.mp huP).1
  have huJ : u ∈ J := (mem_inf.mp huP).2
  have hvN : u⁻¹ * s ∈ normalizer (J : Set G) := mul_mem (inv_mem (le_normalizer huJ)) hsN
  have hvS : u⁻¹ * s ∈ S := mul_mem (inv_mem huS) hsS
  have hvP : ∀ p ∈ P, (u⁻¹ * s) * p = p * (u⁻¹ * s) := by
    intro p hp
    have hpS : p ∈ S := (mem_inf.mp hp).1
    have h1 : p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s) ∈ oddIn J :=
      (mem_coreActionKernel.mp hvK).2 p (mem_inf.mp hp).2
    have h2 : p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s) ∈ S :=
      mul_mem (mul_mem (mul_mem (inv_mem hpS) (inv_mem hvS)) hpS) hvS
    have h3 := eq_bot_of_le_two_group_of_le_odd (isPGroup_of_isSylowTwoIn hS)
      (odd_card_map_pPrimeCore J) (zpowers_le.mpr h2) (zpowers_le.mpr h1)
    have h4 : p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s) = 1 := by
      have h5 := mem_zpowers (p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s))
      rwa [h3, mem_bot] at h5
    calc (u⁻¹ * s) * p = (u⁻¹ * s) * p * (p⁻¹ * (u⁻¹ * s)⁻¹ * p * (u⁻¹ * s)) := by
          rw [h4, mul_one]
      _ = p * (u⁻¹ * s) := by group
  have huc : ∀ p ∈ P, u * p = p * u := by
    intro p hp
    have h1 := hsP p hp
    have h2 := hvP p hp
    have hv' : (u⁻¹ * s)⁻¹ * p = p * (u⁻¹ * s)⁻¹ := by
      calc (u⁻¹ * s)⁻¹ * p = (u⁻¹ * s)⁻¹ * (p * (u⁻¹ * s)) * (u⁻¹ * s)⁻¹ := by group
        _ = (u⁻¹ * s)⁻¹ * ((u⁻¹ * s) * p) * (u⁻¹ * s)⁻¹ := by rw [← h2]
        _ = p * (u⁻¹ * s)⁻¹ := by group
    calc u * p = s * ((u⁻¹ * s)⁻¹ * p) := by group
      _ = s * (p * (u⁻¹ * s)⁻¹) := by rw [hv']
      _ = (s * p) * (u⁻¹ * s)⁻¹ := by group
      _ = (p * s) * (u⁻¹ * s)⁻¹ := by rw [h1]
      _ = p * u := by group
  have huZ : u ∈ zStarIn J := by
    have hcen : u ∈ P ⊓ centralizer (P : Set G) :=
      mem_inf.mpr ⟨huP, mem_centralizer_iff.mpr fun p hp => (huc p hp).symm⟩
    rw [hCF1 G J P hJper hL34 hP (by rwa [hZP])
      (by rw [hZP]; exact exists_sq_ne_one_of_exponent_eq_four hexp)] at hcen
    exact (mem_inf.mp hcen).2
  rw [show j⁻¹ * s⁻¹ * j * s = (j⁻¹ * (u⁻¹ * s)⁻¹ * j * (u⁻¹ * s)) *
    ((u⁻¹ * s)⁻¹ * (j⁻¹ * u⁻¹ * j * u) * (u⁻¹ * s)⁻¹⁻¹) by group]
  refine mul_mem (oddIn_le_zStarIn J ((mem_coreActionKernel.mp hvK).2 j hj)) ?_
  have huj : j⁻¹ * u⁻¹ * j * u ∈ zStarIn J := by
    have h1 := conj_mem_zStarIn (le_normalizer (inv_mem hj)) (inv_mem huZ)
    rw [inv_inv] at h1
    exact mul_mem h1 huZ
  exact conj_mem_zStarIn (inv_mem hvN) huj

end CFSG.ComponentClassification.GrSLit
