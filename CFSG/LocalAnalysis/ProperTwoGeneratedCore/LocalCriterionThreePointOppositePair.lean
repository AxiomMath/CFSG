module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeTransport
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def oppositePairStabilizer (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) : Subgroup G :=
  rightCosetStabilizer H beta ⊓ rightCosetStabilizer H (rightCosetTranslate H beta z)

@[expose] def oppositePairOddCore [Finite G] (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) : Subgroup G :=
  (oddCore (oppositePairStabilizer H z beta)).map
    (oppositePairStabilizer H z beta).subtype

theorem original_pair_flip_exists [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    (rightPairFlipFiber H z beta).Nonempty := by
  have hzclass : z ∈ conjugacyWithin H z := by
    refine ⟨1, ?_⟩
    simp only [Subgroup.coe_one, inv_one, one_mul, mul_one]
  let : Nonempty (conjugacyWithin H z) := ⟨⟨z, hzclass⟩⟩
  have hpositive : 0 < Nat.card (conjugacyWithin H z) := Nat.card_pos
  by_contra hempty
  have heq : rightPairFlipFiber H z beta = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
  have hcard := (involution_point_uniform_pair_flips h beta hbeta).1
  rw [heq] at hcard
  have hzero : Nat.card (conjugacyWithin H z) = 0 := by
    simpa using hcard.symm
  omega

theorem triple_stabilizer_le_opposite_pair (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) :
    triplePointStabilizer H z beta ≤ oppositePairStabilizer H z beta :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem opposite_pair_z_centralizer_eq_triple
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) :
    oppositePairStabilizer H z beta ⊓ Subgroup.centralizer ({z} : Set G) =
      triplePointStabilizer H z beta ⊓ Subgroup.centralizer ({z} : Set G) := by
  apply le_antisymm
  · intro a ha
    refine ⟨⟨⟨?_, ha.1.1⟩, ha.1.2⟩, ha.2⟩
    rw [rightCosetStabilizer_base]
    exact point_centralizer_le h ha.2
  · exact inf_le_inf_right _ (triple_stabilizer_le_opposite_pair H z beta)

theorem opposite_pair_flip_class_card [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    Nat.card (conjugacyWithin (oppositePairStabilizer H z beta) z) =
      Nat.card (conjugacyWithin H z) := by
  refine Quotient.inductionOn' beta (fun x hbeta => ?_) hbeta
  let Hx := rightConjugate H x
  let beta₀ := rightCosetMk Hx z
  have hx := local_embedding_right_conjugate h x
  have hbeta₀ := opposite_point_ne_base h hbeta
  have hflip := distinguished_mem_opposite_pair_fiber H z x
  obtain ⟨T, _, hzT, hTcenter⟩ := central_sylow_right_conjugate S hzS hzcenter x
  have hcard := pair_stabilizer_t_centralizer_index_eq_class_card hx T hzT hTcenter
    hbeta₀ hflip
  rw [← conjugacyWithin_card_eq_centralizer_index, opposite_pair_stabilizer_eq] at hcard
  change Nat.card (conjugacyWithin (oppositePairStabilizer H z (rightCosetMk H x)) z) = _
  refine hcard.trans ?_
  simpa only [rightConjugate, Subgroup.conjBy, rightConjugateElem,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      conjugacyWithin_card_map_automorphism H z (MulAut.conj x⁻¹)

theorem opposite_pair_z_centralizer_index_eq_class_card [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    ((Subgroup.centralizer ({z} : Set G)).subgroupOf
      (oppositePairStabilizer H z beta)).index = Nat.card (conjugacyWithin H z) := by
  rw [← conjugacyWithin_card_eq_centralizer_index]
  exact opposite_pair_flip_class_card h S hzS hzcenter beta hbeta

theorem opposite_pair_eq_z_centralizer_mul_odd_core [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    (oppositePairStabilizer H z beta : Set G) =
      (oppositePairStabilizer H z beta ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
        (oppositePairOddCore H z beta : Set G) := by
  refine Quotient.inductionOn' beta (fun x hbeta => ?_) hbeta
  let Hx := rightConjugate H x
  let beta₀ := rightCosetMk Hx z
  let F := pairPointStabilizer Hx beta₀
  let K := pairFlipGroup Hx beta₀ z
  let J := pairOddCore Hx beta₀
  have hx := local_embedding_right_conjugate h x
  have hbeta₀ := opposite_point_ne_base h hbeta
  have hflip := distinguished_mem_opposite_pair_fiber H z x
  obtain ⟨T, _, hzT, hTcenter⟩ := central_sylow_right_conjugate S hzS hzcenter x
  have hfactor := (pair_flip_zStar_factorization hx T hzT hTcenter hbeta₀ hflip).2
  have hF : F = oppositePairStabilizer H z (rightCosetMk H x) :=
    opposite_pair_stabilizer_eq H x z
  have hJ : J = oppositePairOddCore H z (rightCosetMk H x) := by
    change (oddCore F).map F.subtype = _
    rw [hF]
    rfl
  change (oppositePairStabilizer H z (rightCosetMk H x) : Set G) =
    (oppositePairStabilizer H z (rightCosetMk H x) ⊓
      Subgroup.centralizer ({z} : Set G) : Set G) *
        (oppositePairOddCore H z (rightCosetMk H x) : Set G)
  rw [← hF, ← hJ]
  ext f
  constructor
  · intro hf
    obtain ⟨c, hc, j, hj, hfj⟩ := hfactor f
      (pairPointStabilizer_le_pairFlipGroup Hx beta₀ z hf)
    have hcF : c ∈ F := by
      have hm := F.mul_mem hf (F.inv_mem ((pairOddCore_le Hx beta₀ z).1 hj))
      rw [hfj] at hm
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hm
    exact Set.mem_mul.mpr ⟨c, ⟨hcF, hc.2⟩, j, hj, hfj.symm⟩
  · rintro hf
    obtain ⟨c, hc, j, hj, rfl⟩ := Set.mem_mul.mp hf
    exact F.mul_mem hc.1 ((pairOddCore_le Hx beta₀ z).1 hj)

theorem opposite_pair_eq_odd_core_mul_triple [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    (oppositePairStabilizer H z beta : Set G) =
      (oppositePairOddCore H z beta : Set G) * (triplePointStabilizer H z beta : Set G) := by
  let F := oppositePairStabilizer H z beta
  let J := oppositePairOddCore H z beta
  have hJF : J ≤ F := Subgroup.map_subtype_le _
  have hfactor := opposite_pair_eq_z_centralizer_mul_odd_core h S hzS hzcenter beta hbeta
  ext f
  constructor
  · intro hf
    have hinv : f⁻¹ ∈ (F : Set G) := F.inv_mem hf
    rw [hfactor] at hinv
    obtain ⟨c, hc, j, hj, hcj⟩ := Set.mem_mul.mp hinv
    have hcE : c ∈ triplePointStabilizer H z beta := by
      change c ∈ oppositePairStabilizer H z beta ⊓ Subgroup.centralizer ({z} : Set G) at hc
      rw [opposite_pair_z_centralizer_eq_triple h beta] at hc
      exact hc.1
    refine Set.mem_mul.mpr ⟨j⁻¹, J.inv_mem hj, c⁻¹,
      (triplePointStabilizer H z beta).inv_mem hcE, ?_⟩
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv hcj
  · intro hf
    obtain ⟨j, hj, e, he, rfl⟩ := Set.mem_mul.mp hf
    exact F.mul_mem (hJF hj) (triple_stabilizer_le_opposite_pair H z beta he)

theorem opposite_pair_order_eq_pair [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    Nat.card (oppositePairStabilizer H z beta) = Nat.card (pairPointStabilizer H beta) := by
  obtain ⟨t, ht⟩ := original_pair_flip_exists h beta hbeta
  let C := Subgroup.centralizer ({z} : Set G)
  have hF := C.relIndex_mul_card (oppositePairStabilizer H z beta)
  have hB := C.relIndex_mul_card (pairPointStabilizer H beta)
  change ((C.subgroupOf (oppositePairStabilizer H z beta)).index) *
    Nat.card (C ⊓ oppositePairStabilizer H z beta : Subgroup G) = _ at hF
  change ((C.subgroupOf (pairPointStabilizer H beta)).index) *
    Nat.card (C ⊓ pairPointStabilizer H beta : Subgroup G) = _ at hB
  rw [opposite_pair_z_centralizer_index_eq_class_card h S hzS hzcenter beta hbeta,
    inf_comm C, opposite_pair_z_centralizer_eq_triple h beta,
    triple_z_centralizer_eq_pair] at hF
  rw [pair_stabilizer_z_centralizer_index_eq_class_card h S hzS hzcenter hbeta ht,
    inf_comm C] at hB
  exact hF.symm.trans hB

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
