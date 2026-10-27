module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOddKernelFull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_local_hull_entire_oddCore_eq_center
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z)
    (hescape : ¬ Subgroup.centralizer ({w} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z w)) :
    CFSG.oddCore (localInvolutionPointHull z w) =
      Subgroup.center (localInvolutionPointHull z w) := by
  let L := localInvolutionPointHull z w
  let R := CFSG.oddCore L
  have hcentral : R ≤ Subgroup.center L :=
    original_local_hull_entire_oddCore_central h hcomm hsmallerR1 w hw hwz hescape hrank
  have hmodel := (original_local_hull_native_model_and_borel
    h.local_datum w hw hwz hescape hrank).1
  have hcenter : Subgroup.center (L ⧸ R) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_not_commutative hmodel.isSimple hmodel.not_commutative
  apply le_antisymm hcentral
  intro a ha
  let q := QuotientGroup.mk' R
  have hqa : q a ∈ Subgroup.center (L ⧸ R) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
    simpa only [map_mul] using congrArg q (Subgroup.mem_center_iff.mp ha x)
  rw [hcenter] at hqa
  exact (QuotientGroup.eq_one_iff a).mp (Subgroup.mem_bot.mp hqa)

theorem original_rank_two_hull_cyclic_inversion_torus
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z w)) :
    let L := localInvolutionPointHull z w
    ∃ a : ℕ, 2 ≤ a ∧ IsSimpleBenderGroupAtExponent a (L ⧸ CFSG.oddCore L) ∧
      ∃ J : Subgroup G,
        (J : Set G) = {x : G | x ∈ H ⊓ rightConjugate H t ∧
          rightConjugateElem x t = x⁻¹ ∧ x ∈ L} ∧
        IsCyclic J ∧ Nat.card J = 2 ^ a - 1 := by
  let L := localInvolutionPointHull z w
  have htorder : orderOf t = 2 := order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1
  have htinv : IsInvolution t :=
    ⟨(orderOf_eq_prime_iff.mp htorder).2, (orderOf_eq_prime_iff.mp htorder).1⟩
  have htH : t ∉ H := pair_flip_not_mem_point hbeta ht
  have htL : t ∈ L := Subgroup.subset_closure
    ⟨ht.1, Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm.eq⟩
  have hescape : ¬ Subgroup.centralizer ({w} : Set G) ≤ H :=
    fun hle => htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm.eq))
  obtain ⟨hmodel, hcore, hB⟩ :=
    original_local_hull_native_model_and_borel h.local_datum w hw hwz hescape hrank
  obtain ⟨a, ha, hmodelAt⟩ := hmodel.exists_exponent
  have hRcenter : twoPrimeCore L = Subgroup.center L := by
    rw [← oddCore_eq_twoPrimeCore]
    exact original_local_hull_entire_oddCore_eq_center h hcomm hsmallerR1
      w hw hwz hescape hrank
  have hcoreH : (twoPrimeCore L).map L.subtype ≤ H := by
    rw [← oddCore_eq_twoPrimeCore]
    exact (Subgroup.map_le_iff_le_comap).mpr hcore
  have hpoint : (L ⊓ H).subgroupOf L = H.subgroupOf L := by
    ext x
    change ((x : G) ∈ L ∧ (x : G) ∈ H) ↔ (x : G) ∈ H
    exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
  let e : (L ⧸ CFSG.oddCore L) ≃* (L ⧸ twoPrimeCore L) :=
    QuotientGroup.quotientMulEquivOfEq (oddCore_eq_twoPrimeCore (G := L))
  have hqcomp : e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore L)) =
      QuotientGroup.mk' (twoPrimeCore L) := by
    apply MonoidHom.ext
    intro x
    exact QuotientGroup.quotientMulEquivOfEq_mk (oddCore_eq_twoPrimeCore (G := L)) x
  have hBmap :
      ((H.subgroupOf L).map (QuotientGroup.mk' (CFSG.oddCore L))).map
        e.toMonoidHom =
      ((L ⊓ H).subgroupOf L).map (QuotientGroup.mk' (twoPrimeCore L)) := by
    rw [Subgroup.map_map, hqcomp, hpoint]
  have hBorel : IsBorelSubgroup
      (((L ⊓ H).subgroupOf L).map (QuotientGroup.mk' (twoPrimeCore L))) := by
    rw [← hBmap]
    exact hB.map_mulEquiv e
  have hAt : IsSimpleBenderGroupAtExponent a (L ⧸ twoPrimeCore L) := by
    rcases hmodelAt with ⟨hlinear⟩ | ⟨⟨m, hm, hsuzuki⟩⟩ |
        ⟨⟨E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, hunitary⟩⟩
    · exact IsSimpleBenderGroupAtExponent.isPSL2 ⟨e.symm.trans hlinear.some⟩
    · exact IsSimpleBenderGroupAtExponent.isSuzuki ⟨m, hm, ⟨e.symm.trans hsuzuki.some⟩⟩
    · exact IsSimpleBenderGroupAtExponent.isPSU3
        ⟨E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, ⟨e.symm.trans hunitary.some⟩⟩
  obtain ⟨J, hJset, hJcyclic, hJcard⟩ :=
    proposition84_base_cyclicNormalizer_of_borel_model H L L t htinv htH htL
      le_rfl hRcenter hcoreH hBorel a ha hAt (fun _ hx => hx.2)
  refine ⟨a, ha, hmodelAt, J, ?_, hJcyclic, hJcard⟩
  simpa only [peterfalviKSet, Set.mem_ofPred_eq, and_assoc] using hJset

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
