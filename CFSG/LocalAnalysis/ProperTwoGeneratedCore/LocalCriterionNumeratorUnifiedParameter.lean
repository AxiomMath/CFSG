module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeFamily
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeRootLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorCentralizerAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_whole_root_at_supplied_quotient_root
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u))
    (V : Subgroup (localInvolutionPointHull z u ⧸ CFSG.oddCore (localInvolutionPointHull z u)))
    (hV : IsElementaryAbelian 2 V)
    (hVset : (V : Set (localInvolutionPointHull z u ⧸ CFSG.oddCore (localInvolutionPointHull z u))) =
      {1} ∪ {x | x ∈ (H.subgroupOf (localInvolutionPointHull z u)).map
        (QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z u))) ∧ IsInvolution x}) :
    let L := localInvolutionPointHull z u
    let U := originalPointRoot H z u
    IsElementaryAbelian 2 U ∧ U ≤ H ⊓ L ∧
      (U : Set G) = {1} ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)) ∧
      Nat.card U = Nat.card V ∧
      U ≤ H ⊓ Subgroup.centralizer ({u} : Set G) ∧
      (U.subgroupOf (H ⊓ Subgroup.centralizer ({u} : Set G))).Normal ∧
      (∀ (x y : G), x ∈ U → x ≠ 1 → y ∈ U → y ≠ 1 →
        ∃ g : G, g ∈ H ⊓ Subgroup.centralizer ({u} : Set G) ∧
          rightConjugateElem x g = y) := by
  let L := localInvolutionPointHull z u
  let f := QuotientGroup.mk' (CFSG.oddCore L)
  let B := (H.subgroupOf L).map f
  have hP := h.local_embedding u hu huz hescape
  have hodd : Odd (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card L
  have hkercentral : f.ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
    exact hcentral
  obtain ⟨A, hAelem, hAle, hAset, hAcard⟩ :=
    original_whole_point_root_of_central_odd_surjection h u huz hP f
      (QuotientGroup.mk'_surjective (CFSG.oddCore L)) hodd hkercentral B V rfl hV hVset
  have hroot := originalPointRoot_eq_of_whole_set H z u A hAset
  have hnormal := original_whole_point_root_normal_in_point_centralizer H z u A hAset
  have htrans : ∀ (x y : G), x ∈ A → x ≠ 1 → y ∈ A → y ≠ 1 →
      ∃ g : G, g ∈ H ⊓ Subgroup.centralizer ({u} : Set G) ∧ rightConjugateElem x g = y := by
    intro x y hx hxone hy hyone
    have hxset : x ∈ {1} ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)) :=
      hAset ▸ hx
    have hyset : y ∈ {1} ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)) :=
      hAset ▸ hy
    exact original_point_centralizer_transitive_distinguished_set h u huz hP x y
      (hxset.resolve_left (fun hx => hxone (Set.mem_singleton_iff.mp hx)))
      (hyset.resolve_left (fun hy => hyone (Set.mem_singleton_iff.mp hy)))
  dsimp only
  rw [hroot]
  exact ⟨hAelem, hAle, hAset, hAcard, hnormal.1, hnormal.2, htrans⟩

theorem original_native_root_degree_and_full_action_of_central_oddCore
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let Y := Subgroup.centralizer ({u} : Set G)
    let F := L ⧸ CFSG.oddCore L
    let f := QuotientGroup.mk' (CFSG.oddCore L)
    let B := (H.subgroupOf L).map f
    let U := originalPointRoot H z u
    letI := hullFixedSetAction H z u
    letI := originalCentralizerFixedSetAction H u
    IsSimpleBenderGroup F ∧ IsBorelSubgroup B ∧
      CFSG.oddCore L ≤ H.subgroupOf L ∧
      elementFixedSet H u = numeratorRightOrbit H L (rightCosetMk H 1) ∧
      ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        IsSimpleBenderGroupAtExponent a F ∧
        IsElementaryAbelian 2 U ∧ U ≤ H ⊓ L ∧
        (U : Set G) = {1} ∪
          (involutionPointClass z ∩ (Y : Set G) ∩ (H : Set G)) ∧
        Nat.card U = 2 ^ a ∧ 4 ≤ Nat.card U ∧
        B.index = (Nat.card U) ^ i + 1 ∧
        Nat.card (elementFixedSet H u) = (Nat.card U) ^ i + 1 ∧
        U ≤ H ⊓ Y ∧ (U.subgroupOf (H ⊓ Y)).Normal ∧
        (∀ (x y : G), x ∈ U → x ≠ 1 → y ∈ U → y ≠ 1 →
          ∃ g : G, g ∈ H ⊓ Y ∧ rightConjugateElem x g = y) ∧
        (∃ phi : elementFixedSet H u ≃ (F ⧸ B),
          (∀ y : elementFixedSet H u, y.val = rightCosetMk H 1 →
            phi y = QuotientGroup.mk 1) ∧
          ∀ (l : L) (y : elementFixedSet H u), phi (l • y) = f l • phi y) ∧
        MulAction.IsMultiplyPretransitive L (elementFixedSet H u) 2 ∧
        MulAction.IsMultiplyPretransitive Y (elementFixedSet H u) 2 ∧
        ((i = 1 ∧ Nonempty (F ≃* PSL2BinaryMatrixGroup a)) ∨
          (i = 2 ∧ ∃ m : ℕ, a = 2 * m + 1 ∧ Nonempty (F ≃* SuzukiMatrixGroup m)) ∨
          (i = 3 ∧ ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
            J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
            Nat.card E = (2 ^ a) ^ 2 ∧
            Nat.card {x : E // J.conj x = x} = 2 ^ a ∧
            Nonempty (F ≃* ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let L := localInvolutionPointHull z u
  let Y := Subgroup.centralizer ({u} : Set G)
  let F := L ⧸ CFSG.oddCore L
  let f := QuotientGroup.mk' (CFSG.oddCore L)
  let B := (H.subgroupOf L).map f
  let V := Subgroup.closure {x : F | x ∈ B ∧ IsInvolution x}
  let U := originalPointRoot H z u
  let := hullFixedSetAction H z u
  let := originalCentralizerFixedSetAction H u
  obtain ⟨hmodel, hcore, hB, hfull, a, i, ha, hi, hAt, helemV, _hVB, hVset,
    hVcard, hVfour, hindex, hcard, hphi, hdouble⟩ :=
    original_central_sylow_native_fixedSet_model h S hzS hzcenter u huH hu huz hescape hrank
  obtain ⟨helemU, hUle, hUset, hUVcard, hUY, hUnormal, hUtrans⟩ :=
    original_whole_root_at_supplied_quotient_root h u hu huz hescape hcentral V helemV hVset
  have hUcard : Nat.card U = 2 ^ a := hUVcard.trans hVcard
  have hfamily := native_family_matches_exact_borel_degree a i ha hAt B hB hindex
  refine ⟨hmodel, hB, hcore, hfull, a, i, ha, hi, hAt, helemU, hUle, hUset,
    hUcard, hUVcard.symm ▸ hVfour, ?_, ?_, hUY, hUnormal, hUtrans, hphi,
    hdouble, original_centralizer_two_pretransitive_of_hull H z u hdouble, hfamily⟩
  · rw [hUcard]
    exact hindex
  · rw [hUcard]
    exact hcard

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
