module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalSylowFusion

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

universe v

variable {G : Type v} [Group G] [Finite G]

omit [Finite G] in
theorem original_root_le_supplied_sylow_of_complete_partition
    {H : Subgroup G} {z u : G}
    (T1 : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hpartition : {x : G | x ∈
        (T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
          (Subgroup.centralizer ({u} : Set G)).subtype ∧ orderOf x = 2} =
      ({u} : Set G) ∪ {w : G | w ∈ originalPointRoot H z u ∧ w ≠ 1} ∪
        (fun w : G => u * w) '' {w : G | w ∈ originalPointRoot H z u ∧ w ≠ 1}) :
    originalPointRoot H z u ≤
      (T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype := by
  intro w hw
  by_cases hwone : w = 1
  · exact hwone ▸ Subgroup.one_mem _
  · have hwpartition : w ∈ ({u} : Set G) ∪
        {v : G | v ∈ originalPointRoot H z u ∧ v ≠ 1} ∪
        (fun v : G => u * v) '' {v : G | v ∈ originalPointRoot H z u ∧ v ≠ 1} :=
      Or.inl (Or.inr ⟨hw, hwone⟩)
    rw [← hpartition] at hwpartition
    exact hwpartition.1

theorem original_native_full_index_of_central_oddCore_and_complete_sylow_partition
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hfour : ¬ TwoRankAtLeastTwo (pairPointStabilizer H beta))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u))
    (T1 : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hpartition : {x : G | x ∈
        (T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
          (Subgroup.centralizer ({u} : Set G)).subtype ∧ orderOf x = 2} =
      ({u} : Set G) ∪ {w : G | w ∈ originalPointRoot H z u ∧ w ≠ 1} ∪
        (fun w : G => u * w) '' {w : G | w ∈ originalPointRoot H z u ∧ w ≠ 1}) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let P := L ⊓ H
    let U := cosetUnitSet H z u
    let q := Nat.card U
    let Gamma := cosetFixedSet H u
    let k := Nat.card Gamma
    let D := pairPointStabilizer H beta
    let Delta := involutionPointClass u ∩
      (((T1 : Subgroup M).map M.subtype : Subgroup G) : Set G)
    let N := Subgroup.normalizer Delta
    let F := L ⧸ CFSG.oddCore L
    let B := (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.oddCore L))
    u * z ∈ involutionPointClass u ∧
      L ≤ M ∧ P = L ⊓ H ∧ IsSimpleBenderGroup F ∧ IsBorelSubgroup B ∧
      CFSG.oddCore L ≤ H.subgroupOf L ∧
      ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        IsSimpleBenderGroupAtExponent a F ∧ q = 2 ^ a ∧ 4 ≤ q ∧ k = q ^ i + 1 ∧
        IsElementaryAbelian 2 (originalPointRoot H z u) ∧
        originalPointRoot H z u ≤ H ⊓ L ∧
        ((originalPointRoot H z u : Subgroup G) : Set G) = U ∧
        Delta = (fun v : G => u * v) '' U ∧
        Delta ∩ (D : Set G) = {u} ∧ N ≤ H ∧
        N ⊓ D = (N ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ D ∧
        (∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype ≤ N ⊓ D) ∧
        D.relIndex N = q * (k - 1) ∧
        (∀ S : Sylow 2 N, D.relIndex ((S : Subgroup N).map N.subtype) = q * (k - 1)) ∧
        q * (k - 1) ∣ Nat.card (pointRightCosetSpace H) - 1 ∧
        (Nat.card (pointRightCosetSpace H) - 1 = q * (k - 1) →
          ∀ S : Sylow 2 N, ∃ R : Sylow 2 G,
            (R : Subgroup G) = (S : Subgroup N).map N.subtype) := by
  obtain ⟨S0, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨_hmodel, _hcore, _hB, _hodd, _hfull, a, i, ha, hi, hAt, helem,
      _hUle, hUset, _hq, _hqfour, _hk, _hBindex, _e, _hbase, _he⟩ :=
    original_native_parameter_and_action_of_central_oddCore
      h.local_datum S0 hzS hzcenter u
      (pairPointStabilizer_le_point H beta huD) hu huz hescape hrank hcentral
  have hUT := original_root_le_supplied_sylow_of_complete_partition T1 hpartition
  obtain ⟨hfused, hDelta⟩ := original_supplied_sylow_entire_class_intersection
    h beta hb huD hu huz hescape (originalPointRoot H z u) hUset helem T1 hUT hpartition
  have hcoverage : ∀ x : G,
      x ∈ (T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype → IsInvolution x →
      x ∈ originalPointRoot H z u ∨ x ∈ translatedCosetUnitSet H z u := by
    intro x hx hxI
    have hxorder : orderOf x = 2 := orderOf_eq_prime_iff.mpr ⟨hxI.2, hxI.1⟩
    have hxpartition : x ∈ ({u} : Set G) ∪
        {w : G | w ∈ originalPointRoot H z u ∧ w ≠ 1} ∪
        (fun w : G => u * w) '' {w : G | w ∈ originalPointRoot H z u ∧ w ≠ 1} :=
      hpartition ▸ (show x ∈ {v : G | v ∈
        (T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
          (Subgroup.centralizer ({u} : Set G)).subtype ∧ orderOf v = 2} from ⟨hx, hxorder⟩)
    rcases hxpartition with (hxbase | hxroot) | hxtranslate
    · right
      rw [Set.mem_singleton_iff.mp hxbase]
      exact ⟨1, Or.inl (Set.mem_singleton 1), mul_one u⟩
    · exact Or.inl hxroot.1
    · right
      obtain ⟨w, hw, rfl⟩ := hxtranslate
      exact ⟨w, hUset ▸ hw.1, rfl⟩
  exact ⟨hfused, original_native_full_index_of_central_oddCore_and_sylow_geometry
    h hcomm beta hb huD hu huz hescape hrank hfour hcentral T1 hcoverage hDelta⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
