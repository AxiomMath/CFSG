module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexUnitAffine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOddKernelFull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorUnifiedParameter

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

universe v

variable {G : Type v} [Group G]

theorem originalPointRoot_le_entire_hull (H : Subgroup G) (z u : G) :
    originalPointRoot H z u ≤ localInvolutionPointHull z u :=
  Subgroup.closure_mono fun _ hx => hx.1

theorem originalPointRoot_entire_commutes_u (H : Subgroup G) (z u : G) :
    ∀ x ∈ originalPointRoot H z u, Commute u x := by
  intro x hx
  exact (show Commute x u from Subgroup.mem_centralizer_singleton_iff.mp
    (localInvolutionPointHull_le_centralizer z u
      (originalPointRoot_le_entire_hull H z u hx))).symm

theorem original_entire_hull_centralizer_le_root_centralizer
    (H : Subgroup G) (z u : G) :
    Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z u : Set G) ≤
      Subgroup.centralizer (originalPointRoot H z u : Set G) :=
  inf_le_right.trans
    (Subgroup.centralizer_le (originalPointRoot_le_entire_hull H z u))

theorem original_entire_hull_centralizer_le_entire_coset_centralizer
    (H : Subgroup G) (z u : G) :
    Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z u : Set G) ≤
      Subgroup.centralizer
        ((fun x : G => u * x) '' (originalPointRoot H z u : Set G)) := by
  rw [unit_translate_entire_centralizer]
  exact le_inf inf_le_left (original_entire_hull_centralizer_le_root_centralizer H z u)

theorem original_entire_hull_centralizer_le_affine_kernel
    (H : Subgroup G) (z u : G) (hu : u * u = 1) :
    let U := originalPointRoot H z u
    let N := Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))
    let K := Subgroup.centralizer ({u} : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z u : Set G)
    K.subgroupOf N ≤
      (unitAffineHom U u hu (originalPointRoot_entire_commutes_u H z u)).ker := by
  dsimp only
  rw [unitAffineHom_ker]
  intro n hn
  exact ⟨hn.1, original_entire_hull_centralizer_le_root_centralizer H z u hn⟩

variable [Finite G]

theorem original_native_affine_whole_root_and_kernel_of_original_rank_data
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type v) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let U := originalPointRoot H z u
    let Gamma := elementFixedSet H u
    let R := CFSG.oddCore L
    let K := M ⊓ Subgroup.centralizer (L : Set G)
    let Delta := (fun x : G => u * x) '' (U : Set G)
    let N := Subgroup.normalizer Delta
    let hu2 : u * u = 1 := by
      simpa only [pow_two] using (orderOf_eq_prime_iff.mp hu).1
    let hUcentral := originalPointRoot_entire_commutes_u H z u
    let f := unitAffineHom U u hu2 hUcentral
    R ≤ Subgroup.center L ∧ Odd (Nat.card R) ∧
      IsElementaryAbelian 2 U ∧ (U : Set G) = cosetUnitSet H z u ∧
      Delta = translatedCosetUnitSet H z u ∧ N ≤ H ∧
      N ⊓ M = M ⊓ H ∧
      f.ker = (M ⊓ Subgroup.centralizer (U : Set G)).subgroupOf N ∧
      f.ker.map N.subtype = M ⊓ Subgroup.centralizer (U : Set G) ∧
      K ≤ Subgroup.centralizer Delta ∧ K.subgroupOf N ≤ f.ker ∧
      (Subgroup.centralizer Delta).relIndex N = Nat.card f.range ∧
      (∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        Nat.card U = 2 ^ a ∧ 4 ≤ Nat.card U ∧
        Nat.card Gamma = (Nat.card U) ^ i + 1 ∧
        IsSimpleBenderGroupAtExponent a (L ⧸ R)) := by
  let L := localInvolutionPointHull z u
  have hcentral := original_local_hull_entire_oddCore_central
    h hcomm hsmallerR1 u hu huz hescape hrank
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨_hmodel, _hB, _hcore, _hfixed, a, i, ha, hi, hAt, hUelem,
      _hUle, hUset, hUcard, hUfour, _hBindex, hGammacard, _hUY,
      _hUnormal, _hUtrans, _hphi, _hLdouble, _hMdouble, _hfamily⟩ :=
    original_native_root_degree_and_full_action_of_central_oddCore h.local_datum
      S hzS hzcenter u huH hu huz hescape hrank hcentral
  have hDelta : (fun x : G => u * x) '' (originalPointRoot H z u : Set G) =
      translatedCosetUnitSet H z u := by
    rw [hUset]
    rfl
  dsimp only
  refine ⟨hcentral, CFSG.ComponentClassification.OddCore.odd_card L,
    hUelem, hUset, hDelta, ?_, ?_, ?_, ?_,
    original_entire_hull_centralizer_le_entire_coset_centralizer H z u,
    original_entire_hull_centralizer_le_affine_kernel H z u _, ?_,
    a, i, ha, hi, hUcard, hUfour, hGammacard, hAt⟩
  · rw [hDelta]
    exact translated_coset_normalizer_le_point h.local_datum huH huz.symm
  · rw [hDelta]
    exact translated_normalizer_centralizer_eq_point_centralizer h.local_datum huH huz.symm
  · exact unitAffineHom_ker _ _ _ _
  · exact unitAffineHom_ker_map _ _ _ _
  · exact entire_coset_centralizer_index_eq_affine_image_card _ _ _ _

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
