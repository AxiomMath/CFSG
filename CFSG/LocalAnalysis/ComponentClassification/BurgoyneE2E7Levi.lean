module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Frame
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6Frame
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofAdjointRoots
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.HighestRoot.CentChevalley

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.HighestRoot (rankOneGroup rankOneGroup_adjDatum)
open scoped MatrixGroups

@[expose] def e7LeviE6Node : Fin 6 → Fin (Tag.rank .E7) :=
  ![e7Node 0, e7Node 1, e7Node 2, e7Node 3, e7Node 4, e7Node 5]

theorem e7LeviE6_adj : ∀ i j : Fin 6, edgeE 6 i j → e7LeviE6Node i ≠ e7LeviE6Node j ∧
    Tag.cartan .E7 (e7LeviE6Node i) (e7LeviE6Node j) = -1 ∧
    Tag.cartan .E7 (e7LeviE6Node j) (e7LeviE6Node i) = -1 ∧
    ∃ l : Fin 7,
      ¬ (3 : ℤ) ∣ Tag.cartan .E7 (e7LeviE6Node i) l + 2 * Tag.cartan .E7 (e7LeviE6Node j) l := by
  decide

theorem e7LeviE6_nadj : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
    e7LeviE6Node i ≠ e7LeviE6Node j ∧ Tag.cartan .E7 (e7LeviE6Node i) (e7LeviE6Node j) = 0 ∧
    Tag.cartan .E7 (e7LeviE6Node j) (e7LeviE6Node i) = 0 := by
  decide

@[expose] def e7BitsSix : Fin (Tag.rank .E7) → Bool :=
  listMask [false, false, false, false, false, false, true]

theorem e7BitsSix_eq_false : ∀ j : Fin (Tag.rank .E7), j ≠ e7Node 6 → e7BitsSix j = false := by
  decide

theorem maskPairing_e7BitsSix (α : Fin (Tag.rank .E7) → ℤ) :
    maskPairing e7BitsSix α = α (e7Node 6) := by
  rw [maskPairing, Finset.sum_eq_single (e7Node 6)]
  · simp [show e7BitsSix (e7Node 6) = true from by decide]
  · intro j _ hj
    simp [e7BitsSix_eq_false j hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem e7_even_six_cases : ∀ α ∈ rootFinset .E7, Even (α (e7Node 6)) → α (e7Node 6) = 0 := by
  decide +kernel

theorem e7LeviE6Node_ne_six : ∀ k : Fin 6, e7LeviE6Node k ≠ e7Node 6 := by decide

theorem eq_six_of_forall_e7LeviE6Node_ne :
    ∀ i : Fin (Tag.rank .E7), (∀ k, e7LeviE6Node k ≠ i) → i = e7Node 6 := by
  decide

theorem mem_parabolicRoots_e7LeviE6 {α : Fin (Tag.rank .E7) → ℤ} :
    α ∈ parabolicRoots .E7 (Set.range e7LeviE6Node) ↔ IsRoot .E7 α ∧ α (e7Node 6) = 0 := by
  refine and_congr_right fun _ => ⟨fun h => h _ ?_, fun h i hi => ?_⟩
  · rintro ⟨k, hk⟩
    exact e7LeviE6Node_ne_six k hk
  · rw [eq_six_of_forall_e7LeviE6Node_ne i fun k hk => hi ⟨k, hk⟩]
    exact h

theorem neg_one_zpow_eq_of_even {M : Type*} [Group M] [HasDistribNeg M] {a b : ℤ}
    (h : Even (a - b)) : (-1 : M) ^ a = (-1 : M) ^ b := by
  have : a = b + (a - b) := by ring
  rw [this, zpow_add, h.neg_one_zpow, mul_one]

theorem mem_fixedSubgroup_rootDiagAut
    {τ : Tag} {K : Type} [Field K] {a : Fin τ.rank → Kˣ}
    {g : adjointGroup τ K} :
    g ∈ fixedSubgroup (rootDiagAut τ K a) ↔ (g : ModGL τ K) ∈ toralCentralizer τ K a := by
  change rootDiagAut τ K a g = g ↔ _
  rw [toralCentralizer, mem_inf, mem_centralizer_singleton_iff, ← Subtype.coe_inj,
    coe_rootDiagAut]
  constructor
  · intro h
    refine ⟨g.2, ?_⟩
    calc (g : ModGL τ K) * rootDiagUnit τ a =
        rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ * rootDiagUnit τ a := by rw [h]
      _ = rootDiagUnit τ a * g := by group
  · rintro ⟨-, h⟩
    rw [← h]
    group


abbrev e7LeviE6 (K : Type) [Field K] : Subgroup (adjointGroup .E7 K) :=
  ⨆ k, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7LeviE6Node k)

theorem isQuasisimple_e7LeviE6 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) : IsQuasisimple (e7LeviE6 K) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : Fact p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e7LeviE6Node e7LeviE6_adj e7LeviE6_nadj
  exact (e6_frame_subgroup hadm hK hcomm hρ hψ).choose_spec.2.2.1

theorem rootCharKernel_e7BitsSix {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    rootCharKernel (bitsTuple (K := K) e7BitsSix) =
      parabolicRoots .E7 (Set.range e7LeviE6Node) := by
  rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  ext α
  rw [mem_kernelRoots_maskChar, maskPairing_e7BitsSix, mem_parabolicRoots_e7LeviE6]
  constructor
  · rintro ⟨hα, hev⟩
    exact ⟨hα, e7_even_six_cases α (mem_rootFinset.2 hα) hev⟩
  · rintro ⟨hα, h⟩
    exact ⟨hα, by rw [h]; decide⟩

theorem map_e7LeviE6 {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    (e7LeviE6 K).map (adjointGroup .E7 K).subtype =
      rootSpan .E7 K (rootCharKernel (bitsTuple (K := K) e7BitsSix)) := by
  rw [map_subtype_iSup_rankOne, subsystemGroup_eq_rootSpan, rootCharKernel_e7BitsSix hK2]

theorem e7LeviE6_le_fixedSubgroup {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) :
    e7LeviE6 K ≤ fixedSubgroup (rootDiagAut .E7 K (bitsTuple e7BitsSix)) := by
  intro g hg
  rw [mem_fixedSubgroup_rootDiagAut]
  obtain ⟨hSX, -⟩ := odd_toral_involution_centralizer_p_component_root_reduction .E7 K hK2 _
    (bitsTuple_mem _)
  refine hSX ?_
  rw [← map_e7LeviE6 hK2]
  exact ⟨g, hg, rfl⟩

theorem fixedSubgroup_le_normalizer_e7LeviE6 {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) :
    fixedSubgroup (rootDiagAut .E7 K (bitsTuple e7BitsSix)) ≤
      normalizer ((e7LeviE6 K : Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) := by
  obtain ⟨hSX, hSn, -⟩ := odd_toral_involution_centralizer_p_component_root_reduction .E7 K hK2 _
    (bitsTuple_mem _)
  have hmem : ∀ x : adjointGroup .E7 K, x ∈ e7LeviE6 K ↔
      (x : ModGL .E7 K) ∈ rootSpan .E7 K (rootCharKernel (bitsTuple (K := K) e7BitsSix)) := by
    intro x
    rw [← map_e7LeviE6 hK2]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [Subtype.ext hyx] at hy
  intro g hg
  have hgX := mem_fixedSubgroup_rootDiagAut.1 hg
  rw [mem_normalizer_iff]
  intro x
  rw [hmem, hmem]
  have hconj : ∀ y : ModGL .E7 K, y ∈ rootSpan .E7 K (rootCharKernel (bitsTuple (K := K)
      e7BitsSix)) → y ∈ toralCentralizer .E7 K (bitsTuple e7BitsSix) →
      ∀ h : ModGL .E7 K, h ∈ toralCentralizer .E7 K (bitsTuple e7BitsSix) →
        h * y * h⁻¹ ∈ rootSpan .E7 K (rootCharKernel (bitsTuple (K := K) e7BitsSix)) := by
    intro y hy hyX h hh
    have := hSn.conj_mem ⟨y, hyX⟩ hy ⟨h, hh⟩
    exact this
  constructor
  · intro hx
    have hxX : (x : ModGL .E7 K) ∈ toralCentralizer .E7 K (bitsTuple e7BitsSix) := hSX hx
    have := hconj _ hx hxX _ hgX
    simpa using this
  · intro hx
    have hx' : ((g * x * g⁻¹ : adjointGroup .E7 K) : ModGL .E7 K) ∈
        toralCentralizer .E7 K (bitsTuple e7BitsSix) := hSX hx
    have := hconj _ hx hx' _ (inv_mem hgX)
    simpa [mul_assoc] using this

theorem torusElt_six_neg_one (K : Type) [Field K] :
    torusElt .E7 K (e7Node 6) (-1) =
      torusElt .E7 K (e7Node 1) (-1) * torusElt .E7 K (e7Node 4) (-1) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul]
  congr 1
  funext j
  rw [Pi.mul_apply, ← zpow_add]
  refine neg_one_zpow_eq_of_even ?_
  revert j
  decide

abbrev torusEltC (K : Type) [Field K] (i : Fin (Tag.rank .E7)) (t : Kˣ) : adjointGroup .E7 K :=
  ⟨torusElt .E7 K i t, torusElt_mem_adjointGroup i t⟩

theorem torusEltC_mem_rankOne {K : Type} [Field K] (i : Fin (Tag.rank .E7)) (t : Kˣ) :
    torusEltC K i t ∈ rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup i := by
  change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single i 1)
  rw [rankOneGroup_adjDatum _ (isRoot_single _ i), mem_subgroupOf]
  change torusElt .E7 K i t ∈ rootSubgroup .E7 K (Pi.single i 1) ⊔
    rootSubgroup .E7 K (-Pi.single i 1)
  rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
  exact ⟨HSL t, simpleRootSL2_HSL i t⟩

theorem torusEltC_six_mem_e7LeviE6 (K : Type) [Field K] :
    torusEltC K (e7Node 6) (-1) ∈ e7LeviE6 K := by
  have h : torusEltC K (e7Node 6) (-1) =
      torusEltC K (e7Node 1) (-1) * torusEltC K (e7Node 4) (-1) :=
    Subtype.ext (torusElt_six_neg_one K)
  rw [h]
  refine mul_mem ?_ ?_
  · exact le_iSup (fun k => rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup
      (e7LeviE6Node k)) 1 (torusEltC_mem_rankOne _ _)
  · exact le_iSup (fun k => rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup
      (e7LeviE6Node k)) 4 (torusEltC_mem_rankOne _ _)

end CFSG.ComponentClassification.Burgoyne.E2
