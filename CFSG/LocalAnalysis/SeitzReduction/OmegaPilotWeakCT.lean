module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPieces
public import CFSG.ClassicalInvolution.WeakCT.Spin

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.LieType CFSG.LieType.Universal
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (B12 B23 LinearBlockStandardPair)
open scoped MatrixGroups

section Abstract

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F]

theorem map_conj_one_inv_eq' {M : Type*} [Group M] (H : Subgroup M) :
    H.map (MulAut.conj (1 : M)⁻¹).toMonoidHom = H := by
  ext x
  simp

theorem exists_weakCT_spinPlus_of_pieces {n f : ℕ} (hn : 4 ≤ n) (hn3 : 3 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ (2 * f)) (U : Fin n → Subgroup G) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ k, U k)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      U i ≤ centralizer (U j : Set G))
    (hpair : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧
      (B12 F).map θ = U i ∧ (B23 F).map θ = U j) :
    ∃ Ψ : spinGroup (Spin.quadPlus n F) →* G₀, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) .POmegaPlus n 2 (2 * f) ∧
      ∀ k, (CurtisTits.rankOne (Spin.plusDatum n F hn3).rootGroup k).map Ψ =
        (U k).subgroupOf G₀ := by
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle : ∀ k, U k ≤ G₀ := fun k => hG₀ ▸ le_iSup U k
  have hUmap : ∀ k, ((U k).subgroupOf G₀).map G₀.subtype = U k := fun k => by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (hle k)]
  have hgen : ⨆ k, (U k).subgroupOf G₀ = ⊤ := by
    apply map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [hUmap]
    exact hG₀.symm
  have hcomm' : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a ∈ (U i).subgroupOf G₀, ∀ b ∈ (U j).subgroupOf G₀, a * b = b * a := by
    intro i j hij h1 h2 a ha b hb
    have h := mem_centralizer_iff.1 (hcomm i j hij h1 h2 (mem_subgroupOf.1 ha)) (b : G)
      (mem_subgroupOf.1 hb)
    exact Subtype.ext h.symm
  have hpair' : ∀ i j : Fin n, edgeD n i j →
      ∃ W, LinearBlockStandardPair F W ((U i).subgroupOf G₀) ((U j).subgroupOf G₀) := by
    intro i j hij
    obtain ⟨θ, hθker, hθ12, hθ23⟩ := hpair i j hij
    have hθG₀ : ∀ A, θ A ∈ G₀ := by
      intro A
      have hA : θ A ∈ θ.range := ⟨A, rfl⟩
      rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.WeakCT.B12_sup_B23 (K := F),
        Subgroup.map_sup, hθ12, hθ23] at hA
      exact sup_le (hle i) (hle j) hA
    let θ' : SL(3, F) →* G₀ := θ.codRestrict G₀ hθG₀
    have hθ' : ∀ H : Subgroup SL(3, F), (H.map θ').map G₀.subtype = H.map θ := fun H => by
      rw [map_map]
      rfl
    refine ⟨θ'.range, θ', 1, rfl, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hθker
    · rw [map_conj_one_inv_eq']
      apply map_injective G₀.subtype_injective
      rw [hθ', hθ12, hUmap]
    · rw [map_conj_one_inv_eq']
      apply map_injective G₀.subtype_injective
      rw [hθ', hθ23, hUmap]
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus n 2 (2 * f) :=
    ⟨Nat.prime_two, by omega, hn⟩
  obtain ⟨Ψ, hΨs, hΨk, hq, -, hmodel, hroot⟩ :=
    CFSG.ClassicalInvolution.WeakCT.weakCT_spinPlus hadm hn3 hF hF4
      (fun k => (U k).subgroupOf G₀) hgen hcomm' hpair'
  exact ⟨Ψ, hΨs, hΨk, hq, hmodel, hroot⟩

end Abstract

section Nodes

@[expose] def plusNodeSet (n : ℕ) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x : Fin n =>
    (j.val + 1 < n ∧ (x.val = j.val ∨ x.val = j.val + 1)) ∨ (j.val + 1 = n ∧ n ≤ x.val + 2)

@[expose] def plusNodeFlip (n : ℕ) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x : Fin n => j.val + 1 = n ∧ x.val + 1 = n

@[expose] def plusEdgeSet (n : ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x : Fin n => i.val ≤ x.val ∧ x.val ≤ i.val + 2

theorem mem_plusNodeSet {n : ℕ} {j x : Fin n} :
    x ∈ plusNodeSet n j ↔
      (j.val + 1 < n ∧ (x.val = j.val ∨ x.val = j.val + 1)) ∨ (j.val + 1 = n ∧ n ≤ x.val + 2) := by
  simp [plusNodeSet]

theorem mem_plusNodeFlip {n : ℕ} {j x : Fin n} :
    x ∈ plusNodeFlip n j ↔ j.val + 1 = n ∧ x.val + 1 = n := by
  simp [plusNodeFlip]

theorem mem_plusEdgeSet {n : ℕ} {i x : Fin n} :
    x ∈ plusEdgeSet n i ↔ i.val ≤ x.val ∧ x.val ≤ i.val + 2 := by
  simp [plusEdgeSet]

theorem two_le_card_plusNodeSet {n : ℕ} (hn : 2 ≤ n) (j : Fin n) : 2 ≤ (plusNodeSet n j).card := by
  have hj := j.isLt
  by_cases h : j.val + 1 < n
  · refine Finset.one_lt_card.2 ⟨⟨j.val, hj⟩, ?_, ⟨j.val + 1, h⟩, ?_, ?_⟩
    · rw [mem_plusNodeSet]
      left
      exact ⟨h, Or.inl rfl⟩
    · rw [mem_plusNodeSet]
      left
      exact ⟨h, Or.inr rfl⟩
    · intro e
      have := congrArg Fin.val e
      simp at this
  · refine Finset.one_lt_card.2 ⟨⟨n - 2, by omega⟩, ?_, ⟨n - 1, by omega⟩, ?_, ?_⟩
    · rw [mem_plusNodeSet]
      right
      exact ⟨by omega, by simp; omega⟩
    · rw [mem_plusNodeSet]
      right
      exact ⟨by omega, by simp; omega⟩
    · intro e
      have := congrArg Fin.val e
      simp at this
      omega

theorem card_plusNodeSet_le {n : ℕ} (j : Fin n) : (plusNodeSet n j).card ≤ 2 := by
  set lo := if j.val + 1 < n then j.val else n - 2
  have hsub : (plusNodeSet n j).map Fin.valEmbedding ⊆ Finset.Icc lo (lo + 1) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    rw [mem_plusNodeSet] at hy
    rw [Finset.mem_Icc, Fin.valEmbedding_apply]
    have := y.isLt
    simp only [lo]
    split_ifs with h <;> omega
  calc (plusNodeSet n j).card = ((plusNodeSet n j).map Fin.valEmbedding).card :=
        (Finset.card_map _).symm
    _ ≤ (Finset.Icc lo (lo + 1)).card := Finset.card_le_card hsub
    _ = 2 := by
        rw [Nat.card_Icc]
        omega

theorem disjoint_plusNodeSet {n : ℕ} {i j : Fin n} (hij : i ≠ j) (h1 : ¬ edgeD n i j)
    (h2 : ¬ edgeD n j i) (hf1 : ¬ (i.val + 2 = n ∧ j.val + 1 = n))
    (hf2 : ¬ (j.val + 2 = n ∧ i.val + 1 = n)) :
    Disjoint (plusNodeSet n i) (plusNodeSet n j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [mem_plusNodeSet] at hxi hxj
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  unfold edgeD at h1 h2
  have := x.isLt
  omega

theorem plusNodeSet_subset_plusEdgeSet {n : ℕ} {i j : Fin n} (hij : edgeD n i j) :
    plusNodeSet n i ⊆ plusEdgeSet n i ∧ plusNodeSet n j ⊆ plusEdgeSet n i := by
  unfold edgeD at hij
  constructor <;> intro x hx <;> rw [mem_plusNodeSet] at hx <;> rw [mem_plusEdgeSet] <;>
    have := x.isLt <;> omega

theorem disjoint_plusNodeSet_plusNodeFlip {n : ℕ} {i j : Fin n} (hij : edgeD n i j) :
    Disjoint (plusNodeSet n i) (plusNodeFlip n i) ∧
      Disjoint (plusNodeSet n i) (plusNodeFlip n j) := by
  unfold edgeD at hij
  constructor <;> rw [Finset.disjoint_left] <;> intro x hx hx' <;>
    rw [mem_plusNodeSet] at hx <;> rw [mem_plusNodeFlip] at hx' <;> omega

@[expose] def edgeNbr {m : ℕ} (i : Fin (m + 1)) : Fin (m + 1) :=
  if i.val = 0 then Fin.last m else 0

theorem val_succAbove_edgeNbr {m : ℕ} (i : Fin (m + 1)) (x : Fin m) :
    ((edgeNbr i).succAbove x).val = if i.val = 0 then x.val else x.val + 1 := by
  unfold edgeNbr
  split_ifs
  · simp [Fin.succAbove_last]
  · simp

theorem edgeNbr_notMem {m : ℕ} (hm : 3 ≤ m) (i : Fin (m + 1)) :
    edgeNbr i ∉ plusEdgeSet (m + 1) i := by
  unfold edgeNbr
  rw [mem_plusEdgeSet]
  split_ifs with h
  · simp only [Fin.val_last]
    omega
  · simp only [Fin.val_zero]
    omega

theorem preimagePlanes_plusEdgeSet {m : ℕ} (i : Fin (m + 1)) :
    preimagePlanes (edgeNbr i) (plusEdgeSet (m + 1) i) =
      LinearPilot.consecutiveBlock m (i.val - 1) 3 := by
  ext x
  rw [mem_preimagePlanes, mem_plusEdgeSet, val_succAbove_edgeNbr,
    LinearPilot.mem_consecutiveBlock]
  split_ifs with h <;> omega

theorem preimagePlanes_plusNodeSet_left {m : ℕ} {i j : Fin (m + 1)} (hij : edgeD (m + 1) i j) :
    preimagePlanes (edgeNbr i) (plusNodeSet (m + 1) i) =
      LinearPilot.consecutiveBlock m (i.val - 1) 2 := by
  ext x
  rw [mem_preimagePlanes, mem_plusNodeSet, val_succAbove_edgeNbr,
    LinearPilot.mem_consecutiveBlock]
  unfold edgeD at hij
  have := x.isLt
  split_ifs with h <;> omega

theorem preimagePlanes_plusNodeSet_right {m : ℕ} {i j : Fin (m + 1)} (hij : edgeD (m + 1) i j) :
    preimagePlanes (edgeNbr i) (plusNodeSet (m + 1) j) =
      LinearPilot.consecutiveBlock m (i.val - 1 + 1) 2 := by
  ext x
  rw [mem_preimagePlanes, mem_plusNodeSet, val_succAbove_edgeNbr,
    LinearPilot.mem_consecutiveBlock]
  unfold edgeD at hij
  have := x.isLt
  split_ifs with h <;> omega

end Nodes

section Covers

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore_anti commutator_centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG_mono)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]

@[expose] noncomputable def plusNode {n : ℕ}
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (j : Fin n) : Subgroup G :=
  plusSignedLevelCore e (plusNodeSet n j) (plusNodeFlip n j)

theorem commutator_plusNode [Finite G] {n : ℕ}
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K))
    (j : Fin n) : ⁅plusNode e j, plusNode e j⁆ = plusNode e j :=
  commutator_centralizerPerfectCore _

theorem mem_normalizer_iSup_of_forall {M : Type*} [Group M] {ι' : Sort*} {H : ι' → Subgroup M}
    {g : M} (hg : ∀ i, g ∈ normalizer (H i : Set M)) :
    g ∈ normalizer ((⨆ i, H i : Subgroup M) : Set M) := by
  have hmap : ∀ i, (H i).map (MulAut.conj g).toMonoidHom = H i := fun i => by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 (hg i) x).1 hx
    · intro hy
      refine ⟨g⁻¹ * y * g, (mem_normalizer_iff.1 (hg i) _).2 ?_, ?_⟩
      · rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
      · change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hsup : (⨆ i, H i).map (MulAut.conj g).toMonoidHom = ⨆ i, H i := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hmap
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hsup]
    exact ⟨x, hx, rfl⟩
  · rw [← hsup] at hx
    obtain ⟨x', hx', hxx'⟩ := hx
    have : x' = x := by
      change g * x' * g⁻¹ = g * x * g⁻¹ at hxx'
      simpa using hxx'
    exact this ▸ hx'

theorem mem_normalizer_iSup_plusNode {n : ℕ}
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (ht : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer ((⨆ j, plusNode e j : Subgroup G) : Set G) :=
  mem_normalizer_iSup_of_forall fun _ =>
    UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e ht _

theorem plusSignedLevelCore_mono {n : ℕ}
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {J J' : Finset (Fin n)}
    (h : J ⊆ J') (P : Finset (Fin n)) :
    plusSignedLevelCore e J P ≤ plusSignedLevelCore e J' P :=
  centralizerPerfectCore_anti (modelToG_mono e
    (frameTorusOf_mono (Subgroup.comap_mono (levelParam_anti h))))

theorem two_le_card_plusEdgeSet {n : ℕ} {i j : Fin n} (hij : edgeD n i j) :
    2 ≤ (plusEdgeSet n i).card := by
  have hi1 : i.val + 1 < n := by unfold edgeD at hij; have := j.isLt; omega
  refine Finset.one_lt_card.2 ⟨i, ?_, ⟨i.val + 1, hi1⟩, ?_, ?_⟩
  · rw [mem_plusEdgeSet]
    omega
  · rw [mem_plusEdgeSet]
    simp
  · intro e
    have := congrArg Fin.val e
    simp at this

variable [Finite G] [Finite K] [CharP K 2] [Finite F] {m : ℕ}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)} {ι : K →+* F}

theorem exists_theta_plusNode (hm : 3 ≤ m) (hC : ∀ k, PlusFieldCover e ι k)
    (hK : 4 ≤ Nat.card K) (hF : 5 ≤ Nat.card F) {i j : Fin (m + 1)}
    (hij : edgeD (m + 1) i j) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = plusNode e i ∧
      (B23 F).map θ = plusNode e j := by
  have hF4 : 4 ≤ Nat.card F := by omega
  have hk := edgeNbr_notMem hm i
  obtain ⟨hsi, hsj⟩ := plusNodeSet_subset_plusEdgeSet hij
  obtain ⟨hdi, hdj⟩ := disjoint_plusNodeSet_plusNodeFlip hij
  have hUi : plusNode e i =
      plusSignedLevelCore e (plusNodeSet (m + 1) i) (plusNodeFlip (m + 1) j) := by
    rw [plusNode, plusSignedLevelCore_of_disjoint e hdi, plusSignedLevelCore_of_disjoint e hdj]
  have hki : edgeNbr i ∉ plusNodeSet (m + 1) i := fun h => hk (hsi h)
  have hkj : edgeNbr i ∉ plusNodeSet (m + 1) j := fun h => hk (hsj h)
  have ha : i.val - 1 + 3 ≤ m := by
    unfold edgeD at hij
    omega
  have hM := (hC (edgeNbr i)).map_signedLevelCore hK hF4 hk (two_le_card_plusEdgeSet hij)
    (plusNodeFlip (m + 1) j)
  rw [preimagePlanes_plusEdgeSet] at hM
  have hU := (hC (edgeNbr i)).map_signedLevelCore hK hF4 hki
    (two_le_card_plusNodeSet (by omega) i) (plusNodeFlip (m + 1) j)
  rw [preimagePlanes_plusNodeSet_left hij] at hU
  have hV := (hC (edgeNbr i)).map_signedLevelCore hK hF4 hkj
    (two_le_card_plusNodeSet (by omega) j) (plusNodeFlip (m + 1) j)
  rw [preimagePlanes_plusNodeSet_right hij] at hV
  rw [hUi]
  exact (hC (edgeNbr i)).exists_theta hF
    (plusSignedLevelCore_le_plusNeighbourCore e hk (plusNodeFlip (m + 1) j))
    (plusSignedLevelCore_mono e hsi _) (plusSignedLevelCore_mono e hsj _)
    (commutator_centralizerPerfectCore _) (commutator_centralizerPerfectCore _) ha _ hM hU hV

theorem plusNode_le_centralizer (hm : 4 ≤ m) (hC : ∀ k, PlusFieldCover e ι k)
    (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) {i j : Fin (m + 1)}
    (hd : Disjoint (plusNodeSet (m + 1) i) (plusNodeSet (m + 1) j)) :
    plusNode e i ≤ centralizer (plusNode e j : Set G) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := plusNodeSet (m + 1) i ∪ plusNodeSet (m + 1) j) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      have h1 := Finset.card_union_le (plusNodeSet (m + 1) i) (plusNodeSet (m + 1) j)
      have h2 := card_plusNodeSet_le i
      have h3 := card_plusNodeSet_le j
      omega)
  have hki : k ∉ plusNodeSet (m + 1) i := fun h => hk (Finset.mem_union_left _ h)
  have hkj : k ∉ plusNodeSet (m + 1) j := fun h => hk (Finset.mem_union_right _ h)
  have hU : (((plusNode e i).subgroupOf (plusNeighbourCore e k)).map (hC k).π).map
      (StatedOmega (StatedQuadPlus m F)).subtype = _ :=
    (hC k).map_signedLevelCore hK hF hki (two_le_card_plusNodeSet (by omega) i)
      (plusNodeFlip (m + 1) i)
  have hV : (((plusNode e j).subgroupOf (plusNeighbourCore e k)).map (hC k).π).map
      (StatedOmega (StatedQuadPlus m F)).subtype = _ :=
    (hC k).map_signedLevelCore hK hF hkj (two_le_card_plusNodeSet (by omega) j)
      (plusNodeFlip (m + 1) j)
  have hd' : Disjoint (preimagePlanes k (plusNodeSet (m + 1) i))
      (preimagePlanes k (plusNodeSet (m + 1) j)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_preimagePlanes] at hx hx'
    exact Finset.disjoint_left.1 hd hx hx'
  refine (hC k).le_centralizer (plusSignedLevelCore_le_plusNeighbourCore e hki _)
    (plusSignedLevelCore_le_plusNeighbourCore e hkj _) (commutator_plusNode e j) ?_
  intro x hx y hy
  rw [hU] at hx
  rw [hV] at hy
  exact commute_of_mem_flip_siegelBlockGL hd' hx hy

end Covers

end CFSG.SeitzReduction.OmegaPilot
