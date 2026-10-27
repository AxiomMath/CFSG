module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalGen

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore commutator_centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeEnum planeEnum_injective liftParam
  planeTorusParam planeOf diagSpEntry suppGL)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open CFSG.Timmesfeld (edgeD)
open scoped MatrixGroups

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}
  {k : Fin (r + 1)}

@[expose] noncomputable def MinusFieldCover.lift (C : MinusFieldCover e ι k)
    (B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) : Subgroup G :=
  perfectCore ((B.comap ((StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp C.π)).map
    (minusNeighbourCore e k).subtype)

omit [Finite F] in
theorem MinusFieldCover.lift_eq (C : MinusFieldCover e ι k)
    (B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) :
    C.lift B = (perfectCore (B.comap ((StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp
      C.π))).map (minusNeighbourCore e k).subtype :=
  (CFSG.Quasithin.map_perfectCore _ _).symm

omit [Finite F] in
theorem MinusFieldCover.lift_le (C : MinusFieldCover e ι k)
    (B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) : C.lift B ≤ minusNeighbourCore e k := by
  rw [C.lift_eq]
  exact map_subtype_le _

omit [Finite F] in
theorem MinusFieldCover.commutator_lift (C : MinusFieldCover e ι k)
    (B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) : ⁅C.lift B, C.lift B⁆ = C.lift B :=
  perfectCore_perfect _

theorem MinusFieldCover.map_lift (C : MinusFieldCover e ι k)
    {B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)}
    (hBΩ : B ≤ StatedOmega (StatedQuadPlus (r + 1) F)) (hBp : ⁅B, B⁆ = B) :
    (((C.lift B).subgroupOf (minusNeighbourCore e k)).map C.π).map
      (StatedOmega (StatedQuadPlus (r + 1) F)).subtype = B := by
  set π' := (StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp C.π with hπ'
  have hsub : (C.lift B).subgroupOf (minusNeighbourCore e k) = perfectCore (B.comap π') := by
    rw [C.lift_eq]
    ext x
    rw [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hrange : π'.range = StatedOmega (StatedQuadPlus (r + 1) F) := by
    rw [hπ', MonoidHom.range_comp, MonoidHom.range_eq_top.2 C.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  rw [hsub, Subgroup.map_map, ← hπ', CFSG.Quasithin.map_perfectCore, Subgroup.map_comap_eq,
    hrange, inf_of_le_right hBΩ]
  exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hBp

end Lift

section ForkBlock

variable (F : Type) [Field F] (r : ℕ)

@[expose] noncomputable def forkBlock (P : Finset (Fin (r + 1))) :
    Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F) :=
  (siegelBlockGL F (consecutiveBlock (r + 1) (r - 1) 2)).map
    (MulAut.conj (flipGL F P)).toMonoidHom

variable {F r}

theorem card_consecutiveBlock_two {m i : ℕ} (h : i + 2 ≤ m) :
    (consecutiveBlock m i 2).card = 2 := by
  have h1 : consecutiveBlock m i 2 = {⟨i, by omega⟩, ⟨i + 1, by omega⟩} := by
    ext x
    rw [mem_consecutiveBlock, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    simp only
    omega
  rw [h1, Finset.card_pair]
  intro h'
  have := congrArg Fin.val h'
  simp at this

theorem card_consecutiveBlock {m i k : ℕ} (h : i + k ≤ m) :
    (consecutiveBlock m i k).card = k := by
  have hmap : (consecutiveBlock m i k).map Fin.valEmbedding = Finset.Ico i (i + k) := by
    ext x
    simp only [Finset.mem_map, mem_consecutiveBlock, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Ico]
  omega

theorem commutator_forkBlock [Finite F] (hF : 4 ≤ Nat.card F) (hr : 1 ≤ r)
    (P : Finset (Fin (r + 1))) : ⁅forkBlock F r P, forkBlock F r P⁆ = forkBlock F r P := by
  rw [forkBlock, ← Subgroup.map_commutator, commutator_siegelBlockGL hF
    (card_consecutiveBlock_two (by omega)).ge]

theorem forkBlock_le_statedOmega [Finite F] (hF : 4 ≤ Nat.card F) (hr : 1 ≤ r)
    (P : Finset (Fin (r + 1))) : forkBlock F r P ≤ StatedOmega (StatedQuadPlus (r + 1) F) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.1 (flipGL_mem_normalizer (F := F) P) x).1
    (siegelBlockGL_le_statedOmega hF (card_consecutiveBlock_two (by omega)).ge hx)

theorem flip_siegelBlockGL_le_centralizer {m : ℕ} {B P : Finset (Fin m)} {D : Set (Fin m → Fˣ)}
    (hD : ∀ s ∈ D, ∀ i, i ∈ B ∨ i ∈ P → s i = 1) :
    (siegelBlockGL F B).map (MulAut.conj (flipGL F P)).toMonoidHom ≤
      centralizer (diagOmega F m '' D) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  have hflip : flipParam F P s = s := by
    funext i
    rw [flipParam_apply]
    split_ifs with hi
    · rw [hD s hs i (Or.inr hi), inv_one]
    · rfl
  have hs' : diagOmega F m s = flipGL F P * diagOmega F m s * (flipGL F P)⁻¹ := by
    rw [flipGL_mul_diagOmega_mul_inv, hflip]
  have hc : z * diagOmega F m s = diagOmega F m s * z := by
    have h1 := mem_centralizer_iff.1 (siegelBlockGL_le_centralizer (D := {s})
      (fun s' hs' i hi j hj => by
        rw [Set.mem_singleton_iff] at hs'
        rw [hs', hD s hs i (Or.inl hi), hD s hs j (Or.inl hj)]) hz) _ ⟨_, rfl, rfl⟩
    exact h1.symm
  change diagOmega F m s * (flipGL F P * z * (flipGL F P)⁻¹) =
    flipGL F P * z * (flipGL F P)⁻¹ * diagOmega F m s
  rw [hs']
  calc flipGL F P * diagOmega F m s * (flipGL F P)⁻¹ * (flipGL F P * z * (flipGL F P)⁻¹)
      = flipGL F P * (diagOmega F m s * z) * (flipGL F P)⁻¹ := by group
    _ = flipGL F P * (z * diagOmega F m s) * (flipGL F P)⁻¹ := by rw [hc]
    _ = _ := by group

end ForkBlock

section Planes

variable {r : ℕ}

theorem castSuccPlanes_preimagePlanes_zero {j : ℕ} (hj1 : 1 ≤ j) (hj : j + 1 ≤ r) :
    castSuccPlanes (preimagePlanes (0 : Fin (r + 1)) (consecutiveBlock (r + 1) j 2)) =
      consecutiveBlock (r + 1) (j - 1) 2 := by
  ext y
  rw [mem_castSuccPlanes, mem_consecutiveBlock]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [mem_preimagePlanes, Fin.succAbove_zero, mem_consecutiveBlock, Fin.val_succ] at hi
    rw [Fin.val_castSucc]
    omega
  · intro hy
    refine ⟨⟨y.val, by omega⟩, ?_, Fin.ext rfl⟩
    rw [mem_preimagePlanes, Fin.succAbove_zero, mem_consecutiveBlock, Fin.val_succ]
    simp only
    omega

theorem castSuccPlanes_preimagePlanes_last {j : ℕ} (hj : j + 2 ≤ r) :
    castSuccPlanes (preimagePlanes (Fin.last r) (consecutiveBlock (r + 1) j 2)) =
      consecutiveBlock (r + 1) j 2 := by
  ext y
  rw [mem_castSuccPlanes, mem_consecutiveBlock]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [mem_preimagePlanes, Fin.succAbove_last, mem_consecutiveBlock, Fin.val_castSucc] at hi
    rw [Fin.val_castSucc]
    omega
  · intro hy
    refine ⟨⟨y.val, by omega⟩, ?_, Fin.ext rfl⟩
    rw [mem_preimagePlanes, Fin.succAbove_last, mem_consecutiveBlock, Fin.val_castSucc]
    simp only
    omega

theorem insert_castSuccPlanes_preimagePlanes_zero_last (hr : 1 ≤ r) :
    insert (Fin.last r) (castSuccPlanes (preimagePlanes (0 : Fin (r + 1)) {Fin.last r})) =
      consecutiveBlock (r + 1) (r - 1) 2 := by
  ext y
  rw [Finset.mem_insert, mem_castSuccPlanes, mem_consecutiveBlock, Fin.ext_iff, Fin.val_last]
  constructor
  · rintro (h | ⟨i, hi, rfl⟩)
    · omega
    · rw [mem_preimagePlanes, Fin.succAbove_zero, Finset.mem_singleton, Fin.ext_iff,
        Fin.val_succ, Fin.val_last] at hi
      rw [Fin.val_castSucc]
      omega
  · intro hy
    by_cases h : y.val = r
    · exact Or.inl h
    · refine Or.inr ⟨⟨y.val, by omega⟩, ?_, Fin.ext rfl⟩
      rw [mem_preimagePlanes, Fin.succAbove_zero, Finset.mem_singleton, Fin.ext_iff,
        Fin.val_succ, Fin.val_last]
      simp only
      omega

theorem disjoint_castSuccPlanes_preimagePlanes {k : Fin (r + 1)} {I J : Finset (Fin (r + 1))}
    (h : Disjoint I J) :
    Disjoint (castSuccPlanes (preimagePlanes k I)) (castSuccPlanes (preimagePlanes k J)) := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  obtain ⟨i, hi, rfl⟩ := mem_castSuccPlanes.1 hy
  obtain ⟨i', hi', hii'⟩ := mem_castSuccPlanes.1 hy'
  rw [Fin.castSucc_inj] at hii'
  subst hii'
  exact Finset.disjoint_left.1 h (mem_preimagePlanes.1 hi) (mem_preimagePlanes.1 hi')

end Planes

section Nodes

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}

@[expose] noncomputable def minusNode (C₀ : MinusFieldCover e ι 0) (j : Fin (r + 2)) :
    Subgroup G :=
  if j.val + 1 ≤ r then minusLevelCore e (consecutiveBlock (r + 1) j.val 2)
  else if j.val = r then C₀.lift (forkBlock F r ∅)
  else C₀.lift (forkBlock F r {Fin.last r})

omit [Finite G] [Finite F] in
theorem minusNode_of_le (C₀ : MinusFieldCover e ι 0) {j : Fin (r + 2)} (hj : j.val + 1 ≤ r) :
    minusNode C₀ j = minusLevelCore e (consecutiveBlock (r + 1) j.val 2) := by
  simp [minusNode, hj]

omit [Finite G] [Finite F] in
theorem minusNode_of_eq (C₀ : MinusFieldCover e ι 0) {j : Fin (r + 2)} (hj : j.val = r) :
    minusNode C₀ j = C₀.lift (forkBlock F r ∅) := by
  simp [minusNode, hj]

omit [Finite G] [Finite F] in
theorem minusNode_of_eq_succ (C₀ : MinusFieldCover e ι 0) {j : Fin (r + 2)}
    (hj : j.val = r + 1) : minusNode C₀ j = C₀.lift (forkBlock F r {Fin.last r}) := by
  simp [minusNode, hj]

omit [Finite F] in
theorem commutator_minusNode (C₀ : MinusFieldCover e ι 0) (j : Fin (r + 2)) :
    ⁅minusNode C₀ j, minusNode C₀ j⁆ = minusNode C₀ j := by
  unfold minusNode
  split_ifs
  · exact commutator_centralizerPerfectCore _
  · exact C₀.commutator_lift _
  · exact C₀.commutator_lift _

theorem lift_forkBlock_le_minusPieceCore (C₀ : MinusFieldCover e ι 0) (hF : 4 ≤ Nat.card F)
    (hr : 1 ≤ r) {P : Finset (Fin (r + 1))} (hP : P ⊆ {Fin.last r}) :
    C₀.lift (forkBlock F r P) ≤ minusPieceCore e {Fin.last r} := by
  have h0 : (0 : Fin (r + 1)) ∉ ({Fin.last r} : Finset (Fin (r + 1))) := by
    rw [Finset.mem_singleton, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    omega
  have hME := minusPieceCore_le_minusNeighbourCore e h0
  set π' := (StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp C₀.π with hπ'
  have hker : π'.ker ≤ center (minusNeighbourCore e (0 : Fin (r + 1))) := C₀.ker_comp_subtype_le
  have h := map_frameCore_eq_of_conjDiag_quot (isHypFrame_minus K hn b c) e
    (minusNeighbourDiag ι 0) (minusNeighbourDiag_mem_normalizer ι 0)
    (P := planeTorusParam K {Fin.last r}) (X := modelToG e (minusPairTorus hn b c (0 : Fin (r + 1))))
    (modelToG_mono e (minusPairTorus_le_minusPlaneTorus h0)) C₀.π C₀.surjective C₀.ker_le
    (fun t _ hN x => C₀.equivariant t hN x)
  rw [image_minusNeighbourDiag] at h
  have hblock : forkBlock F r P ≤ ((((minusPieceCore e {Fin.last r}).subgroupOf
      (minusNeighbourCore e (0 : Fin (r + 1)))).map C₀.π).map (StatedOmega (StatedQuadPlus (r + 1) F)).subtype) := by
    rw [show (((minusPieceCore e {Fin.last r}).subgroupOf (minusNeighbourCore e (0 : Fin (r + 1)))).map
        C₀.π).map (StatedOmega (StatedQuadPlus (r + 1) F)).subtype = _ from h]
    refine le_perfectCore_of_perfect (le_inf (forkBlock_le_statedOmega hF hr P) ?_)
      (commutator_forkBlock hF hr P)
    refine flip_siegelBlockGL_le_centralizer ?_
    rintro _ ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩ i hi
    have hlast : ∀ x : Fin (r + 1), x = Fin.last r ∨ x.val = r - 1 →
        snocOneParam F r (liftParam ι (restrictParam 0 t)) x = 1 := by
      rintro x (rfl | hx)
      · exact snocOneParam_last _
      · have hx' : x = (⟨r - 1, by omega⟩ : Fin r).castSucc := Fin.ext (by simp [hx])
        rw [hx', snocOneParam_castSucc]
        have htl : t (Fin.last r) = 1 := ht _ (Finset.mem_singleton_self _)
        have hsa : (0 : Fin (r + 1)).succAbove ⟨r - 1, by omega⟩ = Fin.last r :=
          Fin.ext (by simp; omega)
        simp only [liftParam, restrictParam_apply, hsa, htl, map_one]
    apply hlast
    rcases hi with hi | hi
    · rw [mem_consecutiveBlock] at hi
      by_cases h' : i.val = r
      · exact Or.inl (Fin.ext (by simp [h']))
      · exact Or.inr (by omega)
    · exact Or.inl (Finset.mem_singleton.1 (hP hi))
  have hA : ⁅(C₀.lift (forkBlock F r P)).subgroupOf (minusNeighbourCore e (0 : Fin (r + 1))),
      (C₀.lift (forkBlock F r P)).subgroupOf (minusNeighbourCore e (0 : Fin (r + 1)))⁆ =
      (C₀.lift (forkBlock F r P)).subgroupOf (minusNeighbourCore e (0 : Fin (r + 1))) :=
    commutator_subgroupOf_eq_of_le_perfect (C₀.lift_le _) (C₀.commutator_lift _)
  have hB : ⁅(minusPieceCore e {Fin.last r}).subgroupOf (minusNeighbourCore e (0 : Fin (r + 1))),
      (minusPieceCore e {Fin.last r}).subgroupOf (minusNeighbourCore e (0 : Fin (r + 1)))⁆ =
      (minusPieceCore e {Fin.last r}).subgroupOf (minusNeighbourCore e (0 : Fin (r + 1))) :=
    commutator_subgroupOf_eq_of_le_perfect hME (commutator_centralizerPerfectCore _)
  have hAB := le_of_map_le_of_perfect hker hA hB (by
    rw [← Subgroup.map_map, ← Subgroup.map_map, C₀.map_lift (forkBlock_le_statedOmega hF hr P)
      (commutator_forkBlock hF hr P)]
    exact hblock)
  intro x hx
  exact hAB (show (⟨x, C₀.lift_le _ hx⟩ : minusNeighbourCore e (0 : Fin (r + 1))) ∈ _ from hx)

end Nodes

section Pairs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}
  {k : Fin (r + 1)}

omit [Finite F] in
theorem map_conj_flipGL_empty (M : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) :
    M.map (MulAut.conj (flipGL F (∅ : Finset (Fin (r + 1))))).toMonoidHom = M := by
  rw [flipGL_empty, map_conj_one_eq]

omit [Finite G] in
theorem MinusFieldCover.exists_theta_of_images (C : MinusFieldCover e ι k) (hF : 5 ≤ Nat.card F)
    {U V : Subgroup G} (hUE : U ≤ minusNeighbourCore e k) (hVE : V ≤ minusNeighbourCore e k)
    (hUp : ⁅U, U⁆ = U) (hVp : ⁅V, V⁆ = V) {a : ℕ} (ha : a + 3 ≤ r + 1)
    (P : Finset (Fin (r + 1)))
    (hU : ((U.subgroupOf (minusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      (siegelBlockGL F (consecutiveBlock (r + 1) a 2)).map
        (MulAut.conj (flipGL F P)).toMonoidHom)
    (hV : ((V.subgroupOf (minusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      (siegelBlockGL F (consecutiveBlock (r + 1) (a + 1) 2)).map
        (MulAut.conj (flipGL F P)).toMonoidHom) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = U ∧ (B23 F).map θ = V := by
  refine C.exists_theta hF (sup_le hUE hVE) le_sup_left le_sup_right hUp hVp ha P ?_ hU hV
  rw [Subgroup.subgroupOf_sup hUE hVE, Subgroup.map_sup, Subgroup.map_sup, hU, hV,
    ← map_B12_modelTheta a ha P, ← map_B23_modelTheta a ha P, ← Subgroup.map_sup,
    CFSG.ClassicalInvolution.WeakCT.B12_sup_B23, ← MonoidHom.range_eq_map, range_modelTheta]

theorem exists_theta_minusNode (hr : 3 ≤ r) (hC : ∀ k, MinusFieldCover e ι k)
    (hK : 4 ≤ Nat.card K) (hF : 5 ≤ Nat.card F) {i j : Fin (r + 2)} (hij : edgeD (r + 2) i j) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = minusNode (hC 0) i ∧
      (B23 F).map θ = minusNode (hC 0) j := by
  have hF4 : 4 ≤ Nat.card F := by omega
  have hcb : ∀ a, a + 2 ≤ r + 1 → 2 ≤ (consecutiveBlock (r + 1) a 2).card := fun a ha =>
    (card_consecutiveBlock_two ha).ge
  unfold edgeD at hij
  rcases hij with ⟨hij, hjn⟩ | ⟨hi, hj⟩
  · by_cases hjr : j.val + 1 ≤ r
    ·
      have hir : i.val + 1 ≤ r := by omega
      rw [minusNode_of_le _ hir, minusNode_of_le _ hjr]
      by_cases hi0 : i.val = 0
      · have hki : Fin.last r ∉ consecutiveBlock (r + 1) i.val 2 := by
          rw [mem_consecutiveBlock, Fin.val_last]
          omega
        have hkj : Fin.last r ∉ consecutiveBlock (r + 1) j.val 2 := by
          rw [mem_consecutiveBlock, Fin.val_last]
          omega
        have hU := (hC (Fin.last r)).map_levelCore hK hF4 hki (hcb _ (by omega))
        have hV := (hC (Fin.last r)).map_levelCore hK hF4 hkj (hcb _ (by omega))
        rw [castSuccPlanes_preimagePlanes_last (by omega)] at hU hV
        refine (hC (Fin.last r)).exists_theta_of_images hF
          (minusLevelCore_le_minusNeighbourCore e hki) (minusLevelCore_le_minusNeighbourCore e hkj)
          (commutator_centralizerPerfectCore _) (commutator_centralizerPerfectCore _)
          (a := i.val) (by omega) ∅ ?_ ?_
        · rw [hU, map_conj_flipGL_empty]
        · rw [hV, map_conj_flipGL_empty, ← hij]
      · have h0i : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) i.val 2 := by
          rw [mem_consecutiveBlock, Fin.val_zero]
          omega
        have h0j : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) j.val 2 := by
          rw [mem_consecutiveBlock, Fin.val_zero]
          omega
        have hU := (hC 0).map_levelCore hK hF4 h0i (hcb _ (by omega))
        have hV := (hC 0).map_levelCore hK hF4 h0j (hcb _ (by omega))
        rw [castSuccPlanes_preimagePlanes_zero (by omega) hir] at hU
        rw [castSuccPlanes_preimagePlanes_zero (by omega) hjr] at hV
        refine (hC 0).exists_theta_of_images hF
          (minusLevelCore_le_minusNeighbourCore e h0i) (minusLevelCore_le_minusNeighbourCore e h0j)
          (commutator_centralizerPerfectCore _) (commutator_centralizerPerfectCore _)
          (a := i.val - 1) (by omega) ∅ ?_ ?_
        · rw [hU, map_conj_flipGL_empty]
        · rw [hV, map_conj_flipGL_empty, show j.val - 1 = i.val - 1 + 1 by omega]
    ·
      have hjr' : j.val = r := by omega
      have hir : i.val + 1 ≤ r := by omega
      rw [minusNode_of_le _ hir, minusNode_of_eq _ hjr']
      have h0 : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) i.val 2 := by
        rw [mem_consecutiveBlock, Fin.val_zero]
        omega
      have hU := (hC 0).map_levelCore hK hF4 h0 (hcb _ (by omega))
      rw [castSuccPlanes_preimagePlanes_zero (by omega) hir, show i.val - 1 = r - 2 by omega] at hU
      have hV := (hC 0).map_lift (forkBlock_le_statedOmega hF4 (by omega) ∅)
        (commutator_forkBlock hF4 (by omega) ∅)
      refine (hC 0).exists_theta_of_images hF (minusLevelCore_le_minusNeighbourCore e h0)
        ((hC 0).lift_le _) (commutator_centralizerPerfectCore _) ((hC 0).commutator_lift _)
        (a := r - 2) (by omega) ∅ ?_ ?_
      · rw [hU, map_conj_flipGL_empty]
      · rw [hV, forkBlock, show r - 2 + 1 = r - 1 by omega]
  ·
    have hir : i.val + 1 ≤ r := by omega
    have hj' : j.val = r + 1 := by omega
    rw [minusNode_of_le _ hir, minusNode_of_eq_succ _ hj']
    have h0 : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) i.val 2 := by
      rw [mem_consecutiveBlock, Fin.val_zero]
      omega
    have hU := (hC 0).map_levelCore hK hF4 h0 (hcb _ (by omega))
    rw [castSuccPlanes_preimagePlanes_zero (by omega) hir, show i.val - 1 = r - 2 by omega] at hU
    have hV := (hC 0).map_lift (forkBlock_le_statedOmega hF4 (by omega) {Fin.last r})
      (commutator_forkBlock hF4 (by omega) {Fin.last r})
    have hdisj : Disjoint (consecutiveBlock (r + 1) (r - 2) 2) {Fin.last r} := by
      rw [Finset.disjoint_singleton_right, mem_consecutiveBlock, Fin.val_last]
      omega
    refine (hC 0).exists_theta_of_images hF (minusLevelCore_le_minusNeighbourCore e h0)
      ((hC 0).lift_le _) (commutator_centralizerPerfectCore _) ((hC 0).commutator_lift _)
      (a := r - 2) (by omega) {Fin.last r} ?_ ?_
    · rw [hU, map_flipGL_siegelBlockGL_of_disjoint hdisj]
    · rw [hV, forkBlock, show r - 2 + 1 = r - 1 by omega]

end Pairs

section Commute

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}

omit [Finite F] in
theorem map_statedOmega_spEmbedGL_le_suppGL {m : ℕ} (I : Finset (Fin m)) :
    (StatedOmega (StatedQuadPlus I.card F)).map (spEmbedGL (planeEnum I) (planeEnum_injective I)) ≤
      suppGL F (planeCoords I) := by
  have h := (map_statedOmega_le_inf_suppGL (F := F) (planeEnum_injective I)).trans inf_le_right
  rwa [SymplecticPilot.range_sumMap_eq_planeCoords (SymplecticPilot.range_planeEnum I)] at h

theorem minusLevelCore_le_centralizer_minusPieceCore (hr : 3 ≤ r) [CharP F 2]
    (hC : ∀ k, MinusFieldCover e ι k) (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) {j : ℕ}
    (hj : j + 2 ≤ r) :
    minusLevelCore e (consecutiveBlock (r + 1) j 2) ≤
      centralizer (minusPieceCore e {Fin.last r} : Set G) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := consecutiveBlock (r + 1) j 2 ∪ {Fin.last r}) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      have h1 := Finset.card_union_le (consecutiveBlock (r + 1) j 2) {Fin.last r}
      rw [card_consecutiveBlock_two (by omega), Finset.card_singleton] at h1
      omega)
  have hkJ : k ∉ consecutiveBlock (r + 1) j 2 := fun h => hk (Finset.mem_union_left _ h)
  have hkI : k ∉ ({Fin.last r} : Finset (Fin (r + 1))) := fun h => hk (Finset.mem_union_right _ h)
  have hU := (hC k).map_levelCore hK hF hkJ (card_consecutiveBlock_two (by omega)).ge
  have hV := (hC k).map_pieceCore hK hF hkI (Finset.singleton_nonempty _)
  have hdisj : Disjoint (castSuccPlanes (preimagePlanes k (consecutiveBlock (r + 1) j 2)))
      (insert (Fin.last r) (castSuccPlanes (preimagePlanes k {Fin.last r}))) := by
    rw [Finset.disjoint_insert_right]
    refine ⟨last_notMem_castSuccPlanes _, disjoint_castSuccPlanes_preimagePlanes ?_⟩
    rw [Finset.disjoint_singleton_right, mem_consecutiveBlock, Fin.val_last]
    omega
  refine (hC k).le_centralizer (minusLevelCore_le_minusNeighbourCore e hkJ)
    (minusPieceCore_le_minusNeighbourCore e hkI) (commutator_centralizerPerfectCore _) ?_
  intro x hx y hy
  rw [hU] at hx
  rw [hV] at hy
  exact commute_of_mem_suppGL_of_disjoint (disjoint_planeCoords hdisj)
    (siegelBlockGL_le_suppGL _ hx) (map_statedOmega_spEmbedGL_le_suppGL _ hy)

theorem lift_forkBlock_le_centralizer (C₀ : MinusFieldCover e ι 0) (hr : 2 ≤ r)
    (hF : 4 ≤ Nat.card F) :
    C₀.lift (forkBlock F r ∅) ≤ centralizer (C₀.lift (forkBlock F r {Fin.last r}) : Set G) := by
  have hU := C₀.map_lift (forkBlock_le_statedOmega hF (by omega) ∅)
    (commutator_forkBlock hF (by omega) ∅)
  have hV := C₀.map_lift (forkBlock_le_statedOmega hF (by omega) {Fin.last r})
    (commutator_forkBlock hF (by omega) {Fin.last r})
  have hPB : consecutiveBlock (r + 1) (r - 1) 2 ∩ {Fin.last r} = {Fin.last r} := by
    rw [Finset.inter_singleton_of_mem]
    rw [mem_consecutiveBlock, Fin.val_last]
    omega
  refine C₀.le_centralizer (C₀.lift_le _) (C₀.lift_le _) (C₀.commutator_lift _) ?_
  intro x hx y hy
  rw [hU, forkBlock, map_conj_flipGL_empty] at hx
  rw [hV, forkBlock] at hy
  exact commute_siegelBlockGL_flip hF (card_consecutiveBlock_two (by omega)) hPB hx hy

end Commute

end CFSG.SeitzReduction.OmegaPilot
