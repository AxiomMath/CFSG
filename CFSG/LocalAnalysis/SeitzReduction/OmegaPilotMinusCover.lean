module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverLevi
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPieces
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeEnum planeEnum_injective liftParam
  planeTorusParam planeOf diagSpEntry diagSpEntry_inl diagSpEntry_inr diagSpEntry_liftParam
  mem_coords_planeOf)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open scoped MatrixGroups

section Param

variable (F : Type) [Field F] (r : ℕ)

@[expose] def snocOneParam : (Fin r → Fˣ) →* (Fin (r + 1) → Fˣ) where
  toFun s := Fin.snoc (α := fun _ => Fˣ) s 1
  map_one' := by
    funext x
    refine Fin.lastCases ?_ (fun j => ?_) x <;> simp
  map_mul' s t := by
    funext x
    refine Fin.lastCases ?_ (fun j => ?_) x <;> simp

variable {F r}

@[simp] theorem snocOneParam_castSucc (s : Fin r → Fˣ) (i : Fin r) : snocOneParam F r s i.castSucc = s i := by
  simp [snocOneParam]

@[simp] theorem snocOneParam_last (s : Fin r → Fˣ) : snocOneParam F r s (Fin.last r) = 1 := by
  simp [snocOneParam]

theorem diagSpEntry_snocOneParam_sumMap (s : Fin r → Fˣ) (u : Fin r ⊕ Fin r) :
    diagSpEntry (snocOneParam F r s) (Sum.map Fin.castSucc Fin.castSucc u) = diagSpEntry s u := by
  rcases u with i | i <;> simp [diagSpEntry]

theorem diagSpEntry_snocOneParam_of_planeOf (s : Fin r → Fˣ) {u : Fin (r + 1) ⊕ Fin (r + 1)}
    (hu : planeOf u = Fin.last r) : diagSpEntry (snocOneParam F r s) u = 1 := by
  rcases u with i | i
  · have hi : i = Fin.last r := hu
    subst hi
    simp [diagSpEntry]
  · have hi : i = Fin.last r := hu
    subst hi
    simp [diagSpEntry]

theorem exists_sumMap_castSucc_eq {u : Fin (r + 1) ⊕ Fin (r + 1)} (hu : planeOf u ≠ Fin.last r) :
    ∃ u' : Fin r ⊕ Fin r, Sum.map Fin.castSucc Fin.castSucc u' = u := by
  rcases u with i | i
  · exact ⟨.inl (i.castPred hu), congrArg Sum.inl (Fin.castSucc_castPred i hu)⟩
  · exact ⟨.inr (i.castPred hu), congrArg Sum.inr (Fin.castSucc_castPred i hu)⟩

theorem planeOf_sumMap_castSucc (u : Fin r ⊕ Fin r) :
    planeOf (Sum.map Fin.castSucc Fin.castSucc u) = (planeOf u).castSucc := by
  rcases u with i | i <;> rfl

@[expose] def castSuccPlanes (J : Finset (Fin r)) : Finset (Fin (r + 1)) :=
  J.map Fin.castSuccEmb

theorem mem_castSuccPlanes {J : Finset (Fin r)} {x : Fin (r + 1)} :
    x ∈ castSuccPlanes J ↔ ∃ i ∈ J, i.castSucc = x := by
  simp [castSuccPlanes]

theorem castSucc_mem_castSuccPlanes {J : Finset (Fin r)} {i : Fin r} :
    i.castSucc ∈ castSuccPlanes J ↔ i ∈ J := by
  simp [castSuccPlanes]

theorem last_notMem_castSuccPlanes (J : Finset (Fin r)) : Fin.last r ∉ castSuccPlanes J := by
  rw [mem_castSuccPlanes]
  rintro ⟨i, -, h⟩
  exact Fin.castSucc_ne_last i h

theorem card_castSuccPlanes (J : Finset (Fin r)) : (castSuccPlanes J).card = J.card := by
  simp [castSuccPlanes]

theorem sameSide_sumMap_castSucc {J : Finset (Fin r)} {u v : Fin r ⊕ Fin r}
    (h : SameSide J u v) :
    SameSide (castSuccPlanes J) (Sum.map Fin.castSucc Fin.castSucc u)
      (Sum.map Fin.castSucc Fin.castSucc v) := by
  rcases h with ⟨i, hi, j, hj, rfl, rfl⟩ | ⟨i, hi, j, hj, rfl, rfl⟩
  · exact Or.inl ⟨i.castSucc, castSucc_mem_castSuccPlanes.2 hi, j.castSucc,
      castSucc_mem_castSuccPlanes.2 hj, rfl, rfl⟩
  · exact Or.inr ⟨i.castSucc, castSucc_mem_castSuccPlanes.2 hi, j.castSucc,
      castSucc_mem_castSuccPlanes.2 hj, rfl, rfl⟩

end Param

section ModelPieces

variable {K : Type} [Field K] {F : Type} [Field F] {r : ℕ}

theorem exists_mem_levelParam_diagSpEntry_ne_one {κ : Kˣ} (hκ : κ * κ ≠ 1)
    (J : Finset (Fin r)) (u : Fin r ⊕ Fin r) :
    ∃ t ∈ levelParam (K := K) J, diagSpEntry t u ≠ 1 := by
  have h1 : (κ : K) ≠ 1 := fun e =>
    SymplecticPilot.units_ne_one_of_mul_self_ne_one hκ (Units.ext e)
  have h2 : ((κ⁻¹ : Kˣ) : K) ≠ 1 := fun e =>
    SymplecticPilot.units_ne_one_of_mul_self_ne_one hκ (inv_eq_one.1 (Units.ext e))
  refine ⟨levelVec (insert (planeOf u) J) κ,
    levelParam_anti (Finset.subset_insert _ _) (levelVec_mem_levelParam _ κ), ?_⟩
  rcases u with i | i
  · have hm : i ∈ insert i J := Finset.mem_insert_self _ _
    simpa [levelVec, planeOf, hm] using h1
  · have hm : i ∈ insert i J := Finset.mem_insert_self _ _
    simpa [levelVec, planeOf, hm] using h2

theorem perfectCore_statedOmega_inf_centralizer_snocLevel [Finite F] (hF : 4 ≤ Nat.card F)
    (ι : K →+* F) {κ : Kˣ} (hκ : κ * κ ≠ 1) {J : Finset (Fin r)} (hJ : 2 ≤ J.card) :
    perfectCore (StatedOmega (StatedQuadPlus (r + 1) F) ⊓
        centralizer (diagOmega F (r + 1) '' (snocOneParam F r '' (liftParam ι ''
          ((levelParam J : Subgroup (Fin r → Kˣ)) : Set (Fin r → Kˣ)))))) =
      siegelBlockGL F (castSuccPlanes J) := by
  obtain ⟨μ, hμ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hF
  have hJ' : 2 ≤ (castSuccPlanes J).card := by rwa [card_castSuccPlanes]
  have hι : Function.Injective ι := ι.injective
  rw [perfectCore_statedOmega_inf_centralizer_eq_level_of_free hF hJ'
    (last_notMem_castSuccPlanes J) hμ _ ?_ ?_, siegelBlockGL_eq_map_omegaLeviSL hF hJ']
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ x hx y hy
    obtain ⟨i, hi, rfl⟩ := mem_castSuccPlanes.1 hx
    obtain ⟨j, hj, rfl⟩ := mem_castSuccPlanes.1 hy
    rw [snocOneParam_castSucc, snocOneParam_castSucc]
    simp only [liftParam, ht i hi j hj]
  · intro u v huv hss hpp
    have hlast : ∀ u v : Fin (r + 1) ⊕ Fin (r + 1), planeOf u = Fin.last r →
        planeOf v ≠ Fin.last r → ∃ s ∈ snocOneParam F r '' (liftParam ι ''
          ((levelParam J : Subgroup (Fin r → Kˣ)) : Set (Fin r → Kˣ))),
          diagSpEntry s u ≠ diagSpEntry s v := by
      intro u v hu hv
      obtain ⟨v', rfl⟩ := exists_sumMap_castSucc_eq hv
      obtain ⟨t, ht, hne⟩ := exists_mem_levelParam_diagSpEntry_ne_one hκ J v'
      refine ⟨snocOneParam F r (liftParam ι t), ⟨_, ⟨t, ht, rfl⟩, rfl⟩, ?_⟩
      rw [diagSpEntry_snocOneParam_of_planeOf _ hu, diagSpEntry_snocOneParam_sumMap,
        diagSpEntry_liftParam]
      intro h
      apply hne
      apply hι
      rw [← h, map_one]
    by_cases hu : planeOf u = Fin.last r
    · exact hlast u v hu (fun hv => hpp ⟨hu, hv⟩)
    · by_cases hv : planeOf v = Fin.last r
      · obtain ⟨s, hs, hne⟩ := hlast v u hv hu
        exact ⟨s, hs, fun h => hne h.symm⟩
      · obtain ⟨u', rfl⟩ := exists_sumMap_castSucc_eq hu
        obtain ⟨v', rfl⟩ := exists_sumMap_castSucc_eq hv
        have huv' : u' ≠ v' := fun h => huv (h ▸ rfl)
        have hss' : ¬ SameSide J u' v' := fun h => hss (sameSide_sumMap_castSucc h)
        obtain ⟨t, ht, hne⟩ := exists_mem_levelParam_diagSpEntry_ne hκ huv' hss'
        refine ⟨snocOneParam F r (liftParam ι t), ⟨_, ⟨t, ht, rfl⟩, rfl⟩, ?_⟩
        rw [diagSpEntry_snocOneParam_sumMap, diagSpEntry_snocOneParam_sumMap, diagSpEntry_liftParam,
          diagSpEntry_liftParam]
        exact fun h => hne (hι h)

theorem perfectCore_statedOmega_inf_centralizer_snocPlane [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (ι : K →+* F) {κ : Kˣ} (hκ : κ * κ ≠ 1) {I : Finset (Fin r)}
    (hI : I.Nonempty) :
    perfectCore (StatedOmega (StatedQuadPlus (r + 1) F) ⊓
        centralizer (diagOmega F (r + 1) '' (snocOneParam F r '' (liftParam ι ''
          ((planeTorusParam K I : Subgroup (Fin r → Kˣ)) : Set (Fin r → Kˣ)))))) =
      (StatedOmega (StatedQuadPlus (insert (Fin.last r) (castSuccPlanes I)).card F)).map
        (spEmbedGL (planeEnum (insert (Fin.last r) (castSuccPlanes I)))
          (planeEnum_injective _)) := by
  have hι : Function.Injective ι := ι.injective
  have hI2 : 2 ≤ (insert (Fin.last r) (castSuccPlanes I)).card := by
    rw [Finset.card_insert_of_notMem (last_notMem_castSuccPlanes I), card_castSuccPlanes]
    have := hI.card_pos
    omega
  have h1 : (κ : K) ≠ 1 := fun e =>
    SymplecticPilot.units_ne_one_of_mul_self_ne_one hκ (Units.ext e)
  have h2 : ((κ⁻¹ : Kˣ) : K) ≠ 1 := fun e =>
    SymplecticPilot.units_ne_one_of_mul_self_ne_one hκ (inv_eq_one.1 (Units.ext e))
  refine perfectCore_statedOmega_inf_centralizer_eq_map_of_two_le hF hI2 _ ?_ ?_
  ·
    have hone : ∀ t ∈ planeTorusParam K I, ∀ a ∈ planeCoords (insert (Fin.last r)
        (castSuccPlanes I)), diagSpEntry (snocOneParam F r (liftParam ι t)) a = 1 := by
      intro t ht a ha
      rw [SymplecticPilot.mem_planeCoords, Finset.mem_insert] at ha
      rcases ha with ha | ha
      · exact diagSpEntry_snocOneParam_of_planeOf _ ha
      · have hal : planeOf a ≠ Fin.last r := fun h =>
          last_notMem_castSuccPlanes I (h ▸ ha)
        obtain ⟨a', rfl⟩ := exists_sumMap_castSucc_eq hal
        rw [planeOf_sumMap_castSucc, castSucc_mem_castSuccPlanes] at ha
        rw [diagSpEntry_snocOneParam_sumMap, diagSpEntry_liftParam]
        have hta : t (planeOf a') = 1 := ht _ ha
        rcases a' with i | i
        · simp only [planeOf, Sum.elim_inl, id] at hta
          simp [diagSpEntry, hta]
        · simp only [planeOf, Sum.elim_inr, id] at hta
          simp [diagSpEntry, hta]
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ a ha b hb
    rw [hone t ht a ha, hone t ht b hb]
  ·
    have key : ∀ a b : Fin (r + 1) ⊕ Fin (r + 1), a ≠ b →
        a ∉ planeCoords (insert (Fin.last r) (castSuccPlanes I)) →
        ∃ s ∈ snocOneParam F r '' (liftParam ι ''
          ((planeTorusParam K I : Subgroup (Fin r → Kˣ)) : Set (Fin r → Kˣ))),
          diagSpEntry s a ≠ diagSpEntry s b := by
      intro a b hab ha
      rw [SymplecticPilot.mem_planeCoords, Finset.mem_insert, not_or] at ha
      obtain ⟨a', rfl⟩ := exists_sumMap_castSucc_eq ha.1
      have ha' : planeOf a' ∉ I := by
        intro h
        apply ha.2
        rw [planeOf_sumMap_castSucc, castSucc_mem_castSuccPlanes]
        exact h
      have hmem : Pi.mulSingle (planeOf a') κ ∈ planeTorusParam K I := by
        intro i hi
        exact Pi.mulSingle_eq_of_ne (M := fun _ => Kˣ) (fun h : i = planeOf a' => ha' (h ▸ hi)) κ
      refine ⟨snocOneParam F r (liftParam ι (Pi.mulSingle (planeOf a') κ)),
        ⟨_, ⟨_, hmem, rfl⟩, rfl⟩, ?_⟩
      rw [diagSpEntry_snocOneParam_sumMap, diagSpEntry_liftParam]
      by_cases hb : planeOf b = Fin.last r
      · rw [diagSpEntry_snocOneParam_of_planeOf _ hb]
        intro h
        have h' : diagSpEntry (Pi.mulSingle (planeOf a') κ) a' = 1 := hι (by rw [h, map_one])
        rcases a' with i | i
        · exact h1 (by simpa [diagSpEntry, planeOf] using h')
        · exact h2 (by simpa [diagSpEntry, planeOf] using h')
      · obtain ⟨b', rfl⟩ := exists_sumMap_castSucc_eq hb
        rw [diagSpEntry_snocOneParam_sumMap, diagSpEntry_liftParam]
        have hab' : a' ≠ b' := fun h => hab (h ▸ rfl)
        exact fun h => SymplecticPilot.diagSpEntry_mulSingle_ne hκ hab'
          (Or.inl (mem_coords_planeOf a')) (hι h)
    intro a b hab h
    rcases h with ha | hb
    · exact key a b hab ha
    · obtain ⟨s, hs, hne⟩ := key b a (Ne.symm hab) hb
      exact ⟨s, hs, fun h => hne h.symm⟩

end ModelPieces

section Diag

variable {K : Type} [Field K] {F : Type} [Field F] {r : ℕ}

@[expose] noncomputable def minusNeighbourDiag (ι : K →+* F) (k : Fin (r + 1)) :
    (Fin (r + 1) → Kˣ) →* GL (Fin (r + 1) ⊕ Fin (r + 1)) F :=
  (diagOmega F (r + 1)).comp ((snocOneParam F r).comp ((liftParamHom ι).comp (restrictParam k)))

theorem minusNeighbourDiag_apply (ι : K →+* F) (k : Fin (r + 1)) (t : Fin (r + 1) → Kˣ) :
    minusNeighbourDiag ι k t = diagOmega F (r + 1) (snocOneParam F r (liftParam ι (restrictParam k t))) :=
  rfl

theorem minusNeighbourDiag_mem_normalizer (ι : K →+* F) (k : Fin (r + 1)) (t : Fin (r + 1) → Kˣ) :
    minusNeighbourDiag ι k t ∈ normalizer (StatedOmega (StatedQuadPlus (r + 1) F) :
      Set (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) :=
  diagOmega_mem_normalizer _

theorem image_minusNeighbourDiag (ι : K →+* F) (k : Fin (r + 1)) (P : Set (Fin (r + 1) → Kˣ)) :
    minusNeighbourDiag ι k '' P =
      diagOmega F (r + 1) '' (snocOneParam F r '' (liftParam ι '' (restrictParam k '' P))) := by
  simp only [Set.image_image]
  rfl

theorem image_restrictParam_levelParam {k : Fin (r + 1)} {J : Finset (Fin (r + 1))}
    (hk : k ∉ J) :
    restrictParam k '' ((levelParam J : Subgroup (Fin (r + 1) → Kˣ)) : Set (Fin (r + 1) → Kˣ)) =
      ((levelParam (preimagePlanes k J) : Subgroup (Fin r → Kˣ)) : Set (Fin r → Kˣ)) := by
  have h := image_restrictParam_signedLevelParam (K := K) hk ∅
  rwa [signedLevelParam_of_disjoint (Finset.disjoint_empty_right J), preimagePlanes_empty,
    signedLevelParam_of_disjoint (Finset.disjoint_empty_right _)] at h

theorem image_restrictParam_planeTorusParam {k : Fin (r + 1)} {I : Finset (Fin (r + 1))}
    (hk : k ∉ I) :
    restrictParam k '' ((planeTorusParam K I : Subgroup (Fin (r + 1) → Kˣ)) :
        Set (Fin (r + 1) → Kˣ)) =
      ((planeTorusParam K (preimagePlanes k I) : Subgroup (Fin r → Kˣ)) : Set (Fin r → Kˣ)) := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    intro i hi
    exact ht _ (mem_preimagePlanes.1 hi)
  · intro hs
    refine ⟨Fin.insertNth (α := fun _ => Kˣ) k 1 s, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (fun h : x = k => hk (h ▸ hx))
      simp only [Fin.insertNth_apply_succAbove]
      exact hs i (mem_preimagePlanes.2 hx)
    · funext i
      simp only [restrictParam_apply, Fin.insertNth_apply_succAbove]

end Diag

section Cover

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}

structure MinusFieldCover
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c))
    (ι : K →+* F) (k : Fin (r + 1)) where
  π : minusNeighbourCore e k →* StatedOmega (StatedQuadPlus (r + 1) F)
  surjective : Function.Surjective π
  ker_le : π.ker ≤ center (minusNeighbourCore e k)
  equivariant : ∀ (t : Fin (r + 1) → Kˣ)
    (hN : ((e.symm ((isHypFrame_minus K hn b c).frameHom t) : L) : G) ∈
      normalizer (minusNeighbourCore e k : Set G)) (x : minusNeighbourCore e k),
    π ((minusNeighbourCore e k).normalizerMonoidHom ⟨_, hN⟩ x) =
      (StatedOmega (StatedQuadPlus (r + 1) F)).normalizerMonoidHom
        ⟨minusNeighbourDiag ι k t, minusNeighbourDiag_mem_normalizer ι k t⟩ (π x)

variable [Finite G] [Finite F]
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}
  {k : Fin (r + 1)}

theorem MinusFieldCover.map_levelCore (C : MinusFieldCover e ι k) (hK : 4 ≤ Nat.card K)
    (hF : 4 ≤ Nat.card F) {J : Finset (Fin (r + 1))} (hk : k ∉ J) (hJ : 2 ≤ J.card) :
    (((minusLevelCore e J).subgroupOf (minusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      siegelBlockGL F (castSuccPlanes (preimagePlanes k J)) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hK
  have hJ' : 2 ≤ (preimagePlanes k J).card := by
    rw [card_preimagePlanes hk]
    exact hJ
  have h := map_frameCore_eq_of_conjDiag_quot (isHypFrame_minus K hn b c) e
    (minusNeighbourDiag ι k) (minusNeighbourDiag_mem_normalizer ι k) (P := levelParam J)
    (X := modelToG e (minusPairTorus hn b c k))
    (modelToG_mono e (minusPairTorus_le_minusLevelTorus hk)) C.π C.surjective C.ker_le
    (fun t _ hN x => C.equivariant t hN x)
  rw [image_minusNeighbourDiag, image_restrictParam_levelParam hk,
    perfectCore_statedOmega_inf_centralizer_snocLevel hF ι hκ hJ'] at h
  exact h

theorem MinusFieldCover.map_pieceCore [CharP F 2] (C : MinusFieldCover e ι k)
    (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) {I : Finset (Fin (r + 1))} (hk : k ∉ I)
    (hI : I.Nonempty) :
    (((minusPieceCore e I).subgroupOf (minusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      (StatedOmega (StatedQuadPlus
          (insert (Fin.last r) (castSuccPlanes (preimagePlanes k I))).card F)).map
        (spEmbedGL (planeEnum (insert (Fin.last r) (castSuccPlanes (preimagePlanes k I))))
          (planeEnum_injective _)) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hK
  have hI' : (preimagePlanes k I).Nonempty := by
    rw [← Finset.card_pos, card_preimagePlanes hk]
    exact hI.card_pos
  have h := map_frameCore_eq_of_conjDiag_quot (isHypFrame_minus K hn b c) e
    (minusNeighbourDiag ι k) (minusNeighbourDiag_mem_normalizer ι k) (P := planeTorusParam K I)
    (X := modelToG e (minusPairTorus hn b c k))
    (modelToG_mono e (minusPairTorus_le_minusPlaneTorus hk)) C.π C.surjective C.ker_le
    (fun t _ hN x => C.equivariant t hN x)
  rw [image_minusNeighbourDiag, image_restrictParam_planeTorusParam hk,
    perfectCore_statedOmega_inf_centralizer_snocPlane hF ι hκ hI'] at h
  exact h

end Cover

section CoverPairs

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}
  {k : Fin (r + 1)}

theorem MinusFieldCover.ker_comp_subtype_le (C : MinusFieldCover e ι k) :
    ((StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp C.π).ker ≤
      center (minusNeighbourCore e k) := by
  intro x hx
  apply C.ker_le
  rw [MonoidHom.mem_ker] at hx ⊢
  exact Subtype.val_injective hx

theorem MinusFieldCover.exists_theta [Finite F] (C : MinusFieldCover e ι k) (hF : 5 ≤ Nat.card F)
    {M U V : Subgroup G} (hME : M ≤ minusNeighbourCore e k) (hUM : U ≤ M) (hVM : V ≤ M)
    (hUp : ⁅U, U⁆ = U) (hVp : ⁅V, V⁆ = V) {a : ℕ} (ha : a + 3 ≤ r + 1)
    (P : Finset (Fin (r + 1)))
    (hM : ((M.subgroupOf (minusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      (siegelBlockGL F (consecutiveBlock (r + 1) a 3)).map
        (MulAut.conj (flipGL F P)).toMonoidHom)
    (hU : ((U.subgroupOf (minusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      (siegelBlockGL F (consecutiveBlock (r + 1) a 2)).map
        (MulAut.conj (flipGL F P)).toMonoidHom)
    (hV : ((V.subgroupOf (minusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      (siegelBlockGL F (consecutiveBlock (r + 1) (a + 1) 2)).map
        (MulAut.conj (flipGL F P)).toMonoidHom) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = U ∧ (B23 F).map θ = V := by
  set E := minusNeighbourCore e k
  set π' : E →* GL (Fin (r + 1) ⊕ Fin (r + 1)) F :=
    (StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp C.π
  set ρ : M →* GL (Fin (r + 1) ⊕ Fin (r + 1)) F := π'.comp (Subgroup.inclusion hME)
  have hmap : ∀ A : Subgroup G, A ≤ M →
      (A.subgroupOf M).map ρ =
        ((A.subgroupOf E).map C.π).map (StatedOmega (StatedQuadPlus (r + 1) F)).subtype := by
    intro A hAM
    rw [← map_inclusion_subgroupOf hAM hME, Subgroup.map_map, Subgroup.map_map]
  refine exists_theta_of_central hF hUM hVM hUp hVp (modelTheta_injective a ha P) ρ ?_ ?_ ?_ ?_
  · rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self, hmap M le_rfl, hM,
      range_modelTheta]
  · intro x hx
    have hx' : Subgroup.inclusion hME x ∈ center E := C.ker_comp_subtype_le hx
    rw [mem_center_iff] at hx' ⊢
    intro y
    have h2 := congrArg Subtype.val (hx' (Subgroup.inclusion hME y))
    exact Subtype.ext h2
  · rw [hmap U hUM, hU, map_B12_modelTheta]
  · rw [hmap V hVM, hV, map_B23_modelTheta]

theorem MinusFieldCover.le_centralizer (C : MinusFieldCover e ι k) {A B : Subgroup G}
    (hA : A ≤ minusNeighbourCore e k) (hB : B ≤ minusNeighbourCore e k) (hBp : ⁅B, B⁆ = B)
    (h : ∀ x ∈ ((A.subgroupOf (minusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype,
      ∀ y ∈ ((B.subgroupOf (minusNeighbourCore e k)).map C.π).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype, Commute x y) :
    A ≤ centralizer (B : Set G) := by
  set E := minusNeighbourCore e k
  have hc := le_centralizer_of_map_commute C.ker_comp_subtype_le (A := A.subgroupOf E)
    (B := B.subgroupOf E) (commutator_subgroupOf_eq_of_le_perfect hB hBp)
    (fun a ha b hb => (h _ ⟨C.π a, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨C.π b, ⟨b, hb, rfl⟩, rfl⟩).eq)
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  have h1 := mem_centralizer_iff.1 (hc (show (⟨a, hA ha⟩ : E) ∈ A.subgroupOf E from ha))
    ⟨b, hB hb⟩ hb
  exact congrArg Subtype.val h1

end CoverPairs

end CFSG.SeitzReduction.OmegaPilot
