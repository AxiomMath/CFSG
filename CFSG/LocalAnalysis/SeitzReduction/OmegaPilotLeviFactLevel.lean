module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactBlock
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCores

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedMat spEmbedGL spEmbedMat_apply_image
  spEmbedMat_apply_of_not_mem leviEmbedGL mat_leviEmbedGL)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.SeitzReduction.SymplecticPilot (suppGL planeCoords mem_planeCoords planeOf planeEnum
  planeEnum_injective range_planeEnum range_sumMap_eq_planeCoords liftParam diagSpEntry
  diagSpEntry_inl diagSpEntry_inr diagSpEntry_liftParam commute_of_diag_iff siegelLeviGL
  siegelLevi)

variable {F : Type} [Field F] {k m : ℕ}

section Levi

theorem statedQuadPlus_eq_dotProduct (w : Fin k ⊕ Fin k → F) :
    StatedQuadPlus k F w = (w ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) :=
  rfl

theorem statedQuadPlus_fromBlocks_mulVec (A B : Matrix (Fin k) (Fin k) F)
    (v : Fin k ⊕ Fin k → F) :
    StatedQuadPlus k F (fromBlocks A 0 0 B *ᵥ v) =
      (v ∘ Sum.inl) ⬝ᵥ ((Aᵀ * B) *ᵥ (v ∘ Sum.inr)) := by
  rw [statedQuadPlus_eq_dotProduct, fromBlocks_mulVec]
  have h1 : (A *ᵥ v ∘ Sum.inl + (0 : Matrix (Fin k) (Fin k) F) *ᵥ v ∘ Sum.inr ⊕ᵥ
      ((0 : Matrix (Fin k) (Fin k) F) *ᵥ v ∘ Sum.inl + B *ᵥ v ∘ Sum.inr)) ∘ Sum.inl =
      A *ᵥ (v ∘ Sum.inl) := by
    funext i
    simp
  have h2 : (A *ᵥ v ∘ Sum.inl + (0 : Matrix (Fin k) (Fin k) F) *ᵥ v ∘ Sum.inr ⊕ᵥ
      ((0 : Matrix (Fin k) (Fin k) F) *ᵥ v ∘ Sum.inl + B *ᵥ v ∘ Sum.inr)) ∘ Sum.inr =
      B *ᵥ (v ∘ Sum.inr) := by
    funext i
    simp
  rw [h1, h2, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
    mulVec_mulVec]

theorem leviMat_isometry (A : GL (Fin k) F) (v : Fin k ⊕ Fin k → F) :
    StatedQuadPlus k F (fromBlocks (A : Matrix (Fin k) (Fin k) F) 0 0
      ((A⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F)ᵀ *ᵥ v) = StatedQuadPlus k F v := by
  rw [statedQuadPlus_fromBlocks_mulVec, ← transpose_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, transpose_one, one_mulVec]
  rfl

variable (F k) in
@[expose] noncomputable def omegaLeviGL : Subgroup (GL (Fin k ⊕ Fin k) F) :=
  (siegelLeviGL F k).map (StatedSp k F).subtype

variable (F k) in
@[expose] noncomputable def omegaLeviSL : Subgroup (GL (Fin k ⊕ Fin k) F) :=
  (siegelLevi F k).map (StatedSp k F).subtype

theorem coe_leviEmbedGL (A : GL (Fin k) F) :
    (((leviEmbedGL F k A : StatedSp k F) : GL (Fin k ⊕ Fin k) F) :
      Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) =
      fromBlocks (A : Matrix (Fin k) (Fin k) F) 0 0
        ((A⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F)ᵀ := by
  rw [← mat_apply, mat_leviEmbedGL]

theorem mem_omegaLeviGL {x : GL (Fin k ⊕ Fin k) F} :
    x ∈ omegaLeviGL F k ↔ ∃ A : GL (Fin k) F, ((leviEmbedGL F k A : StatedSp k F) :
      GL (Fin k ⊕ Fin k) F) = x := by
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨_, ⟨A, rfl⟩, rfl⟩

theorem isometry_of_mem_omegaLeviGL {x : GL (Fin k ⊕ Fin k) F} (hx : x ∈ omegaLeviGL F k)
    (v : Fin k ⊕ Fin k → F) :
    StatedQuadPlus k F ((x : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) *ᵥ v) =
      StatedQuadPlus k F v := by
  obtain ⟨A, rfl⟩ := mem_omegaLeviGL.1 hx
  rw [coe_leviEmbedGL]
  exact leviMat_isometry A v

theorem omegaLeviSL_le_omegaLeviGL : omegaLeviSL F k ≤ omegaLeviGL F k := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  exact ⟨_, ⟨Matrix.SpecialLinearGroup.toGL A, rfl⟩, rfl⟩

theorem mem_omegaLeviGL_of_isometry {y : GL (Fin k ⊕ Fin k) F}
    (hiso : ∀ v, StatedQuadPlus k F ((y : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) *ᵥ v) =
      StatedQuadPlus k F v)
    (h12 : ∀ i j, (y : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) (Sum.inl i) (Sum.inr j) = 0)
    (h21 : ∀ i j, (y : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) (Sum.inr i) (Sum.inl j) = 0) :
    y ∈ omegaLeviGL F k := by
  set M : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F :=
    (y : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) with hM
  have hMb : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks M]
    congr 1
    · ext i j
      exact h12 i j
    · ext i j
      exact h21 i j
  have hN : (M.toBlocks₁₁)ᵀ * M.toBlocks₂₂ = 1 := by
    ext i j
    have h := hiso (Sum.elim (Pi.single i 1) (Pi.single j 1))
    rw [hMb, statedQuadPlus_fromBlocks_mulVec, statedQuadPlus_eq_dotProduct] at h
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_single_one, single_dotProduct,
      one_mul] at h
    have h' : ((M.toBlocks₁₁)ᵀ * M.toBlocks₂₂) i j = (Pi.single j (1 : F) : Fin k → F) i := h
    rw [h', Matrix.one_apply, Pi.single_apply]
  have hDA : (M.toBlocks₂₂)ᵀ * M.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.transpose hN
    simpa [Matrix.transpose_mul] using this
  set A : GL (Fin k) F := ⟨M.toBlocks₁₁, (M.toBlocks₂₂)ᵀ, mul_eq_one_comm.1 hDA, hDA⟩
  refine mem_omegaLeviGL.2 ⟨A, Units.ext ?_⟩
  rw [coe_leviEmbedGL]
  change fromBlocks M.toBlocks₁₁ 0 0 ((M.toBlocks₂₂)ᵀ)ᵀ = M
  rw [transpose_transpose, ← hMb]

theorem commutator_omegaLeviGL_le : ⁅omegaLeviGL F k, omegaLeviGL F k⁆ ≤ omegaLeviSL F k := by
  rw [omegaLeviGL, omegaLeviSL, ← Subgroup.map_commutator]
  refine map_mono (Subgroup.commutator_le.2 fun g hg g' hg' => ?_)
  rw [commutatorElement_def]
  exact SymplecticPilot.commutator_mem_siegelLevi hg hg'

theorem commutator_omegaLeviSL (hF : 4 ≤ Nat.card F) (hk : 2 ≤ k) :
    ⁅omegaLeviSL F k, omegaLeviSL F k⁆ = omegaLeviSL F k := by
  rw [omegaLeviSL, ← Subgroup.map_commutator,
    Subgroup.isPerfect_iff.1 (SymplecticPilot.isQuasisimple_siegelLevi hF hk).1]

theorem omegaLeviGL_le_isometryClosure : omegaLeviGL F k ≤ isometryClosure F k :=
  fun _ hx => Subgroup.subset_closure (isometry_of_mem_omegaLeviGL hx)

theorem omegaLeviSL_le_statedOmega (hF : 4 ≤ Nat.card F) (hk : 2 ≤ k) :
    omegaLeviSL F k ≤ StatedOmega (StatedQuadPlus k F) := by
  rw [← commutator_omegaLeviSL hF hk, statedOmega_eq_commutator_isometryClosure]
  have h := omegaLeviSL_le_omegaLeviGL.trans (omegaLeviGL_le_isometryClosure (F := F) (k := k))
  exact Subgroup.commutator_mono h h

@[expose] noncomputable def omegaLeviSLEquiv :
    Matrix.SpecialLinearGroup (Fin k) F ≃* omegaLeviSL F k :=
  SymplecticPilot.siegelLeviEquiv.trans
    ((siegelLevi F k).equivMapOfInjective _ (StatedSp k F).subtype_injective)

end Levi

section LevelFact

@[expose] def SameSide (J : Finset (Fin m)) (a b : Fin m ⊕ Fin m) : Prop :=
  (∃ i ∈ J, ∃ j ∈ J, a = Sum.inl i ∧ b = Sum.inl j) ∨
    (∃ i ∈ J, ∃ j ∈ J, a = Sum.inr i ∧ b = Sum.inr j)

theorem SameSide.mem_planeCoords {J : Finset (Fin m)} {a b : Fin m ⊕ Fin m}
    (h : SameSide J a b) : a ∈ planeCoords J ∧ b ∈ planeCoords J := by
  rcases h with ⟨i, hi, j, hj, rfl, rfl⟩ | ⟨i, hi, j, hj, rfl, rfl⟩
  · exact ⟨hi, hj⟩
  · exact ⟨hi, hj⟩

theorem perfectCore_statedOmega_inf_centralizer_eq_level [Finite F] (hF : 4 ≤ Nat.card F)
    {J : Finset (Fin m)} (hJ : 2 ≤ J.card) (D : Set (Fin m → Fˣ))
    (hlevel : ∀ s ∈ D, ∀ i ∈ J, ∀ j ∈ J, s i = s j)
    (hsep : ∀ a b : Fin m ⊕ Fin m, a ≠ b → ¬ SameSide J a b →
      ∃ s ∈ D, diagSpEntry s a ≠ diagSpEntry s b) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓ centralizer (diagOmega F m '' D)) =
      (omegaLeviSL F J.card).map (spEmbedGL (planeEnum J) (planeEnum_injective J)) := by
  set σ := planeEnum J with hσdef
  have hσ : Function.Injective σ := planeEnum_injective J
  have hS : Set.range (Sum.map σ σ) = planeCoords J :=
    range_sumMap_eq_planeCoords (range_planeEnum J)
  have hσJ : ∀ i, σ i ∈ J := fun i => by
    have : σ i ∈ Set.range σ := ⟨i, rfl⟩
    rwa [range_planeEnum] at this
  set C := centralizer (diagOmega F m '' D)
  rw [SymplecticPilot.perfectCore_inf_centralizer_eq_perfectCore_inf_suppGL
      (T := Set.univ) (S := planeCoords J)
      (fun x _ a b hab => absurd ⟨Set.mem_univ a, Set.mem_univ b⟩ hab)
      (diagOmega F m '' D)
      (by rintro _ ⟨s, -, rfl⟩ a b hab; exact diagOmega_apply_ne s hab)
      (fun a _ b _ hab hS' => by
        obtain ⟨s, hs, hne⟩ := hsep a b hab (fun h => by
          rcases hS' with ha | hb
          · exact ha h.mem_planeCoords.1
          · exact hb h.mem_planeCoords.2)
        exact ⟨diagOmega F m s, ⟨s, hs, rfl⟩, by
          rw [diagOmega_apply_self, diagOmega_apply_self]; exact hne⟩)]
  rw [← hS]
  set B := StatedOmega (StatedQuadPlus m F) ⊓ suppGL F (Set.range (Sum.map σ σ)) ⊓ C
  have hB : B ≤ (omegaLeviGL F J.card).map (spEmbedGL σ hσ) := by
    intro x hx
    obtain ⟨hxOS, hxC⟩ := mem_inf.1 hx
    obtain ⟨y, hy, rfl⟩ := statedOmega_inf_suppGL_le_map_isometryClosure hσ hxOS
    refine ⟨y, mem_omegaLeviGL_of_isometry (isometry_of_mem_isometryClosure hy) ?_ ?_, rfl⟩
    · intro i i'
      have hab : (Sum.inl (σ i) : Fin m ⊕ Fin m) ≠ Sum.inr (σ i') := Sum.inl_ne_inr
      obtain ⟨s, hs, hne⟩ := hsep _ _ hab (by
        rintro (⟨_, _, _, _, -, h⟩ | ⟨_, _, _, _, h, -⟩)
        · exact Sum.inr_ne_inl h
        · exact Sum.inl_ne_inr h)
      have hc : Commute (spEmbedGL σ hσ y) (diagOmega F m s) :=
        ((mem_centralizer_iff.1 hxC) _ ⟨s, hs, rfl⟩).symm
      have h0 := (commute_of_diag_iff (fun a b hab => diagOmega_apply_ne s hab) _).1 hc
        (Sum.inl (σ i)) (Sum.inr (σ i')) (by
          rw [diagOmega_apply_self, diagOmega_apply_self]; exact hne)
      have he : ((spEmbedGL σ hσ y : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m)
          (Fin m ⊕ Fin m) F) (Sum.inl (σ i)) (Sum.inr (σ i')) =
          (y : Matrix (Fin J.card ⊕ Fin J.card) (Fin J.card ⊕ Fin J.card) F)
            (Sum.inl i) (Sum.inr i') :=
        spEmbedMat_apply_image hσ _ (Sum.inl i) (Sum.inr i')
      rw [← he]
      exact h0
    · intro i i'
      have hab : (Sum.inr (σ i) : Fin m ⊕ Fin m) ≠ Sum.inl (σ i') := Sum.inr_ne_inl
      obtain ⟨s, hs, hne⟩ := hsep _ _ hab (by
        rintro (⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, -, h⟩)
        · exact Sum.inr_ne_inl h
        · exact Sum.inl_ne_inr h)
      have hc : Commute (spEmbedGL σ hσ y) (diagOmega F m s) :=
        ((mem_centralizer_iff.1 hxC) _ ⟨s, hs, rfl⟩).symm
      have h0 := (commute_of_diag_iff (fun a b hab => diagOmega_apply_ne s hab) _).1 hc
        (Sum.inr (σ i)) (Sum.inl (σ i')) (by
          rw [diagOmega_apply_self, diagOmega_apply_self]; exact hne)
      have he : ((spEmbedGL σ hσ y : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m)
          (Fin m ⊕ Fin m) F) (Sum.inr (σ i)) (Sum.inl (σ i')) =
          (y : Matrix (Fin J.card ⊕ Fin J.card) (Fin J.card ⊕ Fin J.card) F)
            (Sum.inr i) (Sum.inl i') :=
        spEmbedMat_apply_image hσ _ (Sum.inr i) (Sum.inl i')
      rw [← he]
      exact h0
  have hLB : (omegaLeviSL F J.card).map (spEmbedGL σ hσ) ≤ B := by
    refine le_inf ((map_mono (omegaLeviSL_le_statedOmega hF hJ)).trans
      (map_statedOmega_le_inf_suppGL hσ)) ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨A, hA⟩ := mem_omegaLeviGL.1 (omegaLeviSL_le_omegaLeviGL hz)
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    refine ((commute_of_diag_iff (fun a b hab => diagOmega_apply_ne s hab) _).2
      fun a b hab => ?_).eq.symm
    rw [diagOmega_apply_self, diagOmega_apply_self] at hab
    have hne : a ≠ b := fun e => hab (e ▸ rfl)
    by_cases h : a ∈ Set.range (Sum.map σ σ) ∧ b ∈ Set.range (Sum.map σ σ)
    · obtain ⟨⟨p, rfl⟩, ⟨p', rfl⟩⟩ := h
      change spEmbedMat σ (z : Matrix (Fin J.card ⊕ Fin J.card) (Fin J.card ⊕ Fin J.card) F)
        (Sum.map σ σ p) (Sum.map σ σ p') = 0
      rw [spEmbedMat_apply_image hσ, ← hA, coe_leviEmbedGL]
      rcases p with i | i <;> rcases p' with i' | i'
      · exfalso
        apply hab
        simp only [Sum.map_inl, diagSpEntry_inl, hlevel s hs _ (hσJ i) _ (hσJ i')]
      · simp
      · simp
      · exfalso
        apply hab
        simp only [Sum.map_inr, diagSpEntry_inr, hlevel s hs _ (hσJ i) _ (hσJ i')]
    · change spEmbedMat σ (z : Matrix (Fin J.card ⊕ Fin J.card) (Fin J.card ⊕ Fin J.card) F) a b = 0
      rw [spEmbedMat_apply_of_not_mem _ h, Matrix.one_apply_ne hne]
  refine le_antisymm ?_ (le_perfectCore_of_perfect hLB
    (by rw [← Subgroup.map_commutator, commutator_omegaLeviSL hF hJ]))
  calc perfectCore B ≤ perfectCore ((omegaLeviGL F J.card).map (spEmbedGL σ hσ)) :=
        perfectCore_mono hB
    _ = (perfectCore (omegaLeviGL F J.card)).map (spEmbedGL σ hσ) :=
        (CFSG.Quasithin.map_perfectCore _ _).symm
    _ ≤ (omegaLeviSL F J.card).map (spEmbedGL σ hσ) := by
        refine map_mono ?_
        calc perfectCore (omegaLeviGL F J.card) =
              ⁅perfectCore (omegaLeviGL F J.card), perfectCore (omegaLeviGL F J.card)⁆ :=
              (perfectCore_perfect _).symm
          _ ≤ ⁅omegaLeviGL F J.card, omegaLeviGL F J.card⁆ :=
              Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)
          _ ≤ omegaLeviSL F J.card := commutator_omegaLeviGL_le

end LevelFact

section LevelLift

variable {K : Type} [Field K]

@[expose] def levelVec (J : Finset (Fin m)) (κ : Kˣ) : Fin m → Kˣ :=
  fun i => if i ∈ J then κ else 1

theorem levelVec_mem_levelParam (J : Finset (Fin m)) (κ : Kˣ) :
    levelVec J κ ∈ levelParam (K := K) J := fun i hi j hj => by
  simp only [levelVec, hi, hj, ite_true]

theorem exists_mem_levelParam_diagSpEntry_ne {κ : Kˣ} (hκ : κ * κ ≠ 1) {J : Finset (Fin m)}
    {a b : Fin m ⊕ Fin m} (hab : a ≠ b) (hJ : ¬ SameSide J a b) :
    ∃ t ∈ levelParam (K := K) J, diagSpEntry t a ≠ diagSpEntry t b := by
  by_cases ha : planeOf a ∈ J
  · by_cases hb : planeOf b ∈ J
    · have h3 : (κ : K) ≠ ((κ⁻¹ : Kˣ) : K) := fun e =>
        SymplecticPilot.units_ne_inv_of_mul_self_ne_one hκ (Units.ext e)
      refine ⟨levelVec J κ, levelVec_mem_levelParam J κ, ?_⟩
      rcases a with i | i <;> rcases b with j | j
      · exact absurd (Or.inl ⟨i, ha, j, hb, rfl, rfl⟩) hJ
      · have ha' : i ∈ J := ha
        have hb' : j ∈ J := hb
        simp only [diagSpEntry_inl, diagSpEntry_inr, levelVec, ha', hb', ite_true]
        exact h3
      · have ha' : i ∈ J := ha
        have hb' : j ∈ J := hb
        simp only [diagSpEntry_inl, diagSpEntry_inr, levelVec, ha', hb', ite_true]
        exact h3.symm
      · exact absurd (Or.inr ⟨i, ha, j, hb, rfl, rfl⟩) hJ
    · exact ⟨_, rootParam_le_levelParam hb (mulSingle_mem_rootParam _ κ),
        SymplecticPilot.diagSpEntry_mulSingle_ne hκ hab
          (Or.inr (SymplecticPilot.mem_coords_planeOf b))⟩
  · exact ⟨_, rootParam_le_levelParam ha (mulSingle_mem_rootParam _ κ),
      SymplecticPilot.diagSpEntry_mulSingle_ne hκ hab
        (Or.inl (SymplecticPilot.mem_coords_planeOf a))⟩

theorem perfectCore_statedOmega_inf_centralizer_levelTorus [Finite F] (hF : 4 ≤ Nat.card F)
    (ι : K →+* F) {κ : Kˣ} (hκ : κ * κ ≠ 1) {J : Finset (Fin m)} (hJ : 2 ≤ J.card) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓
        centralizer (diagOmega F m '' (liftParam ι ''
          ((levelParam J : Subgroup (Fin m → Kˣ)) : Set (Fin m → Kˣ))))) =
      (omegaLeviSL F J.card).map (spEmbedGL (planeEnum J) (planeEnum_injective J)) := by
  refine perfectCore_statedOmega_inf_centralizer_eq_level hF hJ _ ?_ (fun a b hab hJ' => ?_)
  · rintro _ ⟨t, ht, rfl⟩ i hi j hj
    simp only [liftParam, ht i hi j hj]
  · obtain ⟨t, ht, hne⟩ := exists_mem_levelParam_diagSpEntry_ne (K := K) hκ hab hJ'
    refine ⟨liftParam ι t, ⟨t, ht, rfl⟩, ?_⟩
    rw [diagSpEntry_liftParam, diagSpEntry_liftParam]
    exact fun h => hne (ι.injective h)

theorem perfectCore_statedOmega_inf_centralizer_levelTorus_of_four_le [Finite F]
    (hF : 4 ≤ Nat.card F) (ι : K →+* F) (hK : 4 ≤ Nat.card K) {J : Finset (Fin m)}
    (hJ : 2 ≤ J.card) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓
        centralizer (diagOmega F m '' (liftParam ι ''
          ((levelParam J : Subgroup (Fin m → Kˣ)) : Set (Fin m → Kˣ))))) =
      (omegaLeviSL F J.card).map (spEmbedGL (planeEnum J) (planeEnum_injective J)) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hK
  exact perfectCore_statedOmega_inf_centralizer_levelTorus hF ι hκ hJ

end LevelLift

end CFSG.SeitzReduction.OmegaPilot
