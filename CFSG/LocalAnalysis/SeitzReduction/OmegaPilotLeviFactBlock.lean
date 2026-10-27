module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFact
public import CFSG.LieType.Universal.SpinOmega.Center

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedMat spEmbedGL spEmbedMat_apply_image
  spEmbedMat_apply_of_not_mem spEmbedMat_mul spEmbedMat_one spEmbedMat_injective)
open CFSG.SeitzReduction.SymplecticPilot (suppGL mem_suppGL IsSuppMat planeCoords planeEnum
  planeEnum_injective range_planeEnum range_sumMap_eq_planeCoords planeTorusParam liftParam)

variable {F : Type} [Field F] {k m : ℕ}

section Sums

theorem sum_eq_sum_comp_sumMap {σ : Fin k → Fin m} (hσ : Function.Injective σ)
    (f : Fin m ⊕ Fin m → F) (hf : ∀ c, c ∉ Set.range (Sum.map σ σ) → f c = 0) :
    ∑ c, f c = ∑ y, f (Sum.map σ σ y) := by
  have hinj : Function.Injective (Sum.map σ σ : Fin k ⊕ Fin k → Fin m ⊕ Fin m) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  rw [← Finset.sum_image (s := Finset.univ) (fun x _ y _ h => hinj h)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun c _ hc => hf c ?_).symm
  rintro ⟨y, rfl⟩
  exact hc (Finset.mem_image_of_mem _ (Finset.mem_univ y))

theorem statedQuadPlus_split {σ : Fin k → Fin m} (hσ : Function.Injective σ)
    (u : Fin m ⊕ Fin m → F) :
    StatedQuadPlus m F u = StatedQuadPlus k F (u ∘ Sum.map σ σ) +
      ∑ i ∈ (Finset.univ.image σ)ᶜ, u (Sum.inl i) * u (Sum.inr i) := by
  unfold StatedQuadPlus
  rw [← Finset.sum_add_sum_compl (Finset.univ.image σ),
    Finset.sum_image (fun x _ y _ h => hσ h)]
  rfl

end Sums

section MulVec

variable {σ : Fin k → Fin m}

theorem spEmbedMat_mulVec_comp (hσ : Function.Injective σ)
    (g : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) (v : Fin m ⊕ Fin m → F) :
    (spEmbedMat σ g *ᵥ v) ∘ Sum.map σ σ = g *ᵥ (v ∘ Sum.map σ σ) := by
  have hinj : Function.Injective (Sum.map σ σ : Fin k ⊕ Fin k → Fin m ⊕ Fin m) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  funext x
  simp only [Function.comp_apply, mulVec, dotProduct]
  rw [sum_eq_sum_comp_sumMap hσ _ (fun c hc => by
    rw [spEmbedMat_apply_of_not_mem g (fun h => hc h.2),
      Matrix.one_apply_ne (fun e => hc ⟨x, e⟩), zero_mul])]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [spEmbedMat_apply_image hσ]

theorem spEmbedMat_mulVec_of_not_mem (g : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F)
    (v : Fin m ⊕ Fin m → F) {a : Fin m ⊕ Fin m} (ha : a ∉ Set.range (Sum.map σ σ)) :
    (spEmbedMat σ g *ᵥ v) a = v a := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single a (fun c _ hca => by
      rw [spEmbedMat_apply_of_not_mem g (fun h => ha h.1), Matrix.one_apply_ne (Ne.symm hca),
        zero_mul])
    (fun h => absurd (Finset.mem_univ a) h),
    spEmbedMat_apply_of_not_mem g (fun h => ha h.1), Matrix.one_apply_eq, one_mul]

theorem spEmbedMat_isometry_iff (hσ : Function.Injective σ)
    (g : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) :
    (∀ v, StatedQuadPlus m F (spEmbedMat σ g *ᵥ v) = StatedQuadPlus m F v) ↔
      ∀ w, StatedQuadPlus k F (g *ᵥ w) = StatedQuadPlus k F w := by
  have hrest : ∀ v : Fin m ⊕ Fin m → F,
      ∑ i ∈ (Finset.univ.image σ)ᶜ, (spEmbedMat σ g *ᵥ v) (Sum.inl i) *
          (spEmbedMat σ g *ᵥ v) (Sum.inr i) =
        ∑ i ∈ (Finset.univ.image σ)ᶜ, v (Sum.inl i) * v (Sum.inr i) := by
    intro v
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ∉ Set.range σ := by
      rintro ⟨j, rfl⟩
      exact (Finset.mem_compl.1 hi) (Finset.mem_image_of_mem σ (Finset.mem_univ j))
    have hl : (Sum.inl i : Fin m ⊕ Fin m) ∉ Set.range (Sum.map σ σ) := by
      rintro ⟨y | y, hy⟩
      · exact hi' ⟨y, Sum.inl_injective hy⟩
      · exact Sum.inr_ne_inl hy
    have hr : (Sum.inr i : Fin m ⊕ Fin m) ∉ Set.range (Sum.map σ σ) := by
      rintro ⟨y | y, hy⟩
      · exact Sum.inl_ne_inr hy
      · exact hi' ⟨y, Sum.inr_injective hy⟩
    rw [spEmbedMat_mulVec_of_not_mem g v hl, spEmbedMat_mulVec_of_not_mem g v hr]
  constructor
  · intro h w
    set v : Fin m ⊕ Fin m → F := Function.extend (Sum.map σ σ) w 0 with hv
    have hinj : Function.Injective (Sum.map σ σ : Fin k ⊕ Fin k → Fin m ⊕ Fin m) :=
      Sum.map_injective.2 ⟨hσ, hσ⟩
    have hvw : v ∘ Sum.map σ σ = w := by
      funext y
      exact hinj.extend_apply w 0 y
    have h1 := h v
    rw [statedQuadPlus_split hσ, statedQuadPlus_split hσ v, spEmbedMat_mulVec_comp hσ, hvw,
      hrest] at h1
    exact add_right_cancel h1
  · intro h v
    rw [statedQuadPlus_split hσ, statedQuadPlus_split hσ v, spEmbedMat_mulVec_comp hσ, h, hrest]

end MulVec

section Embed

variable {σ : Fin k → Fin m}

theorem isometry_of_mem_isometryClosure {A : GL (Fin m ⊕ Fin m) F}
    (hA : A ∈ isometryClosure F m) (v : Fin m ⊕ Fin m → F) :
    StatedQuadPlus m F ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v) =
      StatedQuadPlus m F v := by
  induction hA using Subgroup.closure_induction generalizing v with
  | mem x hx => exact hx v
  | one => rw [Units.val_one, one_mulVec]
  | mul x y _ _ hx hy => rw [Units.val_mul, ← mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    calc StatedQuadPlus m F (((x⁻¹ : GL (Fin m ⊕ Fin m) F) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v) =
        StatedQuadPlus m F ((x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ
          (((x⁻¹ : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v)) :=
          (hx _).symm
      _ = StatedQuadPlus m F v := by
          rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem map_isometryClosure_le (hσ : Function.Injective σ) :
    (isometryClosure F k).map (spEmbedGL σ hσ) ≤ isometryClosure F m := by
  rw [isometryClosure, MonoidHom.map_closure]
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Subgroup.subset_closure ((spEmbedMat_isometry_iff hσ _).2 hg)

theorem map_statedOmega_le (hσ : Function.Injective σ) :
    (StatedOmega (StatedQuadPlus k F)).map (spEmbedGL σ hσ) ≤ StatedOmega (StatedQuadPlus m F) := by
  rw [statedOmega_eq_commutator_isometryClosure, statedOmega_eq_commutator_isometryClosure,
    Subgroup.map_commutator]
  exact Subgroup.commutator_mono (map_isometryClosure_le hσ) (map_isometryClosure_le hσ)

theorem spEmbedGL_mem_suppGL (hσ : Function.Injective σ) (g : GL (Fin k ⊕ Fin k) F) :
    spEmbedGL σ hσ g ∈ suppGL F (Set.range (Sum.map σ σ)) :=
  fun _ _ h => spEmbedMat_apply_of_not_mem _ h

theorem spEmbedGL_injective (hσ : Function.Injective σ) :
    Function.Injective (spEmbedGL (K := F) σ hσ) := fun _ _ hgh =>
  Units.ext (spEmbedMat_injective hσ (congrArg Units.val hgh))

theorem exists_spEmbedGL_eq_of_mem_suppGL (hσ : Function.Injective σ)
    {x : GL (Fin m ⊕ Fin m) F} (hx : x ∈ suppGL F (Set.range (Sum.map σ σ))) :
    ∃ y : GL (Fin k ⊕ Fin k) F, spEmbedGL σ hσ y = x := by
  set X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F := (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F)
  set X' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
    ((x⁻¹ : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F)
  have hX : IsSuppMat (Set.range (Sum.map σ σ)) X := hx
  have hX' : IsSuppMat (Set.range (Sum.map σ σ)) X' :=
    SymplecticPilot.IsSuppMat.of_mul_eq_one hX (by rw [← Units.val_mul, inv_mul_cancel,
      Units.val_one]) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hemb : ∀ M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F,
      IsSuppMat (Set.range (Sum.map σ σ)) M →
        spEmbedMat σ (M.submatrix (Sum.map σ σ) (Sum.map σ σ)) = M := by
    intro M hM
    ext a b
    by_cases h : a ∈ Set.range (Sum.map σ σ) ∧ b ∈ Set.range (Sum.map σ σ)
    · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
      rw [spEmbedMat_apply_image hσ, submatrix_apply]
    · rw [spEmbedMat_apply_of_not_mem _ h, hM a b h]
  set Y := X.submatrix (Sum.map σ σ) (Sum.map σ σ)
  set Y' := X'.submatrix (Sum.map σ σ) (Sum.map σ σ)
  have h1 : Y * Y' = 1 := spEmbedMat_injective hσ (by
    rw [spEmbedMat_mul hσ, hemb X hX, hemb X' hX', spEmbedMat_one, ← Units.val_mul,
      mul_inv_cancel, Units.val_one])
  have h2 : Y' * Y = 1 := spEmbedMat_injective hσ (by
    rw [spEmbedMat_mul hσ, hemb X hX, hemb X' hX', spEmbedMat_one, ← Units.val_mul,
      inv_mul_cancel, Units.val_one])
  refine ⟨⟨Y, Y', h1, h2⟩, Units.ext ?_⟩
  exact hemb X hX

theorem statedOmega_inf_suppGL_le_map_isometryClosure (hσ : Function.Injective σ) :
    StatedOmega (StatedQuadPlus m F) ⊓ suppGL F (Set.range (Sum.map σ σ)) ≤
      (isometryClosure F k).map (spEmbedGL σ hσ) := by
  intro x hx
  obtain ⟨hxO, hxS⟩ := mem_inf.1 hx
  obtain ⟨y, rfl⟩ := exists_spEmbedGL_eq_of_mem_suppGL hσ hxS
  have hiso := isometry_of_mem_isometryClosure
    ((Subgroup.commutator_le_self (isometryClosure F m)) hxO)
  exact ⟨y, Subgroup.subset_closure ((spEmbedMat_isometry_iff hσ _).1 hiso), rfl⟩

theorem map_statedOmega_le_inf_suppGL (hσ : Function.Injective σ) :
    (StatedOmega (StatedQuadPlus k F)).map (spEmbedGL σ hσ) ≤
      StatedOmega (StatedQuadPlus m F) ⊓ suppGL F (Set.range (Sum.map σ σ)) := by
  refine le_inf (map_statedOmega_le hσ) ?_
  rintro _ ⟨g, -, rfl⟩
  exact spEmbedGL_mem_suppGL hσ g

theorem perfectCore_statedOmega_inf_suppGL [Finite F] (hσ : Function.Injective σ)
    (hperf : ⁅StatedOmega (StatedQuadPlus k F), StatedOmega (StatedQuadPlus k F)⁆ =
      StatedOmega (StatedQuadPlus k F)) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓ suppGL F (Set.range (Sum.map σ σ))) =
      (StatedOmega (StatedQuadPlus k F)).map (spEmbedGL σ hσ) := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect (map_statedOmega_le_inf_suppGL hσ)
    (by rw [← Subgroup.map_commutator, hperf]))
  calc perfectCore (StatedOmega (StatedQuadPlus m F) ⊓ suppGL F (Set.range (Sum.map σ σ))) ≤
        perfectCore ((isometryClosure F k).map (spEmbedGL σ hσ)) :=
        perfectCore_mono (statedOmega_inf_suppGL_le_map_isometryClosure hσ)
    _ = (perfectCore (isometryClosure F k)).map (spEmbedGL σ hσ) :=
        (CFSG.Quasithin.map_perfectCore _ _).symm
    _ ≤ (StatedOmega (StatedQuadPlus k F)).map (spEmbedGL σ hσ) := by
        refine map_mono ?_
        rw [statedOmega_eq_commutator_isometryClosure]
        calc perfectCore (isometryClosure F k) =
              ⁅perfectCore (isometryClosure F k), perfectCore (isometryClosure F k)⁆ :=
              (perfectCore_perfect _).symm
          _ ≤ ⁅isometryClosure F k, isometryClosure F k⁆ :=
              Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)

end Embed

section Blocks

theorem perfectCore_omegaBlock [Finite F] {N : Finset (Fin m)} (hN : 3 ≤ N.card) :
    perfectCore (omegaBlock F N) =
      (StatedOmega (StatedQuadPlus N.card F)).map
        (spEmbedGL (planeEnum N) (planeEnum_injective N)) := by
  have h := perfectCore_statedOmega_inf_suppGL (F := F) (planeEnum_injective N)
    (Subgroup.isPerfect_iff.1
      (CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := F) hN))
  rwa [range_sumMap_eq_planeCoords (range_planeEnum N)] at h

end Blocks

end CFSG.SeitzReduction.OmegaPilot
